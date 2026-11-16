// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// @notice Minimal interface of the reserve token. The token must be a
///         standard ERC-20 without transfer fees and without rebasing (C8).
interface IERC20Like {
    function transfer(address to, uint256 amount) external returns (bool);
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
}

/// @title  FloorCreditIssuer
/// @notice Reference implementation of floor-anchored token credit on a stepped
///         mint-and-burn curve, as specified in "Lending the Redemption Reserve".
///
///         State (paper notation): steps = schedule p, totalSupply = S,
///         cash = A, totalLocked = L, totalDebt = D, gammaBps = policy LTV.
///
///         Invariant J, preserved by every function:
///           (J1) sum of free balances + totalLocked == totalSupply
///           (J2) loan.debt * BPS * WAD <= gammaCapBps * floorPrice * loan.locked
///           (J3) (cash + totalDebt) * WAD >= reserveNum(totalSupply)
///
///         Rounding (Proposition "Integer refinement"): purchase cost up, net
///         sale proceeds down once, borrowing guard exact, full repayment
///         releases the whole lock, partial release down, guards (G1), (G2) exact.
contract FloorCreditIssuer {
    uint256 internal constant WAD = 1e18;
    uint256 internal constant BPS = 10_000;
    uint256 public constant MAX_STEPS = 64;

    struct Step {
        uint256 price; // reserve units per token unit, WAD-scaled
        uint256 capacity; // token units
    }

    struct Loan {
        uint256 locked;
        uint256 debt;
    }

    IERC20Like public immutable reserve;
    address public immutable governor;
    address public immutable treasury;

    /// immutable caps and fee rates (basis points)
    uint256 public immutable gammaCapBps; // gamma-bar, <= 100%
    uint256 public immutable feeBuyBps; // f_b
    uint256 public immutable feeSellBps; // f_s, charged on every redemption
    uint256 public immutable feeOrigBps; // phi
    uint256 public immutable epochLength; // seconds; curve changes are budgeted per epoch (0: per call)

    uint256 public gammaBps; // current LTV policy, 0 < gammaBps <= gammaCapBps
    Step[] internal _steps; // _steps[0] is the floor step; all capacities positive

    uint256 public totalSupply; // S: free + locked
    uint256 public cash; // A: reserve attributable to the mechanism
    uint256 public totalLocked; // L
    uint256 public totalDebt; // D
    // Epoch budget for upward repricing (see _enterEpoch).
    uint256 public epochIndex; // current epoch number
    uint256 public epochFloor; // floor price when the first curve change of the epoch began
    bool public epochRaised; // a floor raise happened in this epoch
    bool public epochReshaped; // a governor reshape happened in this epoch
    uint256 public windowFloor; // floor at the start of the previous epoch if it had a curve change, else of this one
    bool public prevEpochChanged; // the epoch just before this one had a curve change

    mapping(address => uint256) public balanceOf; // free balances
    mapping(address => Loan) public loans;

    uint256 private _entered = 1;

    event Bought(address indexed account, uint256 tokens, uint256 paid);
    event Sold(address indexed account, uint256 tokens, uint256 received);
    event Borrowed(address indexed account, uint256 lockAdded, uint256 debtAdded, uint256 received);
    event Repaid(address indexed account, uint256 amount, uint256 released);
    event Closed(address indexed account, uint256 locked, uint256 debt, uint256 received);
    event Reshaped(uint256 oldFloor, uint256 newFloor, uint256 injected);
    event Skimmed(uint256 amount);
    event Contributed(address indexed from, uint256 amount);
    event GammaSet(uint256 gammaBps);
    event Transfer(address indexed from, address indexed to, uint256 amount);

    error BadConfig();
    error BadAmount();
    error Slippage();
    error LtvExceeded();
    error NoLoan();
    error NotGovernor();
    error BadSchedule();
    error FloorDecrease(); // (G1)
    error Underfunded(); // (G2)
    error LiftCap();
    error TooSoon();
    error CloseNotCovered();
    error Reentrancy();
    error TransferFailed();

    modifier nonReentrant() {
        if (_entered != 1) revert Reentrancy();
        _entered = 2;
        _;
        _entered = 1;
    }

    modifier onlyGovernor() {
        if (msg.sender != governor) revert NotGovernor();
        _;
    }

    /// @notice Deployment parameters (basis points; seconds for the interval).
    struct Params {
        uint256 gammaCapBps;
        uint256 gammaBps;
        uint256 feeBuyBps;
        uint256 feeSellBps;
        uint256 feeOrigBps;
        uint256 epochLength;
    }

    constructor(IERC20Like reserve_, address governor_, address treasury_, Step[] memory steps_, Params memory p) {
        // parameter rule gammaCap + f_s < 1 (C9); gammaCap < 1 gives a positive margin
        if (
            p.gammaBps == 0 || p.gammaBps > p.gammaCapBps || p.gammaCapBps + p.feeSellBps >= BPS
                || p.feeBuyBps > BPS || p.feeOrigBps >= BPS
        ) revert BadConfig();
        _validate(steps_);
        for (uint256 i = 0; i < steps_.length; i++) {
            _steps.push(steps_[i]);
        }
        reserve = reserve_;
        governor = governor_;
        treasury = treasury_;
        gammaCapBps = p.gammaCapBps;
        gammaBps = p.gammaBps;
        feeBuyBps = p.feeBuyBps;
        feeSellBps = p.feeSellBps;
        feeOrigBps = p.feeOrigBps;
        epochLength = p.epochLength;
    }

    // ------------------------------------------------------------------ views

    function floorPrice() public view returns (uint256) {
        return _steps[0].price;
    }

    function steps() external view returns (Step[] memory) {
        return _steps;
    }

    function capacity() public view returns (uint256 c) {
        for (uint256 i = 0; i < _steps.length; i++) {
            c += _steps[i].capacity;
        }
    }

    /// @notice WAD * R(x): exact numerator of the reserve function.
    function reserveNum(uint256 x) public view returns (uint256) {
        return _reserveNum(_steps, x);
    }

    /// @notice A + D - ceil(R(S)): reserve that backs no curve obligation.
    function surplus() public view returns (uint256) {
        return cash + totalDebt - _ceilDiv(reserveNum(totalSupply), WAD);
    }

    /// @notice floor(price * (1 + f_b) / (1 - f_s)): the largest price to which
    ///         a minted unit priced `price` may be lifted in one reshape.
    function kappaLimit(uint256 price) public view returns (uint256) {
        return (price * (BPS + feeBuyBps)) / (BPS - feeSellBps);
    }

    // ---------------------------------------------------------------- trading

    function buy(uint256 tokens, uint256 maxPay) external nonReentrant returns (uint256 pay) {
        if (tokens == 0 || totalSupply + tokens > capacity()) revert BadAmount();
        uint256 cost = _ceilDiv(reserveNum(totalSupply + tokens) - reserveNum(totalSupply), WAD);
        pay = cost + _ceilDiv(cost * feeBuyBps, BPS);
        if (pay > maxPay) revert Slippage();
        totalSupply += tokens;
        cash += pay; // the fee is retained
        balanceOf[msg.sender] += tokens;
        emit Bought(msg.sender, tokens, pay);
        _pull(msg.sender, pay);
    }

    function sell(uint256 tokens, uint256 minOut) external nonReentrant returns (uint256 out) {
        if (tokens == 0 || tokens > balanceOf[msg.sender]) revert BadAmount();
        out = _netProceeds(tokens);
        if (out < minOut) revert Slippage();
        balanceOf[msg.sender] -= tokens;
        totalSupply -= tokens;
        cash -= out; // cannot underflow: Theorem 1(b)
        _retireFloorCapacity();
        emit Sold(msg.sender, tokens, out);
        _push(msg.sender, out);
    }

    // ----------------------------------------------------------------- credit

    /// @notice Origination, top-up (lockAdd == 0), or added lock with new debt.
    function borrow(uint256 lockAdd, uint256 amount, uint256 minOut)
        external
        nonReentrant
        returns (uint256 out)
    {
        // No admissible debt exceeds price * capacity / WAD < 2^133; the bound keeps the products below in 256 bits.
        if (amount == 0 || amount > type(uint160).max || lockAdd > balanceOf[msg.sender]) revert BadAmount();
        Loan memory loan = loans[msg.sender];
        loan.locked += lockAdd;
        loan.debt += amount;
        // exact integer form of  d <= gamma * Pf * l   (r3)
        if (loan.debt * BPS * WAD > gammaBps * floorPrice() * loan.locked) revert LtvExceeded();
        out = amount - _ceilDiv(amount * feeOrigBps, BPS);
        if (out < minOut) revert Slippage();
        balanceOf[msg.sender] -= lockAdd;
        totalLocked += lockAdd;
        totalDebt += amount;
        loans[msg.sender] = loan;
        cash -= out; // cannot underflow: Theorem 1(c); the fee is retained
        emit Borrowed(msg.sender, lockAdd, amount, out);
        _push(msg.sender, out);
    }

    /// @notice Only the borrower can repay. A full repayment releases the whole lock.
    function repay(uint256 amount) external nonReentrant returns (uint256 released) {
        Loan memory loan = loans[msg.sender];
        if (loan.debt == 0) revert NoLoan();
        if (amount == 0 || amount > loan.debt) revert BadAmount();
        if (amount == loan.debt) {
            released = loan.locked;
            delete loans[msg.sender];
        } else {
            released = (loan.locked * amount) / loan.debt; // round down (r4)
            loans[msg.sender] = Loan(loan.locked - released, loan.debt - amount);
        }
        totalDebt -= amount;
        totalLocked -= released;
        balanceOf[msg.sender] += released;
        cash += amount;
        emit Repaid(msg.sender, amount, released);
        _pull(msg.sender, amount);
    }

    /// @notice Collateral-netted close: repay in full from the proceeds of
    ///         redeeming the lock. Always covered under gammaCap + f_s <= 1.
    function close(uint256 minOut) external nonReentrant returns (uint256 out) {
        Loan memory loan = loans[msg.sender];
        if (loan.debt == 0) revert NoLoan();
        uint256 proceeds = _netProceeds(loan.locked);
        if (proceeds < loan.debt) revert CloseNotCovered();
        out = proceeds - loan.debt;
        if (out < minOut) revert Slippage();
        delete loans[msg.sender];
        totalDebt -= loan.debt;
        totalLocked -= loan.locked;
        totalSupply -= loan.locked;
        cash -= out;
        _retireFloorCapacity();
        emit Closed(msg.sender, loan.locked, loan.debt, out);
        _push(msg.sender, out);
    }

    // ------------------------------------------------------- curve operations

    /// @notice Raise the floor by water-filling the minted range with `budget`
    ///         taken from the surplus. Anyone may call, any number of times.
    ///         The level is rounded down and capped at kappaLimit(windowFloor):
    ///         kappa times the floor at the start of the previous epoch (or of
    ///         this one, if the previous epoch had no curve change). Over any
    ///         window of one epoch length the raises together lift no minted unit by more than
    ///         kappa and a small raise cannot block a later one. Unminted
    ///         capacity priced at or below the new floor is retired.
    function raiseFloor(uint256 budget) external nonReentrant {
        uint256 supply = totalSupply;
        if (budget == 0 || budget > surplus() || supply == 0) revert BadAmount();
        _enterEpoch();
        if (epochReshaped) revert TooSoon(); // no raise after a reshape in the same epoch
        epochRaised = true;
        uint256 n = _steps.length;
        uint256 level = _steps[0].price;
        uint256 below = _min(_steps[0].capacity, supply);
        uint256 limit = kappaLimit(windowFloor);
        if (limit > type(uint96).max) limit = type(uint96).max; // largest representable price
        if (level >= limit) revert BadAmount(); // the budget of this window is used up
        // Numerator of the remaining budget. No raise can cost more than price * capacity < 2^192,
        // so a budget above the largest value that can be scaled is cut there without changing the result.
        uint256 num = (budget > type(uint256).max / WAD ? type(uint256).max / WAD : budget) * WAD;
        uint256 j = 1;
        while (true) {
            uint256 target = j < n ? _min(_steps[j].price, limit) : limit;
            if (num < (target - level) * below) {
                level += num / below; // final level, rounded down
                break;
            }
            num -= (target - level) * below; // exact cost of this lift
            level = target;
            if (j >= n || target < _steps[j].price) break; // stopped at the lift cap
            below = _min(below + _steps[j].capacity, supply); // absorb step j
            j++;
        }
        if (level == _steps[0].price) revert BadAmount(); // nothing to raise (budget too small or cap reached)
        Step[] memory next = new Step[](n - j + 1);
        next[0] = Step(level, below);
        for (uint256 k = j; k < n; k++) {
            next[k - j + 1] = _steps[k];
        }
        _install(next, 0);
    }

    /// @notice Replace the schedule. Guards: valid schedule, capacity >= supply,
    ///         (G1) floor does not fall, (G2) funded, lift cap. At most one
    ///         reshape per epoch, and only if no floor raise came before it in
    ///         that epoch, so that reshapes and raises cannot be chained.
    function reshape(Step[] calldata next, uint256 inject) external onlyGovernor nonReentrant {
        _enterEpoch();
        if (epochReshaped || epochRaised || prevEpochChanged) revert TooSoon();
        epochReshaped = true;
        Step[] memory copy = new Step[](next.length);
        for (uint256 i = 0; i < next.length; i++) {
            copy[i] = next[i];
        }
        _install(copy, inject);
        if (inject > 0) _pull(msg.sender, inject);
    }

    /// @notice Add reserve to the surplus. Anyone may call; the curve is unchanged.
    function contribute(uint256 amount) external nonReentrant {
        if (amount == 0) revert BadAmount();
        cash += amount;
        emit Contributed(msg.sender, amount);
        _pull(msg.sender, amount);
    }

    /// @notice Pay surplus to the treasury.
    function skim(uint256 amount) external onlyGovernor nonReentrant {
        if (amount == 0 || amount > surplus()) revert BadAmount();
        cash -= amount; // cannot underflow: Theorem 1(c)
        emit Skimmed(amount);
        _push(treasury, amount);
    }

    function setGamma(uint256 newGammaBps) external onlyGovernor {
        if (newGammaBps == 0 || newGammaBps > gammaCapBps) revert BadConfig();
        gammaBps = newGammaBps;
        emit GammaSet(newGammaBps);
    }

    /// @notice Transfer free tokens. Locked tokens are not in any balance.
    function transfer(address to, uint256 amount) external returns (bool) {
        if (amount > balanceOf[msg.sender]) revert BadAmount();
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        emit Transfer(msg.sender, to, amount);
        return true;
    }

    // --------------------------------------------------------------- internal

    function _netProceeds(uint256 tokens) internal view returns (uint256) {
        uint256 num = reserveNum(totalSupply) - reserveNum(totalSupply - tokens);
        return (num * (BPS - feeSellBps)) / (WAD * BPS); // one rounding, down
    }

    function _install(Step[] memory next, uint256 inject) internal {
        _validate(next);
        uint256 supply = totalSupply;
        uint256 cap;
        for (uint256 i = 0; i < next.length; i++) {
            cap += next[i].capacity;
        }
        if (cap < supply) revert BadSchedule();
        uint256 oldFloor = _steps[0].price;
        if (next[0].price < oldFloor) revert FloorDecrease(); // (G1)
        // (G2), in a form without a product of the reserve:  R'(S) > X * WAD  <=>  ceil(R'(S) / WAD) > X
        if (_ceilDiv(_reserveNum(next, supply), WAD) > cash + inject + totalDebt) revert Underfunded();
        _checkLiftCap(next, supply);
        cash += inject;
        delete _steps;
        for (uint256 i = 0; i < next.length; i++) {
            _steps.push(next[i]);
        }
        emit Reshaped(oldFloor, _steps[0].price, inject);
    }

    /// @dev Start a new epoch if the clock has moved into one. With epochLength == 0
    ///      every curve change is its own epoch.
    function _enterEpoch() internal {
        uint256 current = epochLength == 0 ? epochIndex + 1 : block.timestamp / epochLength + 1;
        if (current != epochIndex) {
            if (epochLength != 0 && epochIndex != 0 && current == epochIndex + 1) {
                // The previous epoch had a curve change: keep counting from its first floor,
                // so that changes on both sides of the boundary share one budget.
                windowFloor = epochFloor;
                prevEpochChanged = epochRaised || epochReshaped;
            } else {
                windowFloor = _steps[0].price;
                prevEpochChanged = false;
            }
            epochIndex = current;
            epochFloor = _steps[0].price;
            epochRaised = false;
            epochReshaped = false;
        }
    }

    /// @dev No minted unit may be repriced upward by more than kappa.
    function _checkLiftCap(Step[] memory next, uint256 supply) internal view {
        uint256 i; // index into the current schedule
        uint256 k; // index into the new schedule
        uint256 endOld = _steps[0].capacity;
        uint256 endNew = next[0].capacity;
        uint256 u; // position on the supply axis
        while (u < supply) {
            if (next[k].price > kappaLimit(_steps[i].price)) revert LiftCap();
            uint256 stop = _min(_min(endOld, endNew), supply);
            u = stop;
            if (u >= supply) break;
            if (u == endOld) {
                i++;
                endOld += _steps[i].capacity;
            }
            if (u == endNew) {
                k++;
                endNew += next[k].capacity;
            }
        }
    }

    /// @dev Retire redeemed floor capacity, but never the last step of the curve,
    ///      so that the capacity stays positive and floorPrice() == p(0).
    function _retireFloorCapacity() internal {
        uint256 n = _steps.length;
        if (n > 1 && totalSupply < _steps[0].capacity) {
            if (totalSupply == 0) {
                for (uint256 i = 0; i + 1 < n; i++) {
                    _steps[i] = _steps[i + 1];
                }
                _steps.pop();
                // No token is outstanding, so no minted unit can have been repriced:
                // the epoch budget restarts from the newly exposed floor.
                epochFloor = _steps[0].price;
                windowFloor = _steps[0].price;
            } else {
                _steps[0].capacity = totalSupply;
            }
        }
    }

    function _validate(Step[] memory s) internal pure {
        if (s.length == 0 || s.length > MAX_STEPS) revert BadSchedule();
        uint256 total;
        for (uint256 i = 0; i < s.length; i++) {
            if (s[i].price == 0 || s[i].capacity == 0) revert BadSchedule();
            if (s[i].price > type(uint96).max) revert BadSchedule();
            if (i > 0 && s[i].price < s[i - 1].price) revert BadSchedule();
            total += s[i].capacity;
            // The bound is on the total, so that a floor raise that merges steps stays valid.
            if (total > type(uint96).max) revert BadSchedule();
        }
    }

    function _reserveNum(Step[] memory s, uint256 x) internal pure returns (uint256 total) {
        uint256 rem = x;
        for (uint256 i = 0; i < s.length && rem > 0; i++) {
            uint256 take = _min(s[i].capacity, rem);
            total += take * s[i].price;
            rem -= take;
        }
        if (rem > 0) revert BadAmount();
    }

    function _pull(address from, uint256 amount) internal {
        if (!reserve.transferFrom(from, address(this), amount)) revert TransferFailed();
    }

    function _push(address to, uint256 amount) internal {
        if (amount == 0) return;
        if (!reserve.transfer(to, amount)) revert TransferFailed();
    }

    function _min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    function _ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
        return a == 0 ? 0 : (a - 1) / b + 1;
    }
}
