// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Test} from "forge-std/Test.sol";
import {FloorCreditIssuer, IERC20Like} from "../src/FloorCreditIssuer.sol";
import {MockReserve} from "./MockReserve.sol";

/// @notice Drives the issuer with bounded random operations by four accounts
///         and the governor. Reverts are allowed (guards), state checks are not.
contract Handler is Test {
    FloorCreditIssuer public m;
    MockReserve public reserve;
    address public gov;
    address[4] public actors;
    uint256 public floorHighWater;
    uint256 public liquidityRefusals; // a sale/borrow/close/skim that failed for lack of cash
    uint256 public calls;
    uint256 public unsolicited; // reserve sent directly to the contract
    // Ghost flags. A handler that reverted on a bad state would undo the bad state with it,
    // and with fail_on_revert = false the campaign would pass. The flags persist instead.
    bool public floorDecreased; // the floor price was seen below an earlier value
    bool public floorLoweredByReshape; // a reshape with a lower floor price succeeded

    constructor(FloorCreditIssuer m_, MockReserve reserve_, address gov_) {
        m = m_;
        reserve = reserve_;
        gov = gov_;
        actors = [address(0xA1), address(0xA2), address(0xA3), address(0xA4)];
        for (uint256 i = 0; i < 4; i++) {
            reserve.mint(actors[i], 1e30);
            vm.prank(actors[i]);
            reserve.approve(address(m), type(uint256).max);
        }
        reserve.mint(gov, 1e30);
        vm.prank(gov);
        reserve.approve(address(m), type(uint256).max);
        floorHighWater = m.floorPrice();
    }

    function _actor(uint256 seed) internal view returns (address) {
        return actors[seed % 4];
    }

    function _after() internal {
        calls++;
        uint256 f = m.floorPrice();
        if (f < floorHighWater) floorDecreased = true;
        else floorHighWater = f;
    }

    function buy(uint256 seed, uint256 x) external {
        uint256 room = m.capacity() - m.totalSupply();
        if (room == 0) return;
        x = bound(x, 1, room);
        vm.prank(_actor(seed));
        m.buy(x, type(uint256).max);
        _after();
    }

    function sell(uint256 seed, uint256 x) external {
        address a = _actor(seed);
        uint256 b = m.balanceOf(a);
        if (b == 0) return;
        x = bound(x, 1, b);
        vm.prank(a);
        try m.sell(x, 0) {} catch { liquidityRefusals++; }
        _after();
    }

    function borrow(uint256 seed, uint256 lockAdd, uint256 amount) external {
        address a = _actor(seed);
        (uint256 l, uint256 d) = m.loans(a);
        lockAdd = bound(lockAdd, 0, m.balanceOf(a));
        uint256 lim = m.gammaBps() * m.floorPrice() * (l + lockAdd) / (1e22);
        if (lim <= d) return;
        amount = bound(amount, 1, lim - d);
        vm.prank(a);
        try m.borrow(lockAdd, amount, 0) {} catch { liquidityRefusals++; }
        _after();
    }

    function repay(uint256 seed, uint256 amount, bool full) external {
        address a = _actor(seed);
        (, uint256 d) = m.loans(a);
        if (d == 0) return;
        amount = full ? d : bound(amount, 1, d);
        vm.prank(a);
        m.repay(amount);
        _after();
    }

    function close(uint256 seed) external {
        address a = _actor(seed);
        (, uint256 d) = m.loans(a);
        if (d == 0) return;
        vm.prank(a);
        try m.close(0) {} catch { liquidityRefusals++; } // must be covered: gammaCap + f_s < 1
        _after();
    }

    function raiseFloor(uint256 budget) external {
        uint256 s = m.surplus();
        if (s == 0 || m.totalSupply() == 0) return;
        budget = bound(budget, 1, s);
        try m.raiseFloor(budget) {} catch {}
        _after();
    }

    function inflow(uint256 amount) external {
        amount = bound(amount, 1, 1e6);
        vm.prank(gov);
        m.contribute(amount);
        _after();
    }

    function reshapeTail(uint256 bump) external {
        FloorCreditIssuer.Step[] memory s = m.steps();
        uint256 n = s.length;
        bump = bound(bump, 0, s[n - 1].price / 10);
        s[n - 1].price += bump; // reprice the last step upward; may hit (G2) or the lift cap
        vm.prank(gov);
        try m.reshape(s, 0) {} catch {}
        _after();
    }

    function lowerFloorAttempt(uint256 cut) external {
        FloorCreditIssuer.Step[] memory s = m.steps();
        cut = bound(cut, 1, s[0].price - 1);
        s[0].price -= cut;
        vm.prank(gov);
        try m.reshape(s, 0) { floorLoweredByReshape = true; } catch {}
        _after();
    }

    function skim(uint256 amount) external {
        uint256 s = m.surplus();
        if (s == 0) return;
        amount = bound(amount, 1, s);
        vm.prank(gov);
        try m.skim(amount) {} catch { liquidityRefusals++; }
        _after();
    }

    function setGamma(uint256 g) external {
        g = bound(g, 1, m.gammaCapBps());
        vm.prank(gov);
        m.setGamma(g);
        _after();
    }

    /// Free tokens can be transferred between accounts.
    function transferTokens(uint256 seedFrom, uint256 seedTo, uint256 x) external {
        address a = _actor(seedFrom);
        uint256 b = m.balanceOf(a);
        if (b == 0) return;
        vm.prank(a);
        m.transfer(_actor(seedTo), bound(x, 1, b));
        _after();
    }

    /// Anyone can send reserve tokens to the contract; they must not enter the accounting.
    function unsolicitedTransfer(uint256 amount) external {
        amount = bound(amount, 1, 1e6);
        vm.prank(gov);
        reserve.transfer(address(m), amount);
        unsolicited += amount;
        _after();
    }

    function warp(uint256 dt) external {
        vm.warp(block.timestamp + bound(dt, 1, 3 days));
    }
}

contract FloorCreditInvariantTest is Test {
    uint256 constant WAD = 1e18;
    uint256 constant BPS = 10_000;

    FloorCreditIssuer m;
    MockReserve reserve;
    Handler handler;
    address gov = address(0x60);

    function setUp() public {
        reserve = new MockReserve();
        FloorCreditIssuer.Step[] memory s = new FloorCreditIssuer.Step[](6);
        s[0] = FloorCreditIssuer.Step(WAD + 7, 4000);
        s[1] = FloorCreditIssuer.Step(WAD + WAD / 7, 1500);
        s[2] = FloorCreditIssuer.Step(WAD + WAD / 3, 1500);
        s[3] = FloorCreditIssuer.Step(2 * WAD + 1, 2500);
        s[4] = FloorCreditIssuer.Step(3 * WAD, 2500);
        s[5] = FloorCreditIssuer.Step(5 * WAD, 3000);
        m = new FloorCreditIssuer(
            IERC20Like(address(reserve)), gov, address(0x7EA), s, FloorCreditIssuer.Params(9000, 8500, 100, 300, 200, 1 hours)
        );
        handler = new Handler(m, reserve, gov);
        targetContract(address(handler));
    }

    function invariant_J1_custody() public view {
        uint256 free;
        for (uint256 i = 0; i < 4; i++) {
            free += m.balanceOf(handler.actors(i));
        }
        assertEq(free + m.totalLocked(), m.totalSupply());
    }

    function invariant_J2_loanCover() public view {
        uint256 locked;
        uint256 debt;
        for (uint256 i = 0; i < 4; i++) {
            (uint256 l, uint256 d) = m.loans(handler.actors(i));
            assertLe(d * BPS * WAD, m.gammaCapBps() * m.floorPrice() * l);
            locked += l;
            debt += d;
        }
        assertEq(locked, m.totalLocked());
        assertEq(debt, m.totalDebt());
    }

    function invariant_J3_reserveAdequacy() public view {
        assertGe((m.cash() + m.totalDebt()) * WAD, m.reserveNum(m.totalSupply()));
    }

    function invariant_coverageWithSlack() public view {
        assertGe(
            BPS * m.cash() * WAD + m.gammaCapBps() * m.reserveNum(m.totalLocked()),
            BPS * m.reserveNum(m.totalSupply())
        );
    }

    /// The token balance is the accounting plus what was sent to the contract unasked.
    function invariant_balanceCoversAccounting() public view {
        assertEq(reserve.balanceOf(address(m)), m.cash() + handler.unsolicited());
    }

    /// (G1): no operation lowers the floor, and no reshape with a lower floor is accepted.
    function invariant_floorNeverFalls() public view {
        assertFalse(handler.floorDecreased(), "floor decreased");
        assertFalse(handler.floorLoweredByReshape(), "a reshape lowered the floor");
        assertGe(m.floorPrice(), handler.floorHighWater());
    }

    function invariant_noLiquidityRefusal() public view {
        assertEq(handler.liquidityRefusals(), 0);
    }

    function invariant_scheduleIsValid() public view {
        FloorCreditIssuer.Step[] memory s = m.steps();
        uint256 cap;
        for (uint256 i = 0; i < s.length; i++) {
            assertGt(s[i].capacity, 0);
            if (i > 0) assertGe(s[i].price, s[i - 1].price);
            cap += s[i].capacity;
        }
        assertGe(cap, m.totalSupply());
        assertGe(m.floorPrice(), WAD + 7);
    }
}
