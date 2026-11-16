// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Test} from "forge-std/Test.sol";
import {FloorCreditIssuer, IERC20Like} from "../src/FloorCreditIssuer.sol";
import {MockReserve} from "./MockReserve.sol";

/// @notice Directed tests: each mirrors an example or a boundary case of the paper.
contract FloorCreditIssuerTest is Test {
    uint256 constant WAD = 1e18;
    uint256 constant BPS = 10_000;

    MockReserve reserve;
    address gov = address(0xA11CE);
    address treasury = address(0x7EA);
    address alice = address(0xA);
    address bob = address(0xB);

    function _deploy(
        FloorCreditIssuer.Step[] memory s,
        uint256 gammaCap,
        uint256 gamma,
        uint256 fb,
        uint256 fs,
        uint256 fo
    ) internal returns (FloorCreditIssuer m) {
        m = new FloorCreditIssuer(IERC20Like(address(reserve)), gov, treasury, s, FloorCreditIssuer.Params(gammaCap, gamma, fb, fs, fo, 0));
        address[4] memory who = [alice, bob, gov, address(this)];
        for (uint256 i = 0; i < who.length; i++) {
            reserve.mint(who[i], 1e30);
            vm.prank(who[i]);
            reserve.approve(address(m), type(uint256).max);
        }
    }

    function _steps2(uint256 p0, uint256 c0, uint256 p1, uint256 c1)
        internal
        pure
        returns (FloorCreditIssuer.Step[] memory s)
    {
        s = new FloorCreditIssuer.Step[](2);
        s[0] = FloorCreditIssuer.Step(p0, c0);
        s[1] = FloorCreditIssuer.Step(p1, c1);
    }

    function setUp() public {
        reserve = new MockReserve();
    }

    function _assertJ(FloorCreditIssuer m, address[] memory accts) internal view {
        uint256 free;
        for (uint256 i = 0; i < accts.length; i++) {
            free += m.balanceOf(accts[i]);
            (uint256 l, uint256 d) = m.loans(accts[i]);
            assertLe(d * BPS * WAD, m.gammaCapBps() * m.floorPrice() * l, "J2");
        }
        assertEq(free + m.totalLocked(), m.totalSupply(), "J1");
        assertGe((m.cash() + m.totalDebt()) * WAD, m.reserveNum(m.totalSupply()), "J3");
        // coverage with slack: BPS*A*WAD >= BPS*R(S) - gammaCap*R(L)
        assertGe(
            BPS * m.cash() * WAD + m.gammaCapBps() * m.reserveNum(m.totalLocked()),
            BPS * m.reserveNum(m.totalSupply()),
            "coverage"
        );
        assertEq(reserve.balanceOf(address(m)), m.cash(), "balance equals accounting");
    }

    function _two() internal view returns (address[] memory a) {
        a = new address[](2);
        a[0] = alice;
        a[1] = bob;
    }

    // --- rounding of the borrowing guard (paper, Section 3.8; script block N07)

    function test_BorrowGuardIsExact() public {
        FloorCreditIssuer m = _deploy(_steps2(2 * WAD, 100, 3 * WAD, 100), 9000, 9000, 0, 0, 0);
        vm.startPrank(alice);
        m.buy(10, type(uint256).max);
        // debt 3 against 1 token of floor value 2: the rounded-down lock; must be refused
        vm.expectRevert(FloorCreditIssuer.LtvExceeded.selector);
        m.borrow(1, 3, 0);
        // the rounded-up lock is 2 tokens: 3 <= 0.9 * 2 * 2 = 3.6
        m.borrow(2, 3, 0);
        vm.stopPrank();
        _assertJ(m, _two());
    }

    function test_ZeroLockLoanIsRefused() public {
        FloorCreditIssuer m = _deploy(_steps2(100 * WAD, 100, 200 * WAD, 100), 9000, 9000, 0, 0, 0);
        vm.startPrank(alice);
        m.buy(5, type(uint256).max);
        vm.expectRevert(FloorCreditIssuer.LtvExceeded.selector);
        m.borrow(0, 1, 0);
        vm.stopPrank();
    }

    // --- repayment semantics

    function test_FullRepaymentReleasesWholeLock() public {
        FloorCreditIssuer m = _deploy(_steps2(WAD, 1000, 2 * WAD, 1000), 9000, 9000, 100, 100, 200);
        vm.startPrank(alice);
        m.buy(500, type(uint256).max);
        m.borrow(500, 450, 0);
        assertEq(m.balanceOf(alice), 0);
        uint256 released = m.repay(200); // partial: floor(500 * 200 / 450) = 222
        assertEq(released, 222);
        (uint256 l, uint256 d) = m.loans(alice);
        assertEq(l, 278);
        assertEq(d, 250);
        released = m.repay(250);
        assertEq(released, 278);
        (l, d) = m.loans(alice);
        assertEq(l + d, 0);
        assertEq(m.balanceOf(alice), 500);
        vm.stopPrank();
        _assertJ(m, _two());
    }

    function test_OnlyBorrowerCanRepay() public {
        FloorCreditIssuer m = _deploy(_steps2(WAD, 1000, 2 * WAD, 1000), 9000, 9000, 0, 0, 0);
        vm.startPrank(alice);
        m.buy(100, type(uint256).max);
        m.borrow(100, 90, 0);
        vm.stopPrank();
        vm.prank(bob);
        vm.expectRevert(FloorCreditIssuer.NoLoan.selector);
        m.repay(90);
    }

    // --- collateral-netted close (Proposition "Collateral-netted close")

    function test_CloseIsCoveredUnderTheParameterRule() public {
        // Pf = 1.5, gamma = 90%, f_s = 3%: integer net proceeds floor(0.97 * 1.5) = 1 = debt
        FloorCreditIssuer.Step[] memory s = new FloorCreditIssuer.Step[](1);
        s[0] = FloorCreditIssuer.Step(3 * WAD / 2, 10);
        FloorCreditIssuer m = _deploy(s, 9000, 9000, 0, 300, 0);
        vm.startPrank(alice);
        m.buy(1, type(uint256).max);
        m.borrow(1, 1, 0);
        uint256 out = m.close(0);
        assertEq(out, 0);
        vm.stopPrank();
        _assertJ(m, _two());
    }

    // --- the floor guard (Example "A reshape without the floor guard"; script block N06)

    function test_ReshapeCannotLowerTheFloor() public {
        FloorCreditIssuer m = _deploy(_steps2(10 * WAD, 1, 30 * WAD, 1), 9000, 9000, 0, 0, 0);
        vm.prank(alice);
        m.buy(1, type(uint256).max);
        vm.prank(bob);
        m.buy(1, type(uint256).max);
        vm.prank(alice);
        m.borrow(1, 9, 0);
        assertEq(m.cash(), 31);
        vm.prank(gov);
        vm.expectRevert(FloorCreditIssuer.FloorDecrease.selector);
        m.reshape(_steps2(8 * WAD, 1, 32 * WAD, 1), 0);
        // the free holder can still redeem at the curve return 30
        vm.prank(bob);
        assertEq(m.sell(1, 0), 30);
        _assertJ(m, _two());
    }

    function test_ReshapeMustBeFunded() public {
        FloorCreditIssuer m = _deploy(_steps2(10 * WAD, 1, 30 * WAD, 1), 9000, 9000, 0, 0, 0);
        vm.prank(alice);
        m.buy(2, type(uint256).max);
        vm.startPrank(gov);
        vm.expectRevert(FloorCreditIssuer.Underfunded.selector);
        m.reshape(_steps2(10 * WAD, 1, 31 * WAD, 1), 0);
        vm.stopPrank();
    }

    // --- floor raise by water-filling (Figure "A floor raise"; script block N10)

    function test_RaiseFloorIsWaterFilling() public {
        FloorCreditIssuer.Step[] memory s = new FloorCreditIssuer.Step[](9);
        s[0] = FloorCreditIssuer.Step(WAD, 4000);
        for (uint256 i = 1; i < 9; i++) {
            s[i] = FloorCreditIssuer.Step(WAD + i * WAD / 5, 1000);
        }
        // fees chosen so that kappa = 1.3 / 0.91 = 1.428 > 1.34 and the cap does not bind
        FloorCreditIssuer m = _deploy(s, 9000, 9000, 3000, 900, 0);
        vm.prank(alice);
        m.buy(7500, type(uint256).max);
        uint256 sur = m.surplus();
        assertGe(sur, 1500);
        m.raiseFloor(1500);
        assertEq(m.floorPrice(), 134 * WAD / 100);
        assertEq(m.surplus(), sur - 1500);
        FloorCreditIssuer.Step[] memory t = m.steps();
        assertEq(t[0].capacity, 5000);
        assertEq(t[1].price, 14 * WAD / 10);
        _assertJ(m, _two());
    }

    // --- minting just before a raise (Proposition "Mint, reshape, redeem"; script block N05)

    function test_LiftCapMakesMintRaiseRedeemUnprofitable() public {
        FloorCreditIssuer.Step[] memory s = new FloorCreditIssuer.Step[](11);
        s[0] = FloorCreditIssuer.Step(WAD, 1000);
        for (uint256 i = 1; i < 11; i++) {
            s[i] = FloorCreditIssuer.Step(WAD + i * WAD / 10, 100);
        }
        FloorCreditIssuer m = _deploy(s, 9000, 9000, 300, 300, 0);
        vm.prank(alice);
        m.buy(1000, type(uint256).max);
        // accumulate a budget of 300 by an inflow of reserve
        vm.prank(gov);
        m.contribute(300);
        vm.startPrank(bob);
        uint256 paid = m.buy(100, type(uint256).max);
        m.raiseFloor(300);
        uint256 got = m.sell(100, 0);
        vm.stopPrank();
        assertLe(got, paid, "the attacker must not profit");
        assertLe(m.floorPrice(), m.kappaLimit(WAD));
        _assertJ(m, _two());
    }

    function test_ReshapeRespectsLiftCap() public {
        FloorCreditIssuer.Step[] memory s = new FloorCreditIssuer.Step[](1);
        s[0] = FloorCreditIssuer.Step(100 * WAD, 10);
        FloorCreditIssuer m = _deploy(s, 9000, 9000, 100, 100, 0);
        vm.prank(alice);
        m.buy(1, type(uint256).max);
        FloorCreditIssuer.Step[] memory t = new FloorCreditIssuer.Step[](1);
        t[0] = FloorCreditIssuer.Step(200 * WAD, 10);
        vm.startPrank(gov);
        vm.expectRevert(FloorCreditIssuer.LiftCap.selector);
        m.reshape(t, 1000);
        vm.stopPrank();
    }

    // --- surplus and skim

    function test_SkimIsLimitedToSurplus() public {
        FloorCreditIssuer m = _deploy(_steps2(WAD, 1000, 2 * WAD, 1000), 9000, 9000, 100, 100, 200);
        vm.startPrank(alice);
        m.buy(1500, type(uint256).max);
        m.borrow(1500, 1000, 0);
        vm.stopPrank();
        uint256 sur = m.surplus();
        assertGt(sur, 0);
        vm.startPrank(gov);
        vm.expectRevert(FloorCreditIssuer.BadAmount.selector);
        m.skim(sur + 1);
        m.skim(sur);
        vm.stopPrank();
        assertEq(m.surplus(), 0);
        assertEq(reserve.balanceOf(treasury), sur);
        _assertJ(m, _two());
    }

    // --- the floor step when supply returns to it

    function test_LastStepIsNeverRetired() public {
        FloorCreditIssuer.Step[] memory s = new FloorCreditIssuer.Step[](1);
        s[0] = FloorCreditIssuer.Step(WAD, 10);
        FloorCreditIssuer m = _deploy(s, 9000, 9000, 0, 0, 0);
        vm.startPrank(alice);
        m.buy(1, type(uint256).max);
        m.sell(1, 0);
        vm.stopPrank();
        assertEq(m.capacity(), 10);
        _assertJ(m, _two());
    }

    function test_FullRedemptionExposesNextStepAsFloor() public {
        FloorCreditIssuer m = _deploy(_steps2(WAD, 10, 2 * WAD, 10), 9000, 9000, 0, 0, 0);
        vm.startPrank(alice);
        m.buy(15, type(uint256).max);
        m.sell(15, 0);
        vm.stopPrank();
        assertEq(m.floorPrice(), 2 * WAD);
        assertEq(m.capacity(), 10);
        _assertJ(m, _two());
    }

    function test_ReshapeAtZeroSupplyKeepsTheFloorStep() public {
        FloorCreditIssuer m = _deploy(_steps2(WAD, 10, 2 * WAD, 10), 9000, 9000, 0, 0, 0);
        FloorCreditIssuer.Step[] memory same = m.steps();
        vm.prank(gov);
        m.reshape(same, 5);
        assertEq(m.floorPrice(), WAD);
        assertEq(m.capacity(), 20);
        assertEq(m.cash(), 5);
    }

    function test_UnsolicitedTransferDoesNotEnterAccounting() public {
        FloorCreditIssuer m = _deploy(_steps2(WAD, 1000, 2 * WAD, 1000), 9000, 9000, 100, 100, 0);
        vm.prank(alice);
        m.buy(100, type(uint256).max);
        uint256 cashBefore = m.cash();
        uint256 surplusBefore = m.surplus();
        vm.prank(bob);
        reserve.transfer(address(m), 12345);
        assertEq(m.cash(), cashBefore);
        assertEq(m.surplus(), surplusBefore);
        assertEq(reserve.balanceOf(address(m)), cashBefore + 12345);
    }

    function test_IneffectiveRaiseIsRefused() public {
        // budget 1 over 2e18 tokens cannot move the level by one unit of the price scale
        FloorCreditIssuer.Step[] memory s = _steps2(WAD, 3e18, 2 * WAD, 10);
        FloorCreditIssuer m = _deploy(s, 9000, 9000, 100, 100, 0);
        vm.prank(alice);
        m.buy(2e18, type(uint256).max);
        FloorCreditIssuer.Step[] memory before = m.steps();
        assertGe(m.surplus(), 1);
        vm.expectRevert(FloorCreditIssuer.BadAmount.selector);
        m.raiseFloor(1);
        FloorCreditIssuer.Step[] memory afterSteps = m.steps();
        assertEq(afterSteps.length, before.length);
        assertEq(afterSteps[0].capacity, before[0].capacity);
    }

    function _deployEpoch(FloorCreditIssuer.Step[] memory s, uint256 epoch) internal returns (FloorCreditIssuer m) {
        m = new FloorCreditIssuer(
            IERC20Like(address(reserve)), gov, treasury, s, FloorCreditIssuer.Params(9000, 9000, 100, 100, 0, epoch)
        );
        address[3] memory who = [alice, bob, gov];
        for (uint256 i = 0; i < who.length; i++) {
            reserve.mint(who[i], 1e30);
            vm.prank(who[i]);
            reserve.approve(address(m), type(uint256).max);
        }
    }

    function test_OneReshapePerEpoch() public {
        FloorCreditIssuer.Step[] memory s = _steps2(WAD, 1000, 2 * WAD, 1000);
        FloorCreditIssuer m = _deployEpoch(s, 1 hours);
        vm.startPrank(gov);
        vm.warp(10 hours);
        m.reshape(s, 5);
        vm.warp(11 hours - 1);
        vm.expectRevert(FloorCreditIssuer.TooSoon.selector);
        m.reshape(s, 5);
        vm.warp(11 hours);
        vm.expectRevert(FloorCreditIssuer.TooSoon.selector);
        m.reshape(s, 5); // the epoch after a curve change is closed to reshapes as well
        vm.warp(12 hours);
        m.reshape(s, 5);
        vm.stopPrank();
        assertEq(m.cash(), 10);
    }

    /// A small raise must not block a later raise in the same epoch (scheduling grief).
    function test_SmallRaiseDoesNotBlockLaterRaise() public {
        FloorCreditIssuer m = _deployEpoch(_steps2(WAD, 1000, 2 * WAD, 1000), 1 hours);
        vm.warp(10 hours);
        vm.prank(alice);
        m.buy(1000, type(uint256).max); // pays 1000 + 10 fee: surplus 10
        assertEq(m.surplus(), 10);
        vm.prank(bob);
        m.raiseFloor(1);
        assertEq(m.floorPrice(), WAD + WAD / 1000);
        vm.prank(alice);
        m.raiseFloor(5); // same epoch: still allowed
        assertEq(m.floorPrice(), WAD + 6 * WAD / 1000);
        assertEq(m.surplus(), 4);
    }

    /// The raises of one epoch together cannot lift the floor above kappa times the epoch's first floor.
    function test_RaisesInOneEpochShareTheCap() public {
        FloorCreditIssuer m = _deployEpoch(_steps2(WAD, 1000, 2 * WAD, 1000), 1 hours);
        vm.warp(10 hours);
        vm.prank(alice);
        m.buy(1000, type(uint256).max);
        vm.prank(gov);
        m.contribute(500);
        uint256 cap = m.kappaLimit(WAD); // 1.0202...
        m.raiseFloor(10);
        m.raiseFloor(400); // more than enough to pass the cap
        assertEq(m.floorPrice(), cap);
        vm.expectRevert(FloorCreditIssuer.BadAmount.selector);
        m.raiseFloor(50); // nothing left to raise in this epoch
        vm.warp(11 hours);
        vm.expectRevert(FloorCreditIssuer.BadAmount.selector);
        m.raiseFloor(50); // the next epoch still counts from the floor at the start of this one
        vm.warp(12 hours);
        m.raiseFloor(50); // one full epoch later: a new budget, from the new floor
        assertGt(m.floorPrice(), cap);
        assertLe(m.floorPrice(), m.kappaLimit(cap));
    }

    /// The schedules the contract accepts are closed under floor raises (found in review):
    /// a raise that merges steps must not produce a capacity the validator rejects.
    function test_TotalCapacityIsBoundedSoMergedStepsAreRepresentable() public {
        uint256 M = type(uint96).max;
        FloorCreditIssuer.Step[] memory s = _steps2(WAD, M, WAD, M);
        vm.expectRevert(FloorCreditIssuer.BadSchedule.selector);
        new FloorCreditIssuer(
            IERC20Like(address(reserve)), gov, treasury, s, FloorCreditIssuer.Params(9000, 9000, 100, 100, 0, 1 hours)
        );
    }

    /// No amount of reserve paid in may make later arithmetic overflow and block the curve
    /// changes, and no bound on cash may refuse a funded raise (both found in review).
    function test_LargeReserveKeepsCurveChangesLive() public {
        FloorCreditIssuer m = _deployEpoch(_steps2(WAD, 1000, 2 * WAD, 1000), 1 hours);
        vm.warp(10 hours);
        vm.prank(alice);
        m.buy(500, type(uint256).max);
        uint256 big = type(uint256).max / WAD + 1; // big * WAD does not fit in 256 bits
        reserve.mint(bob, big);
        vm.prank(bob);
        m.contribute(big);
        vm.prank(alice);
        m.buy(100, type(uint256).max); // inflows after a large contribution
        vm.prank(alice);
        m.borrow(100, 50, 0);
        m.raiseFloor(1); // a small funded raise is accepted
        assertGt(m.floorPrice(), WAD);
        uint256 s0 = m.surplus();
        m.raiseFloor(s0); // the whole surplus as budget: stops at the lift cap, no panic
        assertEq(m.floorPrice(), m.kappaLimit(WAD));
        vm.prank(alice);
        m.repay(50);
        FloorCreditIssuer.Step[] memory t = m.steps();
        vm.warp(12 hours);
        vm.prank(gov);
        m.reshape(t, 7); // the funding guard works with a large reserve
        vm.prank(alice);
        m.sell(600, 0);
    }

    /// A borrow request of absurd size is refused by a guard, not by an arithmetic panic.
    function test_AbsurdBorrowAmountIsRefusedCleanly() public {
        FloorCreditIssuer m = _deployEpoch(_steps2(WAD, 1000, 2 * WAD, 1000), 1 hours);
        vm.startPrank(alice);
        m.buy(100, type(uint256).max);
        vm.expectRevert(FloorCreditIssuer.BadAmount.selector);
        m.borrow(100, type(uint256).max / (10_000 * WAD) + 1, 0);
        vm.stopPrank();
    }

    /// A raise near the largest representable price stops at that price instead of reverting.
    function test_RaiseStopsAtTheLargestRepresentablePrice() public {
        uint256 M = type(uint96).max;
        FloorCreditIssuer m = _deployEpoch(_steps2(M - 1000, 1000, M - 500, 1000), 1 hours);
        vm.warp(10 hours);
        vm.prank(alice);
        m.buy(1000, type(uint256).max);
        assertGt(m.kappaLimit(M - 1000), M); // the lift cap alone would allow an unrepresentable price
        m.raiseFloor(1);
        assertEq(m.floorPrice(), M);
    }

    /// A replacement just before a boundary and a raise just after it share one cap.
    function test_ReshapeThenRaiseAcrossABoundaryShareTheCap() public {
        FloorCreditIssuer m = _deployEpoch(_steps2(WAD, 1000, 3 * WAD, 1000), 1 hours);
        vm.prank(alice);
        m.buy(1000, type(uint256).max);
        vm.prank(gov);
        m.contribute(500);
        uint256 cap = m.kappaLimit(WAD);
        vm.warp(11 hours - 12);
        FloorCreditIssuer.Step[] memory t = _steps2(WAD + WAD / 100, 1000, 3 * WAD, 1000);
        vm.prank(gov);
        m.reshape(t, 0); // the floor rises by 1%, funded from the surplus
        assertEq(m.floorPrice(), WAD + WAD / 100);
        vm.warp(11 hours);
        m.raiseFloor(400);
        assertEq(m.floorPrice(), cap); // kappa times the floor before the replacement, not after it
        assertLt(m.floorPrice(), m.kappaLimit(WAD + WAD / 100));
    }

    /// The very first curve change may fall into the first epoch of the clock (found in review).
    function test_FirstRaiseInTheFirstEpoch() public {
        FloorCreditIssuer m = _deployEpoch(_steps2(WAD, 1000, 2 * WAD, 1000), 1 hours);
        vm.warp(1);
        vm.prank(alice);
        m.buy(1000, type(uint256).max);
        m.raiseFloor(5);
        assertEq(m.floorPrice(), WAD + 5 * WAD / 1000);
    }

    /// Raising at the end of one epoch and at the start of the next must not give kappa squared
    /// within a few blocks (found in review). Over any window of one epoch length the floor
    /// rises by at most the factor kappa.
    function test_RaisesAcrossAnEpochBoundaryShareTheWindow() public {
        FloorCreditIssuer m = _deployEpoch(_steps2(WAD, 1000, 3 * WAD, 1000), 1 hours);
        vm.prank(alice);
        m.buy(1000, type(uint256).max);
        vm.prank(gov);
        m.contribute(500);
        uint256 cap = m.kappaLimit(WAD);
        vm.warp(11 hours - 12); // one block before the boundary
        m.raiseFloor(400);
        assertEq(m.floorPrice(), cap);
        vm.warp(11 hours); // first block of the next epoch
        vm.expectRevert(FloorCreditIssuer.BadAmount.selector);
        m.raiseFloor(50);
        assertEq(m.floorPrice(), cap);
        vm.warp(12 hours - 13); // still less than one epoch after the first raise
        vm.expectRevert(FloorCreditIssuer.BadAmount.selector);
        m.raiseFloor(50);
        vm.warp(12 hours); // more than one epoch after it
        m.raiseFloor(50);
        assertLe(m.floorPrice(), m.kappaLimit(cap));
    }

    /// A full redemption exposes the next step as the floor. The epoch budget must restart from it,
    /// or every later raise of the epoch would fail (found in review).
    function test_RaiseAfterFullRedemptionInSameEpoch() public {
        FloorCreditIssuer m = _deployEpoch(_steps2(WAD, 1000, 2 * WAD, 1000), 1 hours);
        vm.warp(10 hours);
        vm.startPrank(alice);
        m.buy(1000, type(uint256).max);
        m.raiseFloor(1);
        assertEq(m.floorPrice(), WAD + WAD / 1000);
        m.sell(1000, 0);
        assertEq(m.floorPrice(), 2 * WAD); // the first step is retired
        m.buy(1000, type(uint256).max);
        uint256 w = m.surplus();
        assertGt(w, 0);
        m.raiseFloor(1); // same epoch
        assertEq(m.floorPrice(), 2 * WAD + WAD / 1000);
        m.raiseFloor(w - 1); // the rest of the surplus (40 in all), below the cap of the exposed floor
        assertEq(m.floorPrice(), 2 * WAD + 40 * WAD / 1000);
        assertLe(m.floorPrice(), m.kappaLimit(2 * WAD));
        vm.stopPrank();
    }

    function test_NoReshapeAfterRaiseInSameEpoch() public {
        FloorCreditIssuer.Step[] memory s = _steps2(WAD, 1000, 2 * WAD, 1000);
        FloorCreditIssuer m = _deployEpoch(s, 1 hours);
        vm.warp(10 hours);
        vm.prank(alice);
        m.buy(1000, type(uint256).max);
        m.raiseFloor(5);
        FloorCreditIssuer.Step[] memory t = m.steps();
        vm.startPrank(gov);
        vm.expectRevert(FloorCreditIssuer.TooSoon.selector);
        m.reshape(t, 1);
        vm.warp(11 hours);
        vm.expectRevert(FloorCreditIssuer.TooSoon.selector);
        m.reshape(t, 1); // nor in the epoch after the raise
        vm.warp(12 hours);
        m.reshape(t, 1);
        vm.expectRevert(FloorCreditIssuer.TooSoon.selector);
        m.raiseFloor(1); // and no raise after a reshape in the same epoch
        vm.stopPrank();
    }

    function test_LiftCapIsCheckedAtEveryBreakpoint() public {
        // three minted steps; the new schedule moves the breakpoints and lifts only the middle stretch too far
        FloorCreditIssuer.Step[] memory s = new FloorCreditIssuer.Step[](3);
        s[0] = FloorCreditIssuer.Step(100 * WAD, 10);
        s[1] = FloorCreditIssuer.Step(110 * WAD, 10);
        s[2] = FloorCreditIssuer.Step(200 * WAD, 10);
        FloorCreditIssuer m = _deploy(s, 9000, 9000, 100, 100, 0); // kappa = 1.01 / 0.99 = 1.0202
        vm.prank(alice);
        m.buy(30, type(uint256).max);
        FloorCreditIssuer.Step[] memory t = new FloorCreditIssuer.Step[](3);
        t[0] = FloorCreditIssuer.Step(100 * WAD, 5);
        t[1] = FloorCreditIssuer.Step(112 * WAD, 15); // positions 5..9 were priced 100: 112 > 1.0202 * 100
        t[2] = FloorCreditIssuer.Step(200 * WAD, 10);
        vm.startPrank(gov);
        vm.expectRevert(FloorCreditIssuer.LiftCap.selector);
        m.reshape(t, 10_000);
        t[1] = FloorCreditIssuer.Step(102 * WAD, 15); // 102 <= 102.02 on 5..9 and 102 <= 110 on 10..19
        m.reshape(t, 10_000);
        vm.stopPrank();
        assertEq(m.floorPrice(), 100 * WAD);
    }

    // --- deployment enforces the parameter rule

    function test_ConstructorEnforcesParameterRule() public {
        FloorCreditIssuer.Step[] memory s = _steps2(WAD, 10, 2 * WAD, 10);
        vm.expectRevert(FloorCreditIssuer.BadConfig.selector);
        new FloorCreditIssuer(IERC20Like(address(reserve)), gov, treasury, s, FloorCreditIssuer.Params(9000, 9000, 0, 1000, 0, 0));
        vm.expectRevert(FloorCreditIssuer.BadConfig.selector);
        new FloorCreditIssuer(IERC20Like(address(reserve)), gov, treasury, s, FloorCreditIssuer.Params(9000, 9500, 0, 100, 0, 0));
    }

    // --- fuzz: a buy followed by a sale of the same tokens never pays more than it cost

    function testFuzz_RoundTripNeverProfits(uint256 seedBuy, uint256 x, uint16 fb, uint16 fs) public {
        fb = uint16(bound(fb, 0, 500));
        fs = uint16(bound(fs, 0, 900));
        FloorCreditIssuer.Step[] memory s = new FloorCreditIssuer.Step[](4);
        s[0] = FloorCreditIssuer.Step(WAD + 7, 1000);
        s[1] = FloorCreditIssuer.Step(WAD + WAD / 3, 500);
        s[2] = FloorCreditIssuer.Step(2 * WAD + 1, 700);
        s[3] = FloorCreditIssuer.Step(5 * WAD, 900);
        FloorCreditIssuer m = _deploy(s, 9000, 9000, fb, fs, 0);
        seedBuy = bound(seedBuy, 0, 3000);
        if (seedBuy > 0) {
            vm.prank(bob);
            m.buy(seedBuy, type(uint256).max);
        }
        x = bound(x, 1, 3100 - seedBuy);
        vm.startPrank(alice);
        uint256 paid = m.buy(x, type(uint256).max);
        uint256 got = m.sell(x, 0);
        vm.stopPrank();
        assertLe(got, paid);
        _assertJ(m, _two());
    }
}
