# Fee allocation and reward-claim ledger

Run from the paper directory:

```bash
python3 -I empirics/rewards.py
```

The script requires only the Python standard library and makes no network calls.
It reads the supplied raw logs, metadata, pool supplies and terminal reserve
identifiers. It prints the report saved in `outputs/rewards_run.txt` and generates
`sections/rewardnums.tex`. The manuscript loads that macro file in `main.tex`.
The existing credit analysis and its generated numbers are unchanged.

## Definitions and checks

`Distributed.totalAmount` is a recorded allocation, with destinations
`protocolFee`, `creatorFee` and `stakingFee`. The script decodes field names,
types and tuple structure from the three supplied ABI JSON files. Topic hashes
come from the accompanying event-topic manifest; their written signatures must
agree with the JSON definitions. Selected payload lengths, indexed-field counts
and integer widths must agree with the ABI.

The pinned sample contains 2,233 distributions and 173 `Claim` events. Every
distribution must satisfy the exact integer identity

```text
totalAmount = protocolFee + creatorFee + stakingFee
```

All reserve identifiers must agree with the terminal pool snapshots. Raw logs
must be unique, ordered, within the pinned block interval, and emitted by the
specified singleton. Pool sums and source sums must each reconcile with the
aggregate totals. No amounts are converted to floating point; display uses
decimal arithmetic and 18 reserve decimals.

## Conservative source matching

For each distribution, inspect the next `Borrow`, `Leverage` or `Swap` event
for the same pool in the same transaction. Match only if its amount is exactly:

| Event | Matching amount |
|---|---|
| Borrow | `fee` |
| Leverage | `debtAdded - reservesIn` |
| Swap | `totalFee - liquidityFee` |

A source can be used only once. If several distributions propose the same
source, none receives that assignment. An event without a unique exact match
remains **Unassigned**; its measured allocation still enters the pool and total
sums. The current sample matches all 49 borrows, 167 leverages and 1,890 swaps,
with 127 distributions left unassigned. The script separately sums the matching
amounts from the source events to check for missing or duplicate sources.

The rule identifies an accounting match, not causal incidence or an ultimate
beneficiary. In particular, `Leverage.reservesIn` is the borrowed reserve used
by the composite purchase, not a second contribution of outside user capital.

## What the ledger does not measure

Claims are reported as a separate event series. The script does not reconstruct
opening earned balances, user reward accruals, full token ownership, contract
reward-accounting rules, or all asset-transfer receipts. Allocations minus
claims therefore is **not** an estimate of unclaimed rewards. Neither series
identifies a holder's earnings, investment return, annualized yield, or net
financing cost. Shared staking eligibility does not establish which borrowers
received these allocations or a causal effect of rewards on borrowing.

Reproducing these accounting identities from the supplied archive does not
independently authenticate that archive against an Ethereum node or verify the
deployed implementations across upgrades.
