# Lending the Redemption Reserve

**Collateral Release and Credit Limits**

Ömer Demirel · Snowfall Finance LLC · November 2026

Two versions of the paper are here. `short.pdf` is the 20-page version (16 pages of main text): the floor-cap contract, credit capacity under repayment rights, the reserve-extraction result and the curve-valued contract. `main.pdf` is the extended version (62 pages), which adds borrower incentives, a stationary economy, extraction bounds, the implementation in detail and the data.

| Path | Content |
|---|---|
| `main.tex`, `sections/`, `references.bib`, `figures/` | LaTeX source of the extended version |
| `short.tex`, `short/` | LaTeX source of the 20-page version |
| `lean/Safety.lean` | Lean 4 proof of the safety theorem (toolchain v4.31.0, Mathlib revision pinned in `lean/lakefile.toml`) |
| `contracts/` | Solidity reference implementation and Foundry tests |
| `scripts/dabc_model.py`, `scripts/test_model.py` | Integer reference model and its randomized tests |
| `scripts/numbers.py` | Every numerical example in the paper, blocks N01 to N17 |
| `scripts/credit_frontier.py` | Exact-rational checks for the credit-capacity section |
| `scripts/gen_differential.py` | Generator of the contract-versus-model traces |
| `empirics/` | Event data of the Baseline credit system and the analysis scripts |
| `outputs/` | Saved outputs of the commands below, of `forge test` and of the Lean check |
| `SHA256SUMS` | Hashes of the files in this repository |

## Commands

```bash
python3 -I scripts/numbers.py
python3 -I scripts/credit_frontier.py
python3 -I scripts/test_model.py 20000 300
python3 -I empirics/analyze.py
python3 -I empirics/rewards.py
```

From `lean/`: `lake build`. From `contracts/`: `forge test` (189 tests).

The Python scripts need Python 3 and no packages. None of them makes a network call; `empirics/fetch.py`, `empirics/supply.py` and `empirics/endpoint.py` download the data again from a public Ethereum endpoint if wanted.

The contract is a reference implementation for the paper. It is not audited and is not offered for deployment.
