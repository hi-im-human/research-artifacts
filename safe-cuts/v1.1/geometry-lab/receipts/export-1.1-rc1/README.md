# Derivative Stage 4B evidence for the 1.1-rc1 research export

**Why this exists.** The export removes private locators from three analytic documents that the ideal-development checker's evidence policy pins by hash. Those documents are `IDEAL-DEVELOPMENT-CONTRACT.md`, `STAGE-4A-DESIGN.md` and `probes/stage4a/L4-CORRESPONDENCE.md`; their mathematics is unchanged. The policy in `glab/ideal_check/checker.py` and `PROVENANCE-STAGE-4B.json` therefore pin new identifiers, and the checker revision changes with them. Rather than relabel old evidence, this folder holds a fresh run made with the rebound checker.

## Contents

- **`stage4b-results/`** is the output of `python -B -m tests.two_rim_ideal.write_stage4b_receipts` on the export's engine. It was run on 8 October 2026 with Python 3.11.9 and NumPy 2.4.4 on Windows.
  - `MANIFEST.json` covers every file except `timing.json`.
  - `e11-ideal-summary.json` gives the eleven-panel verdicts at δ = 1/10000.
- **`e11-recheck-mpmath.json`** is the independent re-check of `stage4b-results/e11-recheck-bundle.json` by `tests/two_rim_ideal_recheck/recheck_ideal_mpmath.py`, with mpmath 1.3.0. All 11 seams are verified, and the recomputed verdicts agree with the summary.
- **`comparison-with-historical.json`** compares these receipts field by field with the historical ones in `../stage4b-repair/results/`.

## What the comparison shows

**Identical:**
- the per-seam results, the totals and the state identities;
- 605 face pairs: 110 decided by Theorem S, 484 by a separating axis and 11 by an interior witness;
- E0–E2 and E4–E7 pass; E3, E8, E9 and E10 fail;
- the historical comparison, the port-equivalence digests and the 32 prism cases.

**Different:** only the analytic-dependency pins, the checker revision, the evidence identifiers derived from them, the run digest, and the platform build string.

## What did not change

The historical receipts in `../stage4b/` and `../stage4b-repair/` keep their original identifiers. They identify the private originals of the analytic documents. The companion figure's display data cites the historical run's digest.

These are finite-case checks of one specimen at one positive trim. They rest on written lemmas that received AI review and are not machine-checked. They are not a proof of the universal theorem.
