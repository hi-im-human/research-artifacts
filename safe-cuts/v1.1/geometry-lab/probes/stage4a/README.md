# Stage 4A probe: isolated prototype

**This directory is an isolated Stage 4A prototype.** It is not glab code, it is not registered in any glab `Registry`, and it issues no `rigorous_enclosure` or `formal_proof` claims. The design is [../../STAGE-4A-DESIGN.md](../../STAGE-4A-DESIGN.md), and the decision checkpoint is [../../STAGE-4A-RETURN.md](../../STAGE-4A-RETURN.md).

| File | Role |
|---|---|
| `ratint.py` | outward rational intervals (Fraction endpoints), verified integer square roots; standard library only |
| `ideal.py` | the ideal trimmed development `D`: exact model, exact face checks, Theorem S, enclosure recursion |
| `classify.py` | pair decisions (Theorem S, separating axis, interior witness) over a precision schedule; seam totals; `applies_to` |
| `firewall.py` | certificates that name only the ideal subject; float placement distance (diagnostic only) |
| `specimens.py` | real Stage 2/3 states and prerequisite evidence in a maintained Run (read-only use of glab) |
| `run_probe.py` | targets, direct scan, historical reference comparison, timing, receipts |
| `recheck_mpmath.py` | independent re-checker (mpmath `iv`, different construction), run in a throwaway environment; since repair A03 it enforces the bound bundle contract `stage4a.recheck_bundle/2` and exits 0 only when every seam is verified |
| `recheck_controls.py` | Stage 4A tampering controls for the original unbound bundle, kept as history; superseded by `tests/review_env/test_a03_recheck_contract.py` |
| `binding.py` | repair A02: rebuilds the subject from the Run states its spec names and resolves prerequisites from actual evidence at certificate issuance |
| `L4-CORRESPONDENCE.md` | written argument relating `D` to the manuscript's fixed full maps, including the trim-dependent normalization; not machine-checked |
| `tests/controls/` | controls C1-C7, run before any target |
| `tests/targets/` | targets T1-T3, the square prism, and the scan |
| `tests/repair/` | repairs A01 (domain and preconditions) and A02 (binding), in the maintained environment |
| `tests/review_env/` | repair A03 (re-checker contract) and the adapted copy of System's review cases; need mpmath, so they run only in the throwaway review environment and are skipped elsewhere |
| `review-cases/stage4a-review/` | System's review cases, verbatim |

**Repair receipts** are in `receipts/repair/` (A01-A03) and `receipts/recheck-repair/` (R01/R02); the original Stage 4A receipts are unchanged. Since R01/R02 the re-checker also verifies the recorded witness and Euclidean-gap bounds, checks the local geometry preconditions of its own construction before any geometry, lists its unverified diagnostic fields, and states its scope: it does not re-verify Stage 2 source correspondence or Run evidence, and `verified: true` is not a safety statement. System's review of `commit-62` is preserved under `<geometry-lab-project>/reviews/stage4a-repair-commit-62/`.

Commands, run from `engine/` with the maintained `.venv`. Nothing is installed into the maintained environment.

```bash
python -m pytest -p no:cacheprovider -q probes/stage4a/tests/controls
```

```bash
python -m pytest -p no:cacheprovider -q probes/stage4a/tests/targets
```

```bash
python -m probes.stage4a.run_probe probes/stage4a/receipts/results
```
