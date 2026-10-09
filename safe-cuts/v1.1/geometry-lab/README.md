---
title: Geometry Lab engine (Stage 1 core, repaired)
status: Stage 1 core (repaired, plus C01), the Stage 2 exact source-geometry port, Stage 3 static development (numerical, repaired S01-S04), and the Stage 4B positive-trim ideal lane (implemented on the work branch; under bounded repair and review; not accepted or released)
dg-publish: false
---

# Geometry Lab engine: Stage 1 core

The core is a standard-library-only Python package, `glab.core`. It provides:

- exact input
- canonical records and content hashes
- a versioned registry of trusted local actions and checkers
- **one ordered history of recorded action and check attempts**
- per-claim evidence with conservative, coverage-aware summaries
- whole-run integrity with chronology checks and an optional external anchor
- whole-record replay

Contracts are in [DESIGN.md](DESIGN.md). The repair contract is in [STAGE-1-REPAIR-PLAN.md](STAGE-1-REPAIR-PLAN.md), and the repair return is in [STAGE-1-REPAIR-RETURN.md](STAGE-1-REPAIR-RETURN.md). The original [STAGE-1-RETURN.md](STAGE-1-RETURN.md) and `receipts/` are kept as history, and `receipts/repair/` holds the repair receipts.

Run files use format `glab.run/2`. The loader rejects the Stage 1 format, `glab.run/1`, with an explanation rather than migrating it. The v1 file `receipts/demo/demo.run.json` is a historical artifact.

## Stage 2: exact two-rim source geometry

- **`glab.two_rim`** turns two rational rims and a positive rational height into two records: a recorded normalization (the source state) and the original maximal facets, hinges, rim edges, and caps (the material state).
- **`glab.check.two_rim_source`** (v2) checks both independently, with exact predicates and a brute-force supporting-plane oracle. It validates each record's schema first. Through the core's read-only dependency context, it also checks that each material matches its actual source; that check is `two_rim.material.matches_parent_source`.

The Stage 2 repair (D01–D03) is recorded in [STAGE-2-REPAIR-PLAN.md](STAGE-2-REPAIR-PLAN.md) and [STAGE-2-REPAIR-RETURN.md](STAGE-2-REPAIR-RETURN.md), with receipts in `receipts/stage2-repair/`. The Stage 2 receipts in `receipts/stage2/` are historical, v1-checker artifacts.

Stage 2 itself has no floating placements, cuts, trims, or rendering. The contract is in [TWO-RIM-SCHEMA.md](TWO-RIM-SCHEMA.md), the plan in [STAGE-2-PLAN.md](STAGE-2-PLAN.md), provenance in [PROVENANCE-STAGE-2.json](PROVENANCE-STAGE-2.json), and the return in [STAGE-2-RETURN.md](STAGE-2-RETURN.md).

## Stage 3: static development (numerical)

- **`glab.two_rim.cut`** opens one original hinge as the seam and records the exact cut topology: face chain, retained hinges, face occurrences, and glue classes.
- **`glab.two_rim.develop`** places every face in the plane with a float64 affine map (rotation plus translation), ported from the historical `midsection_bridge.py` formulas.
- **`glab.two_rim.trim`** applies a positive exact trim depth to each face and reuses the same maps.
- **`glab.check.two_rim_development`** checks all three states independently with NumPy, which is pinned as the optional `numeric` extra. It never imports the generator.
  - Every face pair is tested; results are `pass`, `fail`, or `unknown`, and shared glued material is recorded as information only.
  - Registered versions: the cut checker is v1; the development and trimmed checkers are v2 since the repair.
  - Numerical claims declare `NUMERICAL_TOLERANCE_POLICY` in `Claim.tolerances`.
- **`glab.two_rim.search`** runs cut, develop, trim, and checks for every original hinge. It is an enumerated candidate search, not proof-guided seam selection.
  - It reports **local** totals (the chain from the material down) separately from **source-linked** totals, which add the Stage 2 source and material bundles, including `matches_parent_source`.
- **`glab.view.static`** writes a static SVG and polygon OBJ files from an exported view.

Numerical results are diagnostics: no Stage 3 claim uses `rigorous_enclosure`, and a numerical `unknown` is not a proof of safety. The plan is in [STAGE-3-PLAN.md](STAGE-3-PLAN.md), the contract in [TWO-RIM-DEVELOPMENT-SCHEMA.md](TWO-RIM-DEVELOPMENT-SCHEMA.md), provenance in [PROVENANCE-STAGE-3.json](PROVENANCE-STAGE-3.json), the eleven-panel mapping in [ELEVEN-PANEL-MAPPING.md](ELEVEN-PANEL-MAPPING.md), the return in [STAGE-3-RETURN.md](STAGE-3-RETURN.md), and receipts in `receipts/stage3/`. The Stage 3 repair (System review `stage3-review`, S01-S04) is in [STAGE-3-REPAIR-PLAN.md](STAGE-3-REPAIR-PLAN.md) and [STAGE-3-REPAIR-RETURN.md](STAGE-3-REPAIR-RETURN.md), with receipts in `receipts/stage3-repair/`. The `receipts/stage3/` files are historical, v1-checker artifacts.

## Stage 4B: positive-trim ideal lane (under review)

Implemented on the work branch, not accepted or released. It adds a separate exact-input lane for the ideal trimmed development `D`: the state and action in `glab.two_rim.ideal_actions`, the independent checker in `glab.ideal_check`, the arithmetic in `glab.rigorous`, and the source-linked search in `glab.two_rim.ideal_search`. The float lane is unchanged. Contract: [TWO-RIM-IDEAL-SCHEMA.md](TWO-RIM-IDEAL-SCHEMA.md) and [IDEAL-DEVELOPMENT-CONTRACT.md](IDEAL-DEVELOPMENT-CONTRACT.md). Records: [STAGE-4B-RETURN.md](STAGE-4B-RETURN.md) and [STAGE-4B-REPAIR-RETURN.md](STAGE-4B-REPAIR-RETURN.md).

## Commands (run from `engine/`)

Create the ignored local environment once. Pytest is the only development dependency, and it is pinned:

```bash
python -m venv .venv && .venv/Scripts/python -m pip install pytest==9.1.1
```

Stage 3 also needs the pinned NumPy extra:

```bash
.venv/Scripts/python -m pip install numpy==2.4.4
```

Run the core tests, which include the adapted review cases:

```bash
python -m pytest -p no:cacheprovider -q tests/core
```

Run System's review cases verbatim. R05 there reads the v1 key `actions`; see the repair return:

```bash
python -m pytest -p no:cacheprovider -q review-cases/stage1-review/test_review_regressions.py
```

Run the demo. It uses a tiny integer domain defined inside the example, and covers rejected, failed, one-claim, multi-claim, zero-claim, and crashed-check attempts, an unknown, and an external-anchor comparison:

```bash
python examples/core_demo.py receipts/repair/demo
```

Run the Stage 2 domain tests, which include the golden comparison with the pinned originals on the 4 fixtures and 200 seeded random pairs:

```bash
python -m pytest -p no:cacheprovider -q tests/two_rim
```

Regenerate the 200-case golden and oracle receipt:

```bash
python -m tests.two_rim.write_golden_receipt receipts/stage2-repair/random-200-v2.json
```

Run the headless Stage 2 demo:

```bash
python examples/two_rim_demo.py receipts/stage2-repair/demo
```

Run the Stage 3 development tests, which include the eleven-panel regression and the golden comparison with the pinned bridge:

```bash
python -m pytest -p no:cacheprovider -q tests/two_rim_dev
```

Regenerate the Stage 3 golden receipt (every seam of the fixtures, the eleven-panel source, and the Stage 2 random and supplementary pairs):

```bash
python -m tests.two_rim_dev.write_development_golden_receipt receipts/stage3-repair/development-golden.json
```

Run the Stage 3 demo (eleven-panel and F2 searches, the historical comparison, save, replay, and the inspection view). It needs the full repository checkout, because it imports test-side support for the historical mapping:

```bash
python examples/two_rim_development_demo.py receipts/stage3-repair/demo
```

Run System's Stage 3 review cases verbatim. The development checkers are v2 now, so 9 cases stop at the v1 version lookup; the adapted copy `tests/two_rim_dev/test_review_stage3_adapted.py` runs in the suite:

```bash
python -m pytest -p no:cacheprovider -q review-cases/stage3-review/test_stage3_regressions.py
```

Render any exported view as SVG and OBJ:

```bash
python -m glab.view.static VIEW.json OUT_PREFIX
```

## What the guarantees mean

- **A loaded run is internally consistent, never authenticated.** Detecting a wholesale rewrite requires a digest kept somewhere else. The demo writes `retained-digest.txt` next to its run only for illustration.
- **Loading is structural.** It checks chronology and never executes anything. Registration-dependent checks (existence, parameter types, kinds) happen at replay.
- **Replay reports `reproduced` only when three things hold:** every entry matched as a complete record, the environment matched, and the full run digest was reproduced.
- **A crashed checker records a failed attempt, not a failed predicate.**
- **`verified` requires re-execution and coverage.** It is true only for passing, covering evidence that this process produced or replayed. The default required coverage is `"all"`.
