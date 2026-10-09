---
title: Eleven-panel historical source mapped to Geometry Lab IDs
author: Claude Code session agent, Claude Opus 5.5
date: 2026-09-29
status: Stage 3 mapping artifact; generated from the byte-verified certificate copy; no historical label reaches any checker
dg-publish: false
---

# Historical source and convention

| Item | Pin |
|---|---|
| Historical certificate `<historical-folder>/review/beveled_source_certificate.json` (byte-identical copy: `tests/two_rim_dev/historical/beveled_source_certificate.json`) | Git blob `c571469284a97f9cd2df75b1f047bda3c0bcc7fc`, at `commit-11` |
| Historical verifier `beveled_source_certificate.py` | Git blob `2471d2d11ee2f8ae9ec3f0717f99d35d90a2e2aa`, stored here only as `tests/two_rim_dev/historical/beveled_source_certificate.py.txt` and never executed |
| Test copies | `tests/two_rim_dev/historical/`; their blobs are re-verified whenever the certificate is loaded |

**Historical convention.** From the verifier and `mixed_fixture_certificate.iv_unfold` at `commit-11`:
- `top` and `bottom` are `hull2` of the listed points.
- `cycle = splice_cycles(top[::-1], bottom[::-1])`, and hinge `t` is `cycle.original_edges(HEIGHT)[t]`, recorded as `original_hinges[t]`.
- Face `f` is the panel between hinges `f` and `f+1`.
- Cut `k` opens hinge `k`, and panel position `s` of cut `k` is face `(k+s) mod 11`.
- The trim uses `low = (1−δ)·B + δ·A` and `high = δ·B + (1−δ)·A`, with `δ = 1/10000` along the original normalized height.
- The historical safety test was exact interval arithmetic: a strict separating axis for every non-adjacent pair, plus `adjacent_opposite` for chain neighbors.

**Geometry Lab convention** (`TWO-RIM-SCHEMA.md`). Each normalized rim starts at its lexicographic minimum and runs clockwise. Hinge `E_t` is `support_pairs[t]`; face `F_t` lies between `E_t` and `E_{t+1}`; cut seam `E_k` opens `E_k`, and the chain is `F_k, F_{k+1}, …`. The trim convention is the same.

# Method

- **Mapping by exact coordinates only.** Each historical `original_hinges[t]` is matched to the current hinge with equal exact lower and upper coordinates. No numeric label is assumed to survive normalization.
- **Result.** The map is a bijection and a single cyclic rotation: current index = historical index + 3 (mod 11).
- **Face check.** Every historical face `f` maps to the current face whose entry is `map(f)` and whose exit is `map(f+1)`.

| Historical hinge / cut | Current seam | Lower (z = 0) | Upper (z = 1/10000) | Historical face (panel after the hinge) | Current face |
|---|---|---|---|---|---|
| 0 | E3 | (-85, 60) | (-15, 50) | 0 | F3 |
| 1 | E4 | (18, 91) | (-15, 50) | 1 | F4 |
| 2 | E5 | (60, 74) | (-15, 50) | 2 | F5 |
| 3 | E6 | (60, 74) | (16, 27) | 3 | F6 |
| 4 | E7 | (60, 74) | (31, -11) | 4 | F7 |
| 5 | E8 | (303/10, -77/2) | (31, -11) | 5 | F8 |
| 6 | E9 | (564/25, -4993/100) | (31, -11) | 6 | F9 |
| 7 | E10 | (1693/100, -2569/50) | (31, -11) | 7 | F10 |
| 8 | E0 | (1693/100, -2569/50) | (-40, -28) | 8 | F0 |
| 9 | E1 | (-26, -53) | (-40, -28) | 9 | F1 |
| 10 | E2 | (-85, 60) | (-40, -28) | 10 | F2 |

**Historical cut-6 overlap, mapped:**
- Cut 6 maps to seam **E9**.
- Panel positions [1, 9], which are historical faces F7 and F4, map to current **F10 and F7**.
- The witness point, in the historical cut-6 frame, is `(39037647/1000000, 565877/1000000)`.
- Placing the historical frame onto ours through the first panel's seam copy (`test_historical_witness_point_is_interior_to_both_mapped_faces`) puts that point strictly inside both mapped face images. This is numerical, with a cross-product margin above 1e-3.

# Classification comparison at δ = 1/10000

Source: `receipts/stage3/demo/eleven-panel-comparison.json`.
- Current results are `two_rim.development.face_interiors_disjoint_all_pairs` on the trimmed development: float64 numerical diagnostics.
- The historical classes are exact interval certificates for this ordinary trim only. They say nothing about the untrimmed band.

| Historical cut | Current seam | Historical exact class | Current all-pairs | Current unglued pairs | Comparison | Interior overlaps found (face pair: area) |
|---|---|---|---|---|---|---|
| 0 | E3 | unsafe | fail | fail | agree (overlap detected) | F3/F2: 4.246 |
| 1 | E4 | safe | unknown | pass | not contradicted (unresolved near-contact) | none |
| 2 | E5 | safe | unknown | pass | not contradicted (unresolved near-contact) | none |
| 3 | E6 | safe | unknown | pass | not contradicted (unresolved near-contact) | none |
| 4 | E7 | safe | unknown | pass | not contradicted (unresolved near-contact) | none |
| 5 | E8 | unsafe | fail | fail | agree (overlap detected) | F8/F7: 7.05; F9/F7: 0.9203; F10/F7: 1.686 |
| 6 | E9 | unsafe | fail | fail | agree (overlap detected) | F9/F7: 0.9203; F9/F8: 18.98; F10/F7: 1.686; F10/F8: 9.487 |
| 7 | E10 | unsafe | fail | fail | agree (overlap detected) | F10/F7: 1.686; F10/F8: 9.487; F10/F9: 38.49 |
| 8 | E0 | safe | unknown | pass | not contradicted (unresolved near-contact) | none |
| 9 | E1 | safe | unknown | pass | not contradicted (unresolved near-contact) | none |
| 10 | E2 | safe | unknown | pass | not contradicted (unresolved near-contact) | none |

**Findings:**
- **Every historically unsafe cut (0, 5, 6, 7) is detected as `fail`,** with interior overlaps well beyond tolerance.
  - Each historical witness pair appears among the failing pairs: cut 0 has the end panels F3 and F2; cuts 5, 6, and 7 each include F10 and F7.
  - The current check also reports further overlapping pairs in those cuts. The historical verifier needed only one witness per unsafe cut.
- **Every historically safe cut is `unknown`, never `pass` or `fail`.**
  - In each, every pair that shares no glued material passes. The 10 retained-adjacent pairs split two ways, varying by seam:
    - between 1 and 5 are decided exactly on the represented float coordinates;
    - the remaining 5 to 9 are `near_contact_unresolved`. Those unresolved pairs are all, and only, retained-adjacent pairs.
  - Their recorded opposite-sides margins (information only) are at least about 1e-4. That is small because trimmed triangles have edges of order δ, but it is still about 1000 × τ.
  - Resolving them needs Stage 4 enclosures, where the historical verifier used exact intervals.
  - This is **not a disagreement**. It is the Stage 3 policy that glued proximity never upgrades an unresolved pair.
- **No disagreement was found.** The checker never received the historical labels, which are compared only in tests and in the demo.
