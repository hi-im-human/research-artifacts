# Supporting-source map

The article cites supporting sources S1–S13. Each is included in this package at the path below. Paths are relative to this folder.

- **Supporting documents and evidence records** are privacy-sanitized copies of the research records. [SANITATION.md](SANITATION.md) lists what changed.
- **Quoted hashes** inside these records identify the private original documents, not the copies here.

| Article identifier | Included material |
|---|---|
| S1 | [Physical source argument](supporting-sources/S1-physical-source.md), read with S6 |
| S2 | [Folded-turn and radial-support argument](supporting-sources/S2-folded-turn-radial-support.md) |
| S3 | [Extremal-seam argument](supporting-sources/S3-extremal-seam.md) |
| S4 | [Polar trace argument](supporting-sources/S4-polar-trace.md). Its additional window assumption is not imported into the article. |
| S5 | [Small-variation proof](supporting-sources/S5-small-variation.md) |
| S6 | [Physical source audit](supporting-sources/S6-physical-source-audit.md). Its source links point to the included Lean files. |
| S7 | [GeneralTwoRimEndpoint.lean](formal/GeneralTwoRimEndpoint.lean), [GeneralTwoRimUnfolding.lean](formal/GeneralTwoRimUnfolding.lean), and the complete included [Lean project](formal/) |
| S8 | [Opus 5.5 review](evidence/S8-opus-review.md), including the checks described in that report. The Codex result directory listed under S9 is not an Opus run archive. |
| S9 | [Codex implementation return](evidence/S9-implementation-return.md) and [Codex result records](evidence/formal-results/codex-2026-09-25/) |
| S10 | [Contribution and literature baseline](supporting-sources/S10-contributions-and-literature.md) |
| S11 | [Source status](supporting-sources/S11-source-status.md), [lineage](supporting-sources/S11-lineage.md) and [source-status manifest](supporting-sources/S11-source-status-manifest.json) |
| S12 | [OriginalFacetCertificates.lean](formal/OriginalFacetCertificates.lean), [NormalFanSplice.lean](formal/NormalFanSplice.lean), [CutSurfaceQuotient.lean](formal/CutSurfaceQuotient.lean), and the two S7 modules |
| S13 | [Author self-review](evidence/S13-author-self-review.md) and [its check records](evidence/author-self-review-checks/) |

**Formal route of Section 10.1.** The zero-defect branch runs through `MixedTurnSafeCut` in this chain:
1. `exists_sameCutSameMaps_of_delta_zero` and `sameCutSameMaps_of_intrinsicTMixed`, in [GeneralTwoRimUnfolding.lean](formal/GeneralTwoRimUnfolding.lean);
2. `fixedCut_nonoverlap`, in [PhysicalMixedTurnDevelopment.lean](formal/PhysicalMixedTurnDevelopment.lean);
3. `small_variation_nonoverlap`, in [MixedTurnSafeCut.lean](formal/MixedTurnSafeCut.lean).

**Opus review and Codex receipts are separate.** The Opus review (S8) and Codex's implementation receipts (S9) are separate events by separate agents.
- Codex's receipts are an implementer's records, not a non-author review.
- The Opus review is an AI review with stated limits, not human peer review.

**Records not in this package.** Some records cite research documents that are not included. Those mentions are plain text marked "(not included)", or name the placeholder `<historical-folder>`. Where a cited historical file is included, [SANITATION.md](SANITATION.md) lists its copy here.

## Figure 1 and its evidence

- **Figure files:** [figure/](figure/), with the manifest `figure/SHA256SUMS`. The article's two landscape pages are exact crops of `figure/out/safe-cuts-e4-e9-comparison.png`. [article/figure-1/PANELS.json](article/figure-1/PANELS.json) records the crop boxes and hashes.
- **Historical records.** `figure/figure-data.json` names its historical inputs `e11-ideal-run.json` and `e11-ideal-summary.json`.
  - Both are in [geometry-lab/receipts/stage4b/results/](geometry-lab/receipts/stage4b/results/), with identical copies in `geometry-lab/receipts/stage4b-repair/results/`.
  - The data's `run_digest` equals the `run_digest` of that run.
- **Derivative evidence.** A fresh run with this edition's rebound checker, its independent re-check, and a field-by-field comparison with the historical run are in [geometry-lab/receipts/export-1.1/](geometry-lab/receipts/export-1.1/). The earlier run in [geometry-lab/receipts/export-1.1-rc1/](geometry-lab/receipts/export-1.1-rc1/) checked an unpublished release candidate and is kept unchanged as a historical record.
- **The checker.** Its contract, schema and tests are in [geometry-lab/](geometry-lab/). Start with [IDEAL-DEVELOPMENT-CONTRACT.md](geometry-lab/IDEAL-DEVELOPMENT-CONTRACT.md), [TWO-RIM-IDEAL-SCHEMA.md](geometry-lab/TWO-RIM-IDEAL-SCHEMA.md) and [STAGE-4B-RETURN.md](geometry-lab/STAGE-4B-RETURN.md).

These are finite-case records for one specimen at one positive trim. They are separate from the universal theorem and its Lean formalization.

## Names and placeholders in historical records

- **Agent names.** Historical records call the article's Forge "Letta Forge" and its Codex "Codex Forge".
- **Placeholders.** Placeholders such as `<private-repo>`, `<historical-folder>` and `<engine>` stand for private or local locations. Labels such as `commit-07` stand for private commits. [SANITATION.md](SANITATION.md) defines them.

This map records locations, not new verdicts.
