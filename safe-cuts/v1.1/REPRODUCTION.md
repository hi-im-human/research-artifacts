# Reproduction guide

This guide explains how to rebuild or recheck what this package contains. It keeps apart:
- historical results reported by the article and its records;
- checks run on this package's own files on 8 October 2026.

## Verify the package files

From the package root:

```text
sha256sum -c SHA256SUMS
```

`SHA256SUMS` covers every file except itself. `INVENTORY.tsv` lists every file except itself and `SHA256SUMS`.

## Formal theorem (Lean)

**What is included.** The complete selected project is in `formal/`, with:
- `lean-toolchain` (Lean 4.34.0);
- `lakefile.toml` (Mathlib v4.34.0);
- the dependency lock `lake-manifest.json`.

Keep the lock; do not update dependencies.

**Run the named checks.** From `formal/`:

```text
lake build GeneralTwoRimEndpointSanity
lake build GeneralTwoRimReversedFrustumSanity
lake build SelectedPositiveFullSafeSanity
```

**Notes.**
- The default target is `ConvexSectionNesting`, not the general endpoint, so a bare `lake build` does not replace these named checks.
- To tell fresh compilation from reuse of earlier outputs, build in a fresh copy that has no project build outputs, and record any dependency-cache reuse separately.
- One Lean source differs from the historical implementation snapshot: a comment in `MaximalSupportCells.lean` (see SANITATION.md).

**Check run for these Lean sources.**

On 8 October 2026 the three named targets were built from a fresh copy of the Lean project. Its `.lean` files, `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are byte-identical to this `formal/`. Only `WORKLOG.md`, which the build does not read, was edited afterwards, to replace research-folder locations.
- **Setup.** The copy had no project build outputs. Its dependency packages were copied read-only from an existing compiled cache whose nine package revisions equal `lake-manifest.json`. The tools were Lake 5.0.0 and Lean 4.34.0 on Windows.
- **Results.** All three targets built successfully:
  - `GeneralTwoRimEndpointSanity`: exit 0, 8,982 jobs, about 53 minutes;
  - `GeneralTwoRimReversedFrustumSanity`: exit 0;
  - `SelectedPositiveFullSafeSanity`: exit 0.
- **Fresh compilation.** The 61 project modules in the targets' import closures were compiled fresh.
- **Dependency cache.** No dependency package was rebuilt: the cache was reused, and none of its 8,927 `.olean` files changed.
- **Axioms.** The four public endpoints report exactly `propext`, `Classical.choice` and `Quot.sound`, and no `sorry` was reported.

This is a build check by the packaging worker, not a review of the proof.

**Historical evidence.**
- Codex's implementation receipts are in `evidence/formal-results/codex-2026-09-25/`.
- The separate Opus 5.5 review is `evidence/S8-opus-review.md`. It states its own dependency-cache and review limits.
- These are AI records, not human peer review.

## Article PDF

**What is included.** The PDF is `article/Safe_Cuts_Illustrated_v1.1.pdf` (23 pages). It is built from `article/manuscript.md` with the inputs in `article/pdf-build/`.

**Rebuild.** Install Python 3, Pandoc, XeLaTeX (with `graphicx` and `pdflscape`), Latin Modern and DejaVu Sans Mono. Then, from `article/pdf-build/`:

```text
python build_pdf.py ../manuscript.md build
```

The script:
- checks the pinned manuscript and Figure 1 crop fingerprints;
- inserts the two landscape Figure 1 pages;
- writes the PDF, the generated LaTeX, a build log and a result record.

**Byte identity.** The supplied PDF was built with Pandoc 3.1.11.1 and XeTeX 0.999998 (TeX Live 2026), and two builds were byte-identical. Other toolchains can produce different bytes. `article/pdf-build/README.md` records the hashes and the exact changes from edition 1.0.

**Figure 1 crops.** To regenerate the two Figure 1 page images from the supplied composite, run from `article/figure-1/`:

```text
python make_figure_panels.py ../../figure/out/safe-cuts-e4-e9-comparison.png regenerated
```

The script checks the source hash and performs exact crops only. Compare the output with `PANELS.json`, which records the boxes and hashes of the included crops.

## Companion figure

**Render.** Install Python with Matplotlib and NumPy. From `figure/`, render into a new folder so that the supplied outputs are not overwritten:

```text
python -B render_figure.py figure-data.json rerender
```

**Supplied images.**
- `figure/BUILD-RECORD.json` records the environment that made the supplied images: Python 3.13.5, Matplotlib 3.10.8, NumPy 2.3.5 and Pillow 12.3.0 on Linux.
- `figure/SHA256SUMS` identifies the supplied bytes.
- Rendering only redraws the figure. It does not recheck any certificate.

## Finite-case evidence behind the figure (Geometry Lab)

**The engine** is `geometry-lab/` (Python 3.11 or later). Its `pyproject.toml` pins:
- NumPy 2.4.4, the `numeric` extra;
- pytest 9.1.1, the `dev` extra.

The independent re-check tests also need mpmath 1.3.0.

**Run the suites.** From `geometry-lab/`:

```text
python -m pytest
python -m pytest probes/stage4a/tests
```

- **The engine path.** The second command needs `GLAB_ENGINE` set to the absolute path of `geometry-lab/`. For example:
  - in a POSIX shell: `GLAB_ENGINE="$PWD" python -m pytest probes/stage4a/tests`;
  - in PowerShell: set `$env:GLAB_ENGINE = (Get-Location).Path` first.
- **The verbatim review files.** The `review-cases/` folders and `probes/stage4a/review-cases/` keep earlier reviewers' test files. These are sanitized copies, with comments and labels only changed. Several of their tests fail by design, as the stage returns record:
  - the Stage 1–3 files look up record keys or checker versions that later stages replaced;
  - the Stage 4A file's genuine-bundle control uses the old unbound bundle layout.

  The maintained adaptations are in `tests/` and `probes/stage4a/tests/`, and they pass.

**Derivative evidence run.** From `geometry-lab/`, write fresh Stage 4B receipts:

```text
python -B -m tests.two_rim_ideal.write_stage4b_receipts OUT_DIR
```

Then re-check the bundle independently. Use a separate environment that has mpmath:

```text
python -I -B tests/two_rim_ideal_recheck/recheck_ideal_mpmath.py OUT_DIR/e11-recheck-bundle.json OUT.json
```

**Tests run for this package (8 October 2026).** Environment: Python 3.11.9, NumPy 2.4.4, pytest 9.1.1 and mpmath 1.3.0, on Windows.
- **Unchanged outcomes.** The suites were run on edition 1.0, on release candidate 1.1-rc1 and on this package, with the renamed review-case folders mapped. All 943 test outcomes were identical:

  | Suite | Result |
  |---|---|
  | `tests/` | 687 passed |
  | `probes/stage4a/tests` | 205 passed |
  | Stage 1 review case | 9 passed, 1 failed |
  | Stage 1 repair review case | 2 passed |
  | Stage 2 review case | 13 failed |
  | Stage 3 review case | 2 passed, 9 failed |
  | Stage 4A probe review case | 14 passed, 1 failed |

  These are the outcomes of the cases actually run, not proof of equivalence for every input.
- **Derivative run.** The run written by the commands above is in `geometry-lab/receipts/export-1.1/`.
  - Its 605 face pairs give 7 passing and 4 failing seams, with E4 passing and E9 failing.
  - The mpmath re-check verified all 11 seams.
  - The seam results, totals and state identities are identical to the historical run. See that folder's README.

These are finite-case checks of one specimen at one positive trim, resting on written lemmas that received AI review and are not machine-checked. They are not a proof of the universal theorem.
