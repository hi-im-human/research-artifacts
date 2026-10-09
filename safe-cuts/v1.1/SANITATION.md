# Privacy sanitation and derivative disclosure

This package was prepared from private research records. Its supporting documents, evidence records, Lean project and Geometry Lab engine are public derivatives of those records.

**What changed.** The derivatives were changed only to:
- remove private locators;
- repair links;
- re-pin the checks whose subjects changed, with new derivative records.

**What did not change.** Mathematical content, theorem statements, executable logic, test inputs' data and recorded results.

**What stays private.** The originals and the private original-to-derivative mappings are preserved privately. They are not part of this package.

Prior accepted omissions remain in force: private third-party correspondence is not included, and records that mention it do not quote it.

## What was changed, and how

**1. Publication edition 1.0 sanitation** (applies to every file it covered):
- local account names, private repository and branch names, and local or private folder paths were replaced by the placeholders below;
- the human coordinator appears under the public name Summer Bee;
- private commit identifiers were replaced by stable labels `commit-01` … `commit-83`;
- broken links were repaired, or turned into plain text marked "(not included)";
- two private figure-packaging scripts were left out (their recorded results are in `evidence/figure-packaging/FIGURE-VERIFICATION.json`).

**2. Further sanitation for this edition** (including the files edition 1.0 had kept byte-exact). Every remaining private locator was removed:
- **Commit identifiers:** in code comments, docstrings, test labels, provenance records, a test fixture and one Lean source comment. Each became the same `commit-NN` label used everywhere else.
- **Review-case folders:** five folders were renamed, together with the logs and references that name them (`review-cases/stage1-review`, `stage1-repair-review`, `stage2-review`, `stage3-review`, and `probes/stage4a/review-cases/stage4a-review`).
- **Branch name and private paths:** one private branch name and four private research-record paths were replaced by placeholders.
- **Author lines:** the author lines of three analytic documents name no private project.
- **Research-folder locations:** every path through a folder inside the private research record was replaced (73 lines in 26 files). A folder that is not included became `<historical-folder>`; file names, content hashes and the meaning of each reference were kept. References to the Lean project folder became `<lean-project>`. Where the cited file is included, the reference names its copy here, or the table below maps it.
- **Operational identifiers:** a local AI working-session identifier, inside a reviewer's scratch-folder path in `geometry-lab/probes/stage4a/receipts/repair/red-review-env-tests.log`, became `<review-scratch>` (two lines). A local agent-configuration path in `evidence/S8-opus-review.md` became the bare file name `haven.md`, marked as not included. No hash in the package pins either file.

### Placeholders

| Placeholder | Stands for |
|---|---|
| `<user>` | the local account name in a recorded path |
| `<private-repo>`, `<private-repo-clone>` | the private working repository and a local clone of it |
| `<private-branch>` | a private branch |
| `<research-record>` | the private research-record folder; the selected documents from it are in `supporting-sources/` and `evidence/` |
| `<historical-folder>` | a working folder inside the private research record that is not included here. Different references may stand for different folders; the file names and hashes that follow identify the files. |
| `<engine>` | the Geometry Lab engine root, included here as `geometry-lab/` |
| `<geometry-lab-project>`, `<geometry-lab-worktree>` | the private Geometry Lab project folder and a local checkout of it |
| `<lean-project>`, `<lean-worktree>` | the Lean project root (included here as `formal/`) and the local checkout that held it |
| `<local-temp>`, `<review-scratch>` | a local temporary folder and a reviewer's local scratch folder |

**Commit labels.** Labels `commit-01` to `commit-83` follow commit-date order. The same label always stands for the same private commit.

### Historical files that are included here

| Historical file named in the records | Copy in this package |
|---|---|
| `POLAR-WINDOW.md` | `supporting-sources/S4-polar-trace.md` (sanitized) |
| `independent-review.md` (Git blob `c17950e6`) | `supporting-sources/S5-small-variation.md` (sanitized) |
| `OPUS-INDEPENDENT-REVIEW.md` (Git blob `fee72841`) | `evidence/S8-opus-review.md` (sanitized) |
| `PROVENANCE-AND-LITERATURE-BASELINE.md` | `supporting-sources/S10-contributions-and-literature.md` (sanitized) |
| `results/codex-2026-09-25/` | `evidence/formal-results/codex-2026-09-25/` |
| The Lean project | `formal/` |
| `midsection_bridge.py` (Git blob `cce8c34f`) | `geometry-lab/tests/two_rim_dev/pinned_bridge/code/midsection_bridge.py` (export copy, see below) |
| `normal_fan_inputs.py` (`5445ec10`), `cyclic_normal_splice.py` (`314b1938`) | `geometry-lab/tests/two_rim_dev/pinned_bridge/baseline/code/` and `geometry-lab/tests/two_rim/pinned/` (byte-identical) |
| `beveled_source_certificate.json` (`c5714692`) | `geometry-lab/tests/two_rim_dev/historical/beveled_source_certificate.json` (byte-identical) |
| `beveled_source_certificate.py` (`2471d2d1`) | `geometry-lab/tests/two_rim_dev/historical/beveled_source_certificate.py.txt` (export copy, see below) |

Other cited historical files, such as `DRAFT-02.md`, `WORK NOTES.md`, `rational_intervals.py`, `mixed_fixture_certificate.py` and the agents' return files, are not included.

**Names that are kept**, because they are labels rather than private locators:
- **`engine/…` paths** inside the engine name its own components.
- **"Abandoned Observatory"** is the research bench's name, and **"Durer Edge-Unfolding"** names the research project in prose (`supporting-sources/S11-lineage.md`). Neither is used as a folder path in this package.
- **Paths under a placeholder** that name generic subfolders, temporary files or standard tool locations, for example `<geometry-lab-project>/reviews/…`, `<local-temp>\…` or `<user>\.elan\bin\lake.exe`, are kept because the placeholder already hides the private location.
- **The research collection's own address** (`github.com/hi-im-human/research-artifacts/…`) names the public account that hosts this package.

## Checks whose subjects changed, and their new records

Some edited files have exact bytes that code, tests or the evidence policy check. For each, the original is kept privately and the check was re-pinned to the new bytes with an explicit derivative record. No check was weakened or allow-listed.

- **Analytic documents.** `IDEAL-DEVELOPMENT-CONTRACT.md`, `STAGE-4A-DESIGN.md` and `probes/stage4a/L4-CORRESPONDENCE.md` each carry an export note.
  - The checker policy in `glab/ideal_check/checker.py` now pins their export copies: the contract's LF SHA-256, and the blobs of the two analytic documents.
  - `tests/two_rim_ideal/test_geometry_provenance.py` checks those pins.
  - `TWO-RIM-IDEAL-SCHEMA.md` names them.
  - The checker's source revision changed accordingly.
- **Provenance record.** `PROVENANCE-STAGE-4B.json` pins the export copies.
  - `export_derivative_1_1_rc1` lists the historical identifiers that the first export replaced. It is kept unchanged as the record of an unpublished release candidate.
  - `export_derivative_1_1` lists the release candidate's identifiers that this edition replaced.
- **Fixtures.** `tests/two_rim/golden_support.py` pins the sanitized fixtures `F1_translated_square_prism.json` and `X_pinned_hard_flat.json`. Only their provenance text changed; the coordinates are unchanged.
- **Historical code copies.** Two copies of historical code each contained a research-folder name, which became `<historical-folder>`.
  - In `tests/two_rim_dev/pinned_bridge/code/midsection_bridge.py`, the name was part of a fallback search path that is never reached in this package, because the bridge finds `pinned_bridge/baseline/code` first. `tests/two_rim_dev/bridge_support.py` pins the export copy and names the historical blob `cce8c34f`.
  - `tests/two_rim_dev/historical/beveled_source_certificate.py.txt` is stored for reference and never executed. `tests/two_rim_dev/eleven_panel.py` pins the export copy and names the historical blob `2471d2d1`.
- **New evidence.** Because the checker policy changed, `geometry-lab/receipts/export-1.1/` holds a fresh Stage 4B evidence run, its independent mpmath re-check, and a field-by-field comparison with the historical run.
  - The seam results, totals and state identities are identical.
  - Only pins, revisions, evidence identifiers, the run digest and the platform string differ.
  - `geometry-lab/receipts/export-1.1-rc1/` holds the same kind of run for the unpublished release candidate. It is kept unchanged; its identifiers refer to that candidate's bytes, not to this package.

## Hashes that identify private originals

Some records quote a hash of a document whose copy here was sanitized. Those quoted hashes identify the private original, not the copy in this package:
- **The historical Stage 4B receipts** (`receipts/stage4b/results/`, `receipts/stage4b-repair/results/`) and `STAGE-4B-PLAN.md` quote the original analytic documents. The historical receipts are kept unchanged as historical evidence.
- **The review-case docstrings** in the adapted tests and generators, `STAGE-1-REPAIR-PLAN.md`, `STAGE-3-REPAIR-RETURN.md` and `STAGE-4A-REPAIR-RETURN.md` quote the verbatim review files. The included review cases are sanitized copies; the docstrings say so.
- **`PROVENANCE-STAGE-2.json`** quotes the original fixtures.
- **`PROVENANCE-STAGE-3.json`, `ELEVEN-PANEL-MAPPING.md`, `STAGE-3-PLAN.md`, `STAGE-3-RETURN.md`, `TWO-RIM-DEVELOPMENT-SCHEMA.md` and `glab/two_rim/develop.py`** quote the historical blobs of `midsection_bridge.py` (`cce8c34f`) and `beveled_source_certificate.py` (`2471d2d1`). The Stage 3 receipts record the same identifiers. The copies here are the export copies described above.
- **`PROVENANCE-STAGE-3.json`, the Stage 3 receipts and `probes/stage4a/receipts/probe-environment.json`** record the historical source revision of the Stage 3 development code. In this package one docstring line of `glab/two_rim/develop.py` names `<historical-folder>`, so that code's source revision, and with it the `two_rim.cut.open@1` action revision, differs. The new value is recorded in `geometry-lab/receipts/export-1.1/`.
- **`supporting-sources/S1-physical-source.md`** quotes the original S5. **`supporting-sources/S11-source-status-manifest.json`** quotes the original S8 and the original `formal/MaximalSupportCells.lean`.

`SHA256SUMS` and `INVENTORY.tsv` identify the bytes actually included.

## What remains, and why

- **Public dependency URLs** of the Lean packages remain in `formal/lake-manifest.json` and `formal/lakefile.toml`. They are needed for reproduction.
- **The figure's SVG hash salt** (`safe-cuts-first-figure`) is a generic reproducibility string. It is kept so that the supplied figure files stay byte-identical.
- **No other private locator, account name, personal name or contact detail** was found in the package's files, file names or media metadata. The checks are listed in REPRODUCTION.md and summarized below.

## Packaging checks (8 October 2026)

These checks verify integrity, privacy and unchanged outcomes. None is a mathematical review.

- **Privacy:** scans of every file, file name and media metadata, a census of research-folder references, and a check for the previously withheld correspondence.
- **Integrity:** links checked inside the package; every JSON file parsed; inventory and checksum verification.
- **Geometry Lab:** the test suites were run before and after the changes: 943 tests with identical outcomes.
- **Evidence:** the derivative Stage 4B run and its mpmath re-check.
- **Lean:** the three named targets were built on these Lean sources.

The tested outcomes are for the cases actually run, not a proof of equivalence for every input.
