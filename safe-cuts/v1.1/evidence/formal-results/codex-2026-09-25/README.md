# Codex verification receipts — 2026-09-25

These receipts belong to Codex's continuation, not Letta's previous runs. All 23 commands designated as required final passes in `verification.json` completed with exit 0. Failed and aborted diagnostics are retained separately in `command-receipts.json`.

## Reproduce the public result

Use the repository's existing project directory:

```text
<lean-project>
```

The pinned toolchain is Lean 4.34.0, with Mathlib revision `5ed2965256430c3649e86755f9576b54eca72435`. On this host, Lake is `C:\Users\<user>\.elan\bin\lake.exe`; the commands below use `lake` for portability.

```text
lake build GeneralTwoRimEndpointSanity
lake build GeneralTwoRimReversedFrustumSanity
lake build SelectedPositiveFullSafeSanity
lake build
lake build GeneralTwoRimUnfoldingSanity RadialOriginalSeamSanity FixedBaselinePolarTraceSanity
```

The first target imports both completed nonzero branches and the zero branch, prints public types/contracts and recursively audits axioms. The second checks both physical frusta, their opposite nonzero turn signs, their failure of T-mixedness, and their applications of the new endpoint.

`baseline-regression-plan.json` lists the exact additional commands covering all 43 baseline files: 36 registered modules and seven standalone sanity sources. Adapt only the Lake executable path and repository working directory when reproducing on another host. No package update is part of this recipe.

The historical `SelectedNegativeFullDevelopment` target is preserved but is not imported by this public endpoint. Its fresh rebuild was manually stopped; no new passing receipt for that unused wrapper is claimed. The endpoint instead uses `SelectedNegativeDirectDevelopment`, whose dependency is the existing checked negative full-safety theorem and the newly compiled common source assembly.

## Evidence files

- `public-types-and-axioms.txt`: actual elaborated endpoint inputs, original cut-surface/trim/safety contracts, same-map identities and recursive axioms.
- `frustum-sanities.txt`: both exact physical sources, their nonzero signs and non-T-mixedness, and branch/general applications.
- `upstream-axioms.txt`: folded projection, physical RF, radial seam, polar trace and zero-branch axiom checks from the regression build.
- `source-audit.json`: all 73 final Lean SHA-256 values, unchanged 43-file baseline, the sole modified inherited Lean file, pins, and keyword-scan details. All keyword hits are comments.
- `command-receipts.json`: exact commands, working directories, timings, exit codes, timeouts, source hashes and hashes/locations of complete local logs. Failed attempts are included; consult `required_final_pass`.
- `python-regressions.json` and `regression-*.txt`: separate suite counts, paths and complete test output. The source bridge's eight diagnostics are floating; finite controls are not universal proof evidence.
- `verification.json`: checkout identity, pins, configuration hashes and the required passing command list.

The source hashes in a command receipt were collected when that command finished. The final source audit independently checks the current files. A passing Lake target may replay unchanged dependencies; these receipts do not assert a clean recompilation of every dependency.

Full logs and the reversible initial source snapshot remain at `<local-temp>\codex-general-lean-20260925`. No running build is required to use the result.

After Summer Bee authorized commit/push, the three public endpoint, opposite-frustum, and full-safety sanity targets were checked again together. `pre-push-endpoint-build.json` records this separate successful command and its source hashes; `pre-push-endpoint-build.txt` contains the complete output (trailing whitespace normalized). This additional check reused cached dependencies and does not replace the earlier detailed receipts.
