---
title: Geometry Lab engine: reconciled design (Stage 0) and Stage 1 contracts
author: Claude Code session agent, Claude Opus 5.5 (claude-opus-5-5)
date: 2026-09-28
status: Stage 1 contracts, reconciled with the executable API during the R01-R05 repair
dg-publish: false
---

# 1. Sources reconciled

| Source | Pin |
|---|---|
| System's Stage 1 authorization, `<geometry-lab-project>/SYSTEM-TO-CLAUDE-STAGE-1.md` | `commit-20`, blob `eeb384209a73a814c122c6834ecc4c6742d291dc`, read from `origin/main` at `commit-21` without merging |
| Reviewed return and architecture: `assessment/ARCHITECTURE.md`, `IMPLEMENTATION-PLAN.md` | `commit-19` (this branch's base for Stage 1) |
| `DESIGN-BRIEF.md` (§2 records, §4 evidence semantics) | unchanged since `commit-18` |
| System's Stage 1 review, `<geometry-lab-project>/reviews/stage1-review/REVIEW.md` | `commit-27`, blob `5993590d9fcc96e9b4c113927a035ad2320bcde1` (repair contract: `STAGE-1-REPAIR-PLAN.md`) |

**The reconciliation is faithful.** It keeps the approved architecture: a standard-library core, a separate future two-rim module, an independent checker, and file-based adapters. Amendments A to E are adopted as binding. The only deviation from `ARCHITECTURE.md` is in its "Replace or discard" row for `compas_probe.py`: under amendment E, "delete" becomes "not adopted, preserved unchanged." The historical header "no stage authorized" in `IMPLEMENTATION-PLAN.md` is superseded for Stage 0 and Stage 1 only.

# 2. Stage 1 boundary

Stage 1 builds `glab/core` only: records, a registry, evidence, run files, and replay. It contains no geometry, NumPy, generator, checker implementation, or viewer. Tests and the demo define tiny integer actions and checkers locally, which exercises the generic API without adding a domain to the core. Stage 2, where source geometry is ported, would be the first consumer of these schemas. It is not authorized.

# 3. Numeric domains and exact input (`glab.core.numbers`)

- `parse_exact(value) -> Fraction` accepts:
  - `int` (but not `bool`)
  - strings for an integer, a fraction `p/q`, a decimal, or a decimal with exponent
- It rejects `float`, `bool`, `nan`/`inf`, zero denominators, empty strings, and any other type, each with `ExactInputError`.
- `format_exact(q) -> str` produces canonical `"n"` or `"n/d"` text. For example, `"0.5"`, `"1/2"`, and `"2/4"` all normalize to `"1/2"`.
- Every state declares its payload **representation**:
  - `exact`: numbers are exact strings or integers. JSON floats are forbidden and rejected at validation.
  - `approximate`: finite floats are permitted, and the state is approximate as a whole.
  - `mixed`: floats are permitted. The domain module must document which fields are exact.
- Converting a float to a `Fraction` never relabels a state as `exact`. No API performs that promotion.

# 4. Records and semantic hashes (`glab.core.records`)

**Canonical JSON** uses sorted keys, separators `(",", ":")`, ASCII only, and finite numbers only. Keys must be strings, and values must be of JSON types. `content_hash(obj)` is `"sha256:" + hex(sha256(canonical))`. **`strict_loads(text)`** rejects duplicate object keys and the literals `NaN`, `Infinity`, and `-Infinity`.

**State record, `glab.state/1`:**

```json
{"schema": "glab.state/1", "kind": "<domain.kind>", "parent": null | "sha256:...",
 "representation": "exact" | "approximate" | "mixed", "payload": { ... }}
```

The key set must be exact. The state's hash is its content hash. The hash boundary excludes wall-clock time, logging, and viewer settings; records simply never contain such fields.

**`StateStore`** maps hash to canonical text. Its methods:

| Method | Behavior |
|---|---|
| `put(record)` | Validates the record and returns its hash |
| `get(h)` | Returns a fresh deep copy |
| `validate_chain(h)` | Re-hashes every ancestor; detects missing and cyclic references; returns the ordered closure |

Callers never receive retained objects.

# 5. Registry and recorded attempts (`glab.core.registry`, `glab.core.runfile`)

**`ActionSpec(name, version, accepts, params, revision, fn)`:**
- `version` is a positive `int`, not a `bool`.
- `accepts` is a state kind, or `None` for a source action.
- `params` maps each name to a `Param`.
- **The callback signature is `fn(input_copy | None, params_copy, seed) -> StateDraft(kind, payload, representation)`.** The `seed` is `None` or an `int`.

**`CheckerSpec(name, version, accepts, params, revision, fn, uses_context=False)`** takes a callback `fn(subject_copy, params_copy) -> list[Claim]`. Here `Claim(predicate, outcome, method, numeric_domain, coverage="all", tolerances=None, receipt=None)`.

**Contextual checkers (Stage 2 repair D01).** A checker registered with `uses_context=True` (a real `bool`) is called as `fn(subject_copy, params_copy, context)`. Nothing is guessed from the callback's signature.
- `context` is a `DependencyContext`. It snapshots the canonical texts of exactly the subject's validated ancestor closure, and holds no store, registry, or generator.
  - `get(h)` returns a fresh copy for a hash in the closure, and raises `ContextError` for any other hash.
  - `parent()` returns the immediate parent or `None`.
  - `dependencies` returns the closure.
- The closure equals the check attempt's and each evidence record's `dependencies`, so integrity checks, reuse validation (a changed ancestor makes the evidence stale), and replay already bind it. The history format is unchanged.
- A `ContextError`, like any checker exception, makes the attempt `failed`. It never yields a predicate outcome.

The `Param` types are `Param.int()`, `Param.str()`, `Param.exact()`, and `Param.enum(values)`. Extra, missing, or mistyped parameters are rejected. Callbacks never see the store. JSON selects only a registered `(name, version)`. Nothing is imported, evaluated, or executed from a file. Registered callbacks are trusted local code, not a sandbox.

**One ordered history.** `Run.history` holds action attempts and check attempts in a single sequence; `seq` is the index in `history`. `Run.actions` and `Run.checks` are filtered copies of it.

**Input capture (R01).** Each input (name, version, params, input or subject, seed) is stored as a detached JSON copy **with its actual type**, so a rejected `version=True` is stored as `true`. A value JSON cannot represent is stored as the inert description `{"python_type": "<name>"}`, and the field name is added to `unrepresentable`. Such an attempt is always rejected. Replay reports it as `not_replayable`. A stored `repr` is never evaluated.

**Action attempt record, `glab.action/2`:** `seq`, `action`, `version`, `params`, `input`, `output`, `status`, `implementation_revision`, `seed`, `failure`, `unrepresentable`.

| `status` | Meaning |
|---|---|
| `rejected` | Nothing executed. Cause: an unknown name or version, bad parameters, unrepresentable inputs, an input state that is missing, invalid, or of the wrong kind, or a bad seed. |
| `failed` | The callback raised, or returned an invalid draft |
| `succeeded` | A state was created |

`failure` is `{stage, type, message}`, with `stage` equal to `validation` or `execution`. `Run.apply` always appends the attempt, and returns a copy of it without raising.

**Check attempt record, `glab.check/1` (R02):** `seq`, `checker`, `version`, `params`, `subject`, `dependencies`, `status`, `checker_revision`, `evidence` (the IDs this attempt produced, in order), `failure`, `unrepresentable`.

| `status` | Meaning | Returned or raised to the caller |
|---|---|---|
| `rejected` | Validation failed | raises `RegistryError` or `RecordError` |
| `failed` | The callback raised; returned output that is not a list of `Claim`; or returned a `formal_proof` claim or non-JSON content | re-raises the original exception, `RegistryError`, or `EvidenceError` |
| `completed` | The check ran, possibly with zero claims | returns copies of the new evidence |

The attempt is appended **before** anything is raised. A failed attempt is an execution failure of that attempt, not a predicate outcome. Earlier evidence is never changed.

# 6. Evidence (`glab.core.evidence`)

**Evidence record, `glab.evidence/2`:**

| Field | Contents |
|---|---|
| `seq` | position in `run.evidence` |
| `attempt` | the `seq` of the producing check attempt |
| `claim` | the predicate |
| `subject` | the subject state hash |
| `dependencies` | the subject's validated ancestor closure, in order |
| `outcome` | `pass`, `fail`, `unknown`, or `not_run` |
| `method` | `numerical_diagnostic`, `exact_computation`, `rigorous_enclosure`, or `formal_proof` |
| `numeric_domain` | the numeric domain used |
| `representation` | the subject's representation |
| `checker`, `checker_version`, `checker_revision` | the checker's identity |
| `params` | the checker's parameters |
| **`tolerances`** | the claim's tolerance settings, or `null` |
| `coverage` | an exact token such as `"all"` or `"sample:one"` |
| `receipt` | details |

The evidence ID is `content_hash(record)`.

**Capture boundary (R03).** `make_evidence(*, seq, attempt, claim, subject, dependencies, representation, checker, checker_version, checker_revision, params)` detaches the entire record through a canonical JSON round trip. That includes nested receipts and tolerances, so no object held by a checker can reach retained history. `make_evidence` rejects `formal_proof`, because no formal verifier is supported.

**Reuse validation.** `validate_evidence(record, store, registry, *, expected_tolerances=UNSET, reproduced=frozenset())` returns `{id, status, reason, reproduced}`.

| `status` | Condition |
|---|---|
| `current` | subject and dependencies re-validate, the checker revision matches, and the tolerances match when `expected_tolerances` is supplied |
| `stale_subject` | the subject or an ancestor is missing or changed, the dependency closure differs, or the representation differs |
| `checker_mismatch` | the checker is unregistered, or its revision differs |
| `policy_mismatch` | the tolerances differ from `expected_tolerances` |
| `unsupported_method` | the record claims `formal_proof` |

**`Requirement(claim, subject, methods=None, representations=None, params=None, coverage="all")` (R04).**
- The requirement names one exact subject hash. Evidence never transfers between states.
- `coverage` is an exact token that must equal the evidence's `coverage`. The default `"all"` is deliberately conservative. `coverage=None` accepts any recorded coverage, and the caller then owns that choice. Nothing is inferred from predicate names or prose.

**`summarize(evidence, requirements, store, registry, *, reproduced=frozenset(), expected_tolerances=UNSET)`** takes, for each requirement, all matching records (same claim, same subject, and the same `params` if the requirement specifies them). It keeps the `current` ones and decides:

| Situation | Requirement result |
|---|---|
| No matching records | `not_run` |
| None of them current | `unknown` |
| Current records disagree on the outcome, whatever their coverage | `unknown` (conflict) |
| No current record carries the required coverage | `unknown` |
| A covering record's method or representation is outside what the requirement accepts | `unknown` |
| Otherwise | the agreed outcome |

The overall result is the worst requirement result, ordered `fail > unknown > not_run > pass`. **`verified` is true only if the overall result is `pass` and every covering record was produced or replayed in this process.**

There is no tolerance-based pass for an unresolved contact (amendment A).

# 7. Run file, integrity, and replay (`glab.core.runfile`)

**Run file, `glab.run/2`:** `schema`, `environment`, `identities`, `states`, `history`, `evidence`, and `run_digest`.
- `identities` holds the action and checker revisions that appear in the history.
- `run_digest` is the content hash of every other field, so it covers ordered history, parameters, evidence, references, identities, and the environment.
- `Run.save(path)` writes canonical LF text and returns the digest.

**`load_run(path, expected_digest=None) -> LoadedRun`** validates the file **structurally and chronologically, without executing anything and without a registry**:

1. **Parsing.** Duplicate keys and nonfinite values are rejected. The exact key set and the `glab.run/2` schema are required. `glab.run/1` is rejected with an explanation, because it has no check-attempt history and none will be invented.
2. **States.** Every state re-hashes to its key, and every chain resolves, which rejects cyclic or dangling references.
3. **History, in order (R05).**
   - Each `seq` must be the integer index, not a bool.
   - An executed action (`succeeded` or `failed`) needs:
     - a string name and a positive integer version
     - object params with nothing unrepresentable
     - an integer or null seed and a string revision
     - an input already produced earlier in this history
   - A succeeded action's output must be stored, and its `parent` must equal the input. The output then becomes available.
   - Rejected actions and checks may name missing or invalid inputs, because the rejection records exactly that.
   - An executed check needs its subject already available, and its dependencies must equal the stored chain.
   - A completed check's evidence IDs must be exactly the evidence records that name it, and they must match the check's subject, dependencies, checker, version, revision, and params.
   - A failed or rejected check has no evidence.
4. **Evidence records.** Structure, `seq` order, subject existence, and representation are checked. A record whose `attempt` is not a completed check is rejected.
5. **Orphans.** Every stored state must be the output of some succeeded action.
6. **Digest.** The digest must match. `identities` must agree with the history. If `expected_digest` is supplied, it must match (`anchor = "matched"`); otherwise the load is `unanchored`.

**What loading does not check.** Action and checker existence, parameter types, and state kinds need registered code. `replay` checks them by re-executing.

**`LoadedRun`** holds one validated canonical text snapshot. `record` and `store` are properties that return fresh copies built from that same text, so mutating them cannot change the snapshot (R03). `authenticated` is always false. Internal consistency is not authorship. Only an independently retained digest detects a wholesale rewrite that recomputes every hash.

**`replay(loaded, registry)`:**
- It re-checks the snapshot digest, then walks `history` in order:
  - an attempt with unrepresentable inputs is `not_replayable`
  - an entry whose input came from a non-reproduced output is `not_run`
  - an entry whose registered revision differs, or is missing, is `not_run`
  - every other entry is re-executed through `Run.apply` or `Run.check`, and its **complete record** is compared, including failure messages. Check attempts are compared with their evidence contents, excluding only the sequence and attempt numbers.
- `outcome = "reproduced"` requires every entry to be reproduced, the environment to match, and `run_digest_reproduced` to be true.
- Otherwise the outcome is `mismatch`, `not_run`, or `environment_mismatch`. If every entry matched but the digest did not, the outcome is `mismatch`.
- `partial_comparison` counts entries only and is not a whole-run claim.
- The report includes the fresh `run`, so callers can summarize reproduced evidence.

**Environment:** Python version and implementation, platform string, core revision (the SHA-256 of the LF-normalized core sources), and the replay guarantee.

# 8. API names (as implemented)

- **`glab.core.numbers`:** `parse_exact`, `format_exact`, `ExactInputError`.
- **`glab.core.records`:** `canonical_json`, `content_hash`, `strict_loads`, `is_hash`, `validate_state`, `StateStore` (`put`, `get`, `validate_chain`, `from_mapping`, `as_mapping`, `hashes`), `RecordError`.
- **`glab.core.registry`:** `Param`, `ActionSpec`, `CheckerSpec`, `StateDraft`, `Claim`, `Registry` (`register_action`, `register_checker`, `action`, `checker`, `identities`), `source_revision(root, *relative_paths)`, `RegistryError`.
- **`glab.core.evidence`:** `OUTCOMES`, `METHODS`, `SUPPORTED_METHODS`, `make_evidence`, `evidence_id`, `check_evidence_structure`, `validate_evidence`, `Requirement`, `summarize`, `EvidenceError`, `UNSET`.
- **`glab.core.runfile`:**
  - `Run` (`apply`, `check`, `validate`, `summarize`, `history`, `actions`, `checks`, `evidence`, `reproduced`, `to_record`, `digest`, `save`, `get`)
  - `load_run(path, expected_digest=None)`, `LoadedRun`, `replay(loaded, registry)`
  - `environment`, `core_revision`, `RunIntegrityError`
  - `DependencyContext(store, subject)` (`get`, `parent`, `subject`, `dependencies`) and `ContextError`, both added in the Stage 2 repair (D01)

# 9. Known limits

- **Replay is environment-bound.** Replay on another machine or Python version reports `environment_mismatch`.
- **Hashes give integrity, not authorship.**
- **`glab.core.numbers` could shadow the standard library's `numbers`** module if `glab/core` itself were placed on `sys.path`. Never do that.
- **Coverage tokens are compared literally.** There is no implication between scopes, for example "all" implying "sample".
- **No geometry semantics exist yet.** The deferred unsafe-seam specimen (POLAR-WINDOW §1) is parked until geometry work is authorized.

# Revision note

This document was first written at `commit-22` (Stage 1). It was reconciled with the executable API during the Stage 1 repair (see `STAGE-1-REPAIR-PLAN.md`). The Stage 1 version of this text differed from the code in five places:

- It described the callback without its `seed` argument.
- It said `tolerance_policy` where the field is `tolerances`.
- It said `expected_policy` where the argument is `expected_tolerances`.
- It said `representation` where the argument is `representations`.
- It gave `load_run` a `registry` argument it does not take.

It also advertised kind checks the loader cannot perform. The earlier version remains in Git history.
