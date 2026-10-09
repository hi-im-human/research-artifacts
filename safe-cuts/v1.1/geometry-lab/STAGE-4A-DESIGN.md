---
title: Geometry Lab Stage 4A design - exact-input enclosure of the ideal development
author: Claude Code session (Claude Opus 5.5), outside the project's agent team
date: 2026-09-29
status: written before the probe; design and isolated probe only; maintained Stage 4 integration held
dg-publish: false
---

> **Export note (edition 1.1).** This is a sanitized copy made for the research export. Private repository locations, research-folder locations, branch names and commit identifiers were replaced by placeholders and `commit-NN` labels, and the author line names no private project. The mathematical text is unchanged. Git blob and SHA-256 identifiers pinned by the evidence policy refer to these export copies; the historical originals and their identifiers are retained privately.

# Stage 4A design

## 0. The question and the shape of the answer

System's question (`SYSTEM-TO-CLAUDE-STAGE-4A.md`, authorization `commit-53`): *can exact-input interval arithmetic plus justified shared-hinge identities resolve currently uncertain contacts without misrepresenting a rounded placement as the exact construction?*

The design answers in three parts:

1. **Name the subject.** There is a mathematical object, the *ideal trimmed development* `D`, defined from exact rational data by a recursion with no floating-point numbers and no angles (§2). It is not the Stage 3 float64 placement, and it is not an enclosure. It is what the enclosures enclose.
2. **Decide retained neighbours exactly.** Two faces that share a retained hinge are decided by an **exact rational 3D side test**, transferred to the plane by an elementary lemma about orientation-preserving isometries (§4). No rounding, box intersection, identifier coincidence or tolerance is involved.
3. **Enclose everything else.** All other pairs are decided on **outward rational-interval enclosures** of `D`, which start from the exact material. The only inexact operation is the square root, enclosed by verified integer square roots (§5). The possible outcomes are:
   - a certified separating axis: `pass`, for `D` only
   - a certified interior witness: `fail`
   - anything else: `unknown`

Nothing in this design reads the Stage 3 float maps as input. The old float-state evidence keeps its meaning and its `unknown`s (§3.3).

## 1. Inputs read

- **The handoff:** `<geometry-lab-project>/SYSTEM-TO-CLAUDE-STAGE-4A.md` at `origin/main`.
- **The acceptance review:** `reviews/stage3-repair-commit-52/REVIEW.md` and `RESULTS.json`, the test file, and its receipts.
- **Worker branch:** `<private-branch>` at the reviewed head `commit-52`. It had no later commits and a clean worktree.
- **My Stage 3 repair return,** §"Stage 4 proposal", as the starting point.
- **Material conventions,** from `TWO-RIM-SCHEMA.md`:
  - each lateral face `F_t` has the ring `[L_t, U_t, U_{t+1}, L_{t+1}]`, with 3 or 4 vertices
  - the ring is **counterclockwise about the outward normal**
  - `plane = (a, b, c, d)` is made of primitive integers, with outward normal `(a, b, c)` and `a x + b y + c z <= d` on the body
  - `L` and `U` are the lower (`z = 0`) and upper (`z = h`) endpoints of a hinge
- **Historical exact verifier,** read only, provenance checked:
  - `beveled_source_certificate.py`, blob `2471d2d1` (the test-side `.py.txt` copy)
  - its dependencies at `commit-11`, under `<historical-folder>/verification/packet/code/` (not included): `rational_intervals.py` (`a8f9a268`) and `mixed_fixture_certificate.py` (`d7cc4977`)

  Its method is assessed in §6.4. It is prior art, not an oracle, and it is not executed in 4A.
- **Backend documentation,** read on 2026-09-29:
  - the mpmath 1.3.0 "Contexts" page, section "Arbitrary-precision interval arithmetic (iv)"
  - the FLINT documentation "arb.h – real numbers", 3.7.0-dev build

## 2. The mathematical subject

### 2.1 Exact inputs

The subject is fixed by the following. All data are exact rationals, read from Stage 2/3 **states in a Run**, never retyped.

| Field | Source |
|---|---|
| `source_state`, `material_state`, `material_identity` | Stage 2 states; material `identity` hash |
| `cut_state`, `seam = E_k`, chain `F_k, F_{k+1}, …, F_{k−1}` | Stage 3 `two_rim.cut/1` (exact) |
| `delta` | exact rational, `0 < δ < 1/2` |
| `orientation` | `outward`: each face map is orientation-preserving with respect to that face's outward normal |
| `normalization` | `N0`: the first chain face's entry-hinge low trim point goes to `(0, 0)`, and that hinge points along `+x` |

Notation:
- **Hinge vectors:** `e_t = U_t − L_t`. The outward normal of `F_t` is `n_t`.
- **Trim points (the normalized trim):** `P_t^lo = L_t + δ e_t` and `P_t^hi = L_t + (1−δ) e_t`. These are the Stage 3 `E_t@lo` and `E_t@hi`.
- **Trimmed face:** `T_t = conv{P_t^lo, P_t^hi, P_{t+1}^hi, P_{t+1}^lo}`, with vertices listed in this cyclic order, the same order as the ring.

### 2.2 Two elementary lemmas

**L1 (orientation and side transfer).** Let `Π` be a plane with unit normal `n̂`, direction space `Π₀ = {v : v·n̂ = 0}`, and a unit vector `ê ∈ Π₀`. Let `H = [ê ; n̂ × ê]` (a 2×3 matrix) and `R ∈ SO(2)`, and set `A = R H`. Then:
- `A` restricted to `Π₀` is a linear isometry onto `R²`;
- for all `a, b ∈ Π₀`, `cross2(A a, A b) = (a × b) · n̂`, where `cross2(x, y) = x₁y₂ − x₂y₁`.

*Proof.* The vectors `ê` and `n̂ × ê` form an orthonormal basis of `Π₀`, and `H` sends it to `(1,0)` and `(0,1)`. By the Binet–Cauchy identity,

`cross2(Ha, Hb) = (ê·a)((n̂×ê)·b) − ((n̂×ê)·a)(ê·b) = (a×b)·(ê × (n̂×ê)) = (a×b)·n̂`,

because `ê·ê = 1` and `ê·n̂ = 0`. Finally, `det R = 1`. ∎

**L2 (existence and uniqueness).** Let `Π` have orientation `n̂`, let `L ≠ U` be points of `Π`, and let `p, q ∈ R²` satisfy `|q − p| = |U − L|`. Then exactly one isometry `Φ : Π → R²` preserves orientation with respect to `n̂` and satisfies `Φ(L) = p` and `Φ(U) = q`.

*Proof.*
- **Existence:** take `Φ(x) = p + R H (x − L)`, with `ê = (U−L)/|U−L|` and `R` the rotation taking `(1,0)` to `(q−p)/|q−p|`. By L1 it preserves orientation.
- **Uniqueness:** two such maps differ by an orientation-preserving isometry of `R²` that fixes two distinct points, which is the identity. ∎

### 2.3 Definition of the ideal trimmed development `D`

The faces are placed as follows:

- **First face.** `Φ_k` is the orientation-preserving isometry of `plane(F_k)` that sends `P_k^lo` to `(0,0)` and `P_k^hi` to `((1−2δ)|e_k|, 0)`. This is L2 applied to the pair `(P_k^lo, P_k^hi)`.
- **Each next face.** For each chain step `t → t+1` with `t+1 ≠ k`, where `E_{t+1}` is a **retained** hinge, `Φ_{t+1}` is the orientation-preserving isometry of `plane(F_{t+1})` with
  - `Φ_{t+1}(L_{t+1}) = Φ_t(L_{t+1})`
  - `Φ_{t+1}(U_{t+1}) = Φ_t(U_{t+1})`

  This is well defined by L2, because `L_{t+1}` and `U_{t+1}` lie in both planes and `Φ_t` preserves their distance.
- **Result.** `D_t = Φ_t(T_t)`. The development `D` is the family `(Φ_t, D_t)`.
- **The seam is open.** Nothing requires `Φ_{k−1}` to agree with `Φ_k` on `E_k`.

**The classification question** for a pair `t ≠ t'` is whether `int D_t ∩ int D_{t'} = ∅`. Boundary contact is allowed.

**Invariance.** The answer does not depend on `N0`: any other normalization differs by a global isometry of `R²`. It also does not depend on the orientation convention, since a global mirror reflects the whole picture. The orientation and normalization still matter for explicit coordinates, such as witness points, so they are part of the subject.

### 2.4 Three objects that must not be confused

| Object | What it is | Where it lives |
|---|---|---|
| `D` | the definition above, in exact real arithmetic; its coordinates involve square roots | nowhere as numbers; only as a definition plus exact inputs |
| enclosure `B(D)` | rational intervals certified to contain `D`'s vertex images | the Stage 4A probe (`engine/probes/stage4a/`) |
| Stage 3 float placement | float64 maps from the ported generator; its own subject (`two_rim.development` or `two_rim.trimmed_development` state hash) | the maintained engine, with `numerical_diagnostic` evidence |

A certificate about `D` says nothing about a float state, and float evidence says nothing about `D`. §3.3 states the firewall.

### 2.5 Relation to the manuscript's chart development (L4): a remaining obligation

The Stage 3 generator ports DRAFT-02 §4:
- chart `ψ_i = [ν_i ; −ξ_i](x − M_i)`
- turn `q_i = φ(ν_i) − φ(ν_{i−1})`
- transition `T_i(z) = R(q_{i+1}) z + (ℓ_i, 0)`

**Claim L4.** In exact real arithmetic this chart development is the orientation-preserving hinge-agreement development `D`, up to a global orientation-preserving isometry of `R²`.

**Derivation sketch.**
1. The midpoints `M_i` are at height `h/2`, so `ν_i` is horizontal. `ξ_i` has a positive `z`-component, because `G_i` does. Every hinge `G_{i+1}` has `z`-extent `h > 0`, so its component along `ξ_i` is positive.
2. Hence `ψ_i(G_{i+1}) = |G|(cos φ⁻, −sin φ⁻)` and `ψ_{i+1}(G_{i+1}) = |G|(cos φ⁺, −sin φ⁺)`, with both angles in `(0, π)`. The rotation between them is `φ⁺ − φ⁻ = q_{i+1}`, and `T_i(0) = (ℓ_i, 0) = ψ_i(M_{i+1})`. So consecutive charts agree on the whole retained hinge line.
3. The orientation sign of `ψ_i` with respect to `n_i` is the sign of `−(ν_i × ξ_i)·n_i`. That is an exact rational sign after clearing the square-root denominators.

**Status.**
- The derivation is **written here and not machine-checked**.
- Its per-instance hypotheses (midpoint heights, positive hinge `z`-extents, uniform chart orientation signs) are exact checks that the probe may record.
- L4 is **not used by any probe claim**. The probe's claims are about `D` as defined in §2.3.
- L4 matters only for saying that `D` is the manuscript's development `W`. Until it is reviewed or formalized, that identification stays a **remaining obligation** (§9).

## 3. Source correspondence and the evidence firewall

### 3.1 The chain of identity carried into every probe result

A probe result names all of the following:
- `source_state`, `material_state` with its material `identity`, and `cut_state`
- the evidence IDs and outcomes of `two_rim.check.source` v2 and `two_rim.check.material` v2 (including `matches_parent_source`), and of `two_rim.check.cut` v1, each produced by those registered checkers in the same Run
- the result of `Run.validate` for each of those records at the time of use

The exact data used by `D` is read from the **cut state's parent material** through `run.get`. It is also compared field by field with the cut's embedded material copy.

**No certificate is issued without complete prerequisites.** If any prerequisite is missing, non-current or not `pass`, the result is labeled `not_source_linked` and gives no source-linked verdict. Copied metadata and passing arithmetic are not correspondence.

### 3.2 The subject identifier

`ideal_subject = content_hash({"kind": "ideal_trimmed_development", "definition": "stage4a.ideal_development/1", "material_state", "material_identity", "source_state", "cut_state", "seam", "delta", "orientation", "normalization"})`

This uses the core's `content_hash`, called read-only. It is not a Stage 3 state hash.

### 3.3 The firewall

- **No inputs from float states.** The probe never reads a `two_rim.development` or `two_rim.trimmed_development` payload as input to `D`. Float values are used only to *propose* candidate axes and witness points. Every proposal is re-certified exactly or on intervals, and a failed proposal is just `unknown`.
- **No transfer to float states.** A probe certificate never applies to a float state. The probe has a predicate `applies_to(certificate, subject)` that accepts only the identical ideal-subject spec. A control (§7, C7) shows that it refuses both the unaltered and a deliberately altered float placement.
- **Old evidence keeps its meaning.** Old `numerical_diagnostic` evidence is not changed, re-labeled or summarized with probe results. The Stage 3 `unknown`s remain `unknown` for the Stage 3 subjects.

## 4. Shared-hinge decisions: exact, with the derivation

### Theorem S

Take consecutive chain faces `F_t` and `F_{t+1}` that share the retained hinge `E = E_{t+1}` (`t+1 ≠ k`), with `L = L_{t+1}`, `U = U_{t+1}` and `e = U − L`. Suppose these exact checks hold:

| Check | Condition |
|---|---|
| S1 (identity) | In the material, `F_t.exit = E = F_{t+1}.entry`. The ring of `F_t` contains `L` and `U` as vertex IDs **and** with the same exact coordinates as the ring of `F_{t+1}`. `E` is not the seam, and the two faces are consecutive in the cut's `face_order`. |
| S2 | `L ≠ U`, and both normals `n_t, n_{t+1} ≠ 0`. |
| S3 (planarity) | Every ring vertex of `F_t` satisfies `plane(F_t)` with equality, and likewise for `F_{t+1}`. So `e · n_t = e · n_{t+1} = 0`. |
| S4 (sides) | With `σ_t(w) = (e × (w − L)) · n_t` for the vertices `w` of `T_t`, and `σ_{t+1}(w) = (e × (w − L)) · n_{t+1}` for those of `T_{t+1}`: one face has all `σ ≤ 0`, the other all `σ ≥ 0`, and each face has at least one strict value. |

Then `int D_t ∩ int D_{t+1} = ∅`.

*Proof.*
1. By definition `Φ_t(L) = Φ_{t+1}(L) =: p` and `Φ_t(U) = Φ_{t+1}(U) =: q`. Both maps are affine, orientation-preserving isometries of their planes (§2.3), with linear parts `A_t` and `A_{t+1}`.
2. For any `w` in `plane(F_t)`, L1 gives `cross2(q − p, Φ_t(w) − p) = cross2(A_t e, A_t(w − L)) = (e × (w − L))·n̂_t = σ_t(w)/|n_t|`.
3. For `F_{t+1}` the same holds with `n_{t+1}`, measured against **the same** directed planar line `p → q`, by agreement.
4. So the two images lie in opposite closed half-planes of one line. A set in a closed half-plane has its interior in the open half-plane, and the two open half-planes are disjoint. ∎

### What this does and does not use

- **Exact, machine-computed:** S1–S4, as rational arithmetic on the material.
- **By definition of `D`, justified by L2:** agreement of `Φ_t` and `Φ_{t+1}` on `E`, and orientation preservation.
- **Written derivation, not machine-checked:** L1, L2 and Theorem S itself (§9, O1).
- **Not used:**
  - numerical values of `Φ`
  - intervals, or boxes that merely intersect
  - identifier coincidence without coordinate equality
  - any tolerance or snapping
  - skipping the pair

  The pair is decided, and the row records its `σ` values.
- **Expected outcome.** Material rings are counterclockwise about outward normals, so for valid materials S4 always gives opposite signs:
  - `F_t` traverses its exit hinge as `U → L`, so it lies to the right of `L → U`
  - `F_{t+1}` traverses its entry hinge as `L → U`, so it lies to the left

  The exact computation checks this rather than assuming it.
- **When S1–S4 fail.** The row is `unknown`, with reason `shared_hinge_preconditions_failed`, and the pair is then tried on intervals like any other pair. Theorem S never outputs `fail`.

**Scope.** Theorem S decides only pairs that share a retained hinge. In the trimmed domain (δ > 0), the only material points two faces share are on their common retained hinge. The seam copies are not shared: the first and last chain faces are an ordinary pair.

The untrimmed domain adds pairs that share only a glued vertex. Those need a tangent-cone or angle-sum argument and are **out of 4A scope**.

## 5. Enclosures of `D` for all other pairs

### 5.1 Closed formulas (entry-hinge frames)

For face `t`:

- `H_t v = ( (e_t·v)/|e_t| , ((n_t × e_t)·v)/(|n_t||e_t|) )`. This is `[ê_t ; n̂_t × ê_t] v`, orientation-preserving by L1.
- `Φ_t(x) = O_t + Rot(C_t, S_t) · H_t (x − L_t)`, where `Rot(c, s) = [[c, −s], [s, c]]`.
- **Start (first chain face):** `(C_k, S_k) = (1, 0)` and `O_k = (−δ|e_k|, 0)`. This gives `Φ_k(P_k^lo) = 0` and `Φ_k(P_k^hi) = ((1−2δ)|e_k|, 0)`.
- **Step `t → t+1`:**
  - `c_t = (e_t·e_{t+1}) / (|e_t||e_{t+1}|)`
  - `s_t = (n_t·(e_t × e_{t+1})) / (|n_t||e_t||e_{t+1}|)`
  - `(C_{t+1}, S_{t+1}) = (C_t c_t − S_t s_t, S_t c_t + C_t s_t)`
  - `O_{t+1} = Φ_t(L_{t+1})`

**Why the step is right.** `e_{t+1}` lies in `plane(F_t)`, so `H_t e_{t+1} = |e_{t+1}|(c_t, s_t)` with `c_t² + s_t² = 1`. Also `H_{t+1} e_{t+1} = (|e_{t+1}|, 0)`, so this choice of rotation is the unique map in L2 that agrees on `E_{t+1}`.

Every coordinate is an **exact rational numerator times the reciprocal of the square root of an exact positive rational**. The only radicands are `e_t·e_t` and `(n_t·n_t)(e_t·e_t)`.

### 5.2 Operations and outward containment

Numbers are closed intervals `[lo, hi]` with `Fraction` endpoints, `lo ≤ hi`.

| Operation | Rule | Containment argument | Failure record |
|---|---|---|---|
| exact input `q` | `[q, q]` | trivial | none |
| `+`, `−` | endpoint arithmetic in exact `Fraction` | exact interval operation, no rounding | none |
| `×` | min/max of the four endpoint products, exact | exact interval product | none |
| `1/x` | `[1/hi, 1/lo]` | exact, when `0 ∉ [lo, hi]` | `zero_denominator` if `lo ≤ 0 ≤ hi` |
| `√a`, `a = N/D > 0` exact | `r = isqrt(N·D·4^P)`, `lo = r/(D·2^P)`, `hi = (r+1)/(D·2^P)`, or `hi = lo` when `r² = N·D·4^P` | integer floor square root is exact; the certificate records and checks `lo² ≤ a ≤ hi²` in exact arithmetic | `negative_radicand`, `sqrt_lower_bound_zero` (division impossible at this precision) |
| outward rounding at `P` bits | `lo ↦ ⌊lo·2^P⌋/2^P`, `hi ↦ ⌈hi·2^P⌉/2^P` | only widens | none |

**Remarks.**
- Normalization, rotation composition and affine composition are finite compositions of these rows. Enclosure follows by inclusion monotonicity.
- **Higher precision only narrows the intervals.** The proof of containment comes from the rules, never from precision.
- **Sign of an interval** has four outcomes: `positive` (`lo > 0`), `negative` (`hi < 0`), `zero` (`lo = hi = 0`, exact), and `undecided` otherwise. `Undecided` is never read as zero or as a sign.

### 5.3 Precision schedule and budget

- **Schedule.** Each target is tried at `P ∈ (16, 32, 64, 128, 256, 512)` and stops at the first decision. Every attempt is recorded, including the undecided ones.
- **Exhaustion.** If the schedule is exhausted, the result is `unknown`, reason `budget_exhausted`.
- **Errors.** An arithmetic error at one precision is recorded and the next precision is tried. If errors persist at 512 bits, the result is `unknown`, reason `error:<kind>`.
- **Unsupported inputs** give `unknown`, reason `unsupported_input:<detail>`:
  - a degenerate hinge
  - a non-planar ring
  - a non-convex or wrongly oriented trimmed ring
  - a material or cut that fails its prerequisite
- **No error is ever converted into `pass` or `fail`.**

### 5.4 Certificates for a pair that shares no retained hinge

Let `V_t` be the interval boxes of `Φ_t` applied to the four vertices of `T_t`.

- **Separation → `pass` (for `D`).** Choose a rational axis `d` (exact). If `max_{v ∈ V_t} sup(d·v) ≤ min_{v' ∈ V_{t'}} inf(d·v')`, or the symmetric inequality, holds, then `D_t` and `D_{t'}` lie in opposite closed half-planes. Their interiors are disjoint; boundary contact is allowed, and equality is accepted.

  This uses only `D_t = conv(Φ_t(vertices))`, which is true because `Φ_t` is affine and `T_t` is defined as a convex hull. The recorded gap lower bound is `min inf − max sup`.
- **Interior witness → `fail`.** Choose a rational point `y` (exact). For each of the two faces:
  - first, exactly: the cyclic vertex list of `T_t` is strictly convex and counterclockwise about `n_t` (every turn `((v_{i+1}−v_i) × (v_{i+2}−v_{i+1}))·n_t > 0`);
  - then, on intervals: every `cross2(v_{i+1} − v_i, y − v_i)` has a positive lower bound.

  By L1 the planar polygon `D_t` is strictly convex and counterclockwise. So `y` is strictly inside both, the interiors meet, and the pair is `fail` for `D`. The recorded margin is the smallest lower bound.
- **Otherwise `unknown`.** The reason is `no_certified_axis_or_witness` at the last precision tried.
- **Candidates are proposals.** Axes come from the edge normals and centroid directions of box midpoints. Witnesses come from float intersections of box midpoints. They are converted to rationals, and their origin has no evidential weight.

### 5.5 Scoped outcomes

| Outcome | Meaning | Scope |
|---|---|---|
| `pass` via Theorem S | retained-neighbour pair has disjoint interiors | `D` for this `ideal_subject`; conditional on O1 (§9) |
| `pass` via axis | certified separating axis | `D` only; conditional on O1 and O3 |
| `fail` via witness | certified common interior point | `D` only; conditional on O1 and O3 |
| `unknown` | nothing certified within budget, or an error | nothing is claimed |

A seam of `D` is `pass` only if all pairs are `pass`, `fail` if any pair is `fail`, and `unknown` otherwise.

## 6. Trusted base, re-checking and backends

### 6.1 Trusted arithmetic base (recommended)

- CPython 3.11 `int` (arbitrary precision), `fractions.Fraction` and `math.isqrt`, plus about 150 lines of probe interval code.
- There is no floating-point step in any decision. Floats are proposals only.
- No third-party code is used in the decision path.

### 6.2 How another checker inspects a result

Every certificate records:
- the exact inputs, by state hash plus the coordinates used
- each square-root enclosure (`radicand`, `lo`, `hi`, exact check of `lo² ≤ a ≤ hi²`)
- the vertex-image boxes, with exact rational endpoints
- the axis `d` and the two bounds, or the witness `y` and its cross-product lower bounds
- the exact `σ` values for Theorem S rows

An independent checker then:
1. recomputes the exact `σ` values and the convexity and orientation turns;
2. computes **its own** enclosures of `D` by any sound method, at higher precision, and checks **exactly** that its boxes lie inside the recorded boxes. Its boxes contain `D`, so the recorded boxes are then confirmed to contain `D`;
3. re-evaluates the recorded axis and witness inequalities exactly, on the recorded boxes.

The probe demonstrates step 2 with an independent implementation (§6.2.1).

**6.2.1 The probe's independent re-checker.**
- It is a separate module that imports neither the probe nor `glab`.
- It uses a different construction: the historical style of frame unfolding, with in-plane Gram–Schmidt frames, and it fixes each side by the exact `σ` sign.
- It uses a different arithmetic library: mpmath `iv`.
- It runs in a throwaway environment, and it only needs to confirm containment and re-check the recorded inequalities.

### 6.3 Backend evaluation against primary documentation

**mpmath 1.3.0 `iv`** (documentation read 2026-09-29):
- The page states the containment guarantee `f(v) ⊆ f̂(v)` for interval versions of functions.
- It also says the support is "still experimental, and many functions do not yet properly support intervals".
- Other documented behaviours matter:
  - Python floats are converted exactly as floats, so `iv.mpf(0.1)` is not one tenth
  - `==` compares endpoints
  - ordering comparisons are three-valued
- **Use:** only for `+ − × ÷` and `sqrt`, in the independent re-checker. It is not part of the trusted base.
- **Environment:**
  - mpmath 1.3.0 is **already present** on this machine, in the Python 3.11 user site-packages, as a SymPy dependency
  - it will be copied, with no network access, into a throwaway venv outside the repository and outside the maintained `.venv`
  - it is pinned by version and by checking each copied file against its installed `RECORD` hash

**FLINT/Arb `arb_t`** (documentation read 2026-09-29, 3.7.0-dev build):
- Ball arithmetic whose outputs contain the exact result for any points of the input balls, and rigorous propagation.
- Caveats noted in the documentation:
  - "absent any bugs" appears in its convergence remark
  - `arb_sqrtpos` silently discards the negative part of an input ball
  - it is a compiled dependency (python-flint)
- **Not installed and not executed** in 4A. It would be worth considering only if Stage 4B needed far more speed than exact rationals give; the probe measures this (§7).

### 6.4 The historical verifier as prior art

The historical verifier (`beveled_source_certificate.py` with `rational_intervals.py` and `mixed_fixture_certificate.py` at `commit-11`) used essentially this arithmetic: dyadic outward intervals over `Fraction`, square root by `isqrt`, and 256 bits. It unfolded with `iv_unfold`. There is one relevant difference:

- **How it chooses the side.** `iv_unfold` chooses each next panel's side from the interval sign of the previous panel's centre, and `adjacent_opposite` then checks the resulting sign pattern.
- **How this design chooses it.** The side is fixed by orientation preservation in the **definition** of `D`, and it is decided by exact rational 3D `σ` values (Theorem S).
- **Consequence.** Both give the same development for valid materials (§4). The exact route does not depend on an interval sign test, and it states the analytic lemma it relies on.

The probe reuses historical material only as a reference, after classification:
- the eleven-panel coordinates, already mapped (historical hinge `t` = current `E{(t+3) mod 11}`)
- the historical witness points, which live in the same normalization `N0`: the historical frame puts the first panel's low trim point at the origin, the hinge on `+x` and the panel at `+y`, and the same is true of `D`, as §4 shows

Old labels never enter a classifier.

## 7. Probe plan (bounded; `engine/probes/stage4a/`)

**Layout:**
- `ratint.py`: intervals and square roots
- `ideal.py`: the subject, exact checks, Theorem S, enclosure recursion
- `classify.py`: pair decisions and seam totals
- `run_probe.py`: builds the Run states and prerequisite evidence, runs the controls, targets and scan, and writes the receipts
- `recheck_mpmath.py`: independent re-checker
- `tests/`, `receipts/` and `README.md`

Every receipt is labeled **"isolated Stage 4A prototype; not glab evidence; no rigorous_enclosure or formal_proof claim issued"**. Nothing is registered in a glab `Registry`, and nothing is written under `glab/`.

**Specimens:**
- the square prism (square rims, height 3; δ = 1/4 and 1/10000; every radicand a perfect square, so the exact path)
- the eleven-panel source at height 1/10000, δ = 1/10000, on the mapped seams

**Controls, written and executed before the positive targets:**

| Id | Control | Expected |
|---|---|---|
| C1 | interval endpoint and sign cases: exact zero, `[0, x]`, `[−x, 0]`, straddling intervals, mixed-sign products, `x − x` for a wide `x` | four-way sign; never a false sign |
| C2 | zero denominator | `zero_denominator` record; pair `unknown` |
| C3 | square-root bounds: perfect squares, non-squares, large and small radicands, negative and zero radicands | `lo² ≤ a ≤ hi²` checked exactly; errors recorded |
| C4 | low-precision ambiguity: the E9 witness and a separation at `P = 2` or `4` | `unknown` at low `P` (never a false `pass` or `fail`); decided at higher `P` |
| C5 | known overlap versus separation versus exact touching, on synthetic rational squares; a near-touch overlap of 2⁻⁶⁰ | `fail`, `pass`, `pass` (contact allowed), and `unknown` then `fail` as `P` rises |
| C6 | incorrect shared-hinge mapping: a wrong hinge ID; matching IDs with different coordinates; the seam pair (shared in 3D, cut in `D`); an inward normal or swapped `L`/`U`; faces that are not consecutive | Theorem S refuses (`unknown` with the reason); never `pass` from a bad mapping |
| C7 | altered approximate placement: a mutated Stage 3 float trimmed state | the Stage 3 v2 checker still flags the mutation; `applies_to` refuses every float state; the ideal certificate is unchanged and names only `ideal_subject`; the altered placement lies outside the ideal enclosure while the unaltered one lies within about 1e-9 (diagnostic only) |
| C8 | old float64 mutation controls | the inherited suite is rerun unchanged, including the Stage 3 mutation tests |

**Targets (after the controls):**
- **T1.** One retained-neighbour contact in a historically safe seam. On eleven-panel seam E4 (historical cut 1), this is the first retained hinge in chain order whose Stage 3 float row is `near_contact_unresolved`. Decided by Theorem S. The Stage 3 row is used only to *choose* the example.
- **T2.** One robustly separated pair with no shared hinge on E4: the pair with the largest float gap, decided by an interval axis.
- **T3.** The known overlap F10/F7 at current E9, decided by an interval witness that the probe finds itself.
- **Direct scan.** All 55 pairs on all 11 seams, using the same machinery. It is compared with the historical classes **after** classification. The historical witness points are then checked in `D`, as a reference only.
- **Cross-check.** The re-checker (§6.2.1) runs on T1–T3 and the scan.
- **Timing.** Per seam and per precision, recorded as performance limits.

**Firewall and suite.** C7 plus the full inherited suite (411 tests). Collection or import failures are recorded separately from assertion failures.

## 8. Proposed Stage 4B evidence contract (proposal only; not implemented)

- **New exact state** `two_rim.ideal_trimmed_development` (representation `exact`, schema `two_rim.ideal_trim/1`):
  - its parent is the **cut** state, never a float state
  - its payload holds the exact cut copy (the ancestor-copy pattern), `delta`, `orientation`, `normalization` and `definition`
  - it is produced by action `two_rim.ideal.define` v1, which does no numeric work
- **New contextual checker** `two_rim.check.ideal_trimmed_development` v1, with these claims:

  | Claim | Method | Coverage and notes |
  |---|---|---|
  | `two_rim.ideal.record_schema` | `exact_computation` | |
  | `two_rim.ideal.cut_copy_matches_parent` | `exact_computation` | |
  | `two_rim.ideal.trim_faces_convex_counterclockwise` | `exact_computation` | |
  | `two_rim.ideal.retained_neighbours_opposite_sides` | `exact_computation` | coverage `retained_hinges`; receipt holds the `σ` values; declares a dependency on the documented lemmas O1 |
  | `two_rim.ideal.nonadjacent_pairs_certified` | `rigorous_enclosure`, `numeric_domain` `rational_interval` | coverage `pairs_without_retained_hinge`; `Claim.tolerances` = `ENCLOSURE_POLICY` (arithmetic, square-root rule, precision schedule, budget) |
- **Aggregate.** A new search total, `source_linked_ideal_trimmed_obligations`. It combines the source and material bundles, the cut claims, and all ideal claims, and its enclosure claims are held to `ENCLOSURE_POLICY`. The existing float totals are **unchanged and separately named**.
- **Location.** The arithmetic would live in a small standard-library module outside `glab/core` (for example `glab/rigorous/`). The core and action context stay unchanged.

## 9. Assumptions and remaining obligations (kept explicit)

| Id | Statement | Status |
|---|---|---|
| O1 | L1, L2, Theorem S, and the separation and witness lemmas of §5.4 | elementary; derived in this document; **not machine-checked** |
| O2 | L4: `D` equals the manuscript's chart development `W`, up to a global isometry | derivation sketched in §2.5; per-instance hypotheses may be checked exactly; **not established**; not needed for claims about `D` |
| O3 | the probe's interval implementation is correct | controls C1–C5 and the independent mpmath re-checker; **not formally verified** |
| O4 | the material is the source's exact body, with outward normals and counterclockwise rings | Stage 2 v2 checker evidence (exact), carried as a prerequisite |
| O5 | trimmed rings are convex and counterclockwise, and faces are planar | exact checks in the probe, per face |
| O6 | how a verdict on `D` relates to the manuscript's safety statement | outside 4A; agreement with the historical fixture is not a universal proof |

## 10. Boundaries

Not in this pass:
- maintained Stage 4 integration, registry changes, core or action-context changes
- production `rigorous_enclosure` or `formal_proof` claims
- the untrimmed glued-vertex argument, caps, motion, proof-guided seam selection
- Lean, CGAL or FOLD; an interactive viewer; any publishing workflow
- merge, PR, release, deployment, external contact, purchases, scheduler changes, or additional agents

I write only `engine/STAGE-4A-DESIGN.md`, `engine/probes/stage4a/`, and `engine/STAGE-4A-RETURN.md`. Nothing is installed into the maintained `.venv`.
