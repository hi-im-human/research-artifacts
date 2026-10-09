---
title: Ideal trimmed development D - maintained explanatory contract
author: Claude Code session (Claude Opus 5.5), outside the project's agent team
date: 2026-09-29
status: reviewed written dependencies of the maintained ideal lane; NOT machine-checked, NOT Lean results, NOT reviewed by a human mathematician
dg-publish: false
---

> **Export note (edition 1.1).** This is a sanitized copy made for the research export. Private repository locations, research-folder locations, branch names and commit identifiers were replaced by placeholders and `commit-NN` labels, and the author line names no private project. The mathematical text is unchanged. Git blob and SHA-256 identifiers pinned by the evidence policy refer to these export copies; the historical originals and their identifiers are retained privately.

# Ideal trimmed development `D`: maintained explanatory contract

This is the written mathematics that the claims of `two_rim.check.ideal_trimmed_development` v1 depend on. The checker's policy (`IDEAL_POLICY["analytic_dependencies"]`) pins the LF-normalized SHA-256 of this file. Editing it changes the policy, so evidence recorded under the old text stops being current. It is not a proof object; nothing here is checked by a machine.

## 0. Sources, status and identifiers

- **Carried text.** §§1–5 restate `engine/STAGE-4A-DESIGN.md`, Git blob `bb32b132469d0dfe5098f9d0d76ddde5113cc49d`: §2.1–§2.3 (inputs, L1, L2, the definition of `D`), §4 (Theorem S), §5.1 and §5.4 (closed formulas and certificates). The mathematics is unchanged; the wording is condensed.
- **L4.** The correspondence with the manuscript's fixed maps is `engine/probes/stage4a/L4-CORRESPONDENCE.md`, Git blob `e60cb7f1bdcb4589084e7716adc0ca7dd727b012`, kept there unchanged. §6 summarizes it; the note is the text of record.
- **Review status.** System, an AI reviewer, reviewed these derivations (`reviews/stage4a-review`, `reviews/stage4a-repair-commit-62`, `reviews/stage4a-recheck-commit-66`) and accepted them at their listed dependencies. They are **reviewed written dependencies**: not machine-checked, not Lean results, not reviewed by a human mathematician.
- **Definition identifier.** `two_rim.ideal_development/1` is the Stage 4A definition `stage4a.ideal_development/1` (design §2.3), unchanged. Only its name is maintained.
- **Evidence methods.** Claims resting on this text use `exact_computation` or `rigorous_enclosure` with this dependency declared. None is `formal_proof`.

## 1. Exact inputs and notation

A subject is fixed by exact rational data read from Run states, never retyped:
- the material (`two_rim.material/1`) and the cut (`two_rim.cut/1`), with seam `E_k` and chain `F_k, F_{k+1}, …, F_{k−1}` (face indices mod `n`); **chain position** `j` names the face `F_{k+j}`, `0 ≤ j < n`;
- `δ`, an exact rational with `0 < δ < 1/2`;
- the orientation `outward` and the normalization `N0` below.

Material conventions (`TWO-RIM-SCHEMA.md`): each lateral face `F_t` has the ring `[L_t, U_t, U_{t+1}, L_{t+1}]` (3 or 4 vertices), counterclockwise about the outward normal `n_t`; `plane = (a, b, c, d)` with outward normal `(a, b, c)` and `a x + b y + c z ≤ d` on the body; `L` and `U` are a hinge's lower and upper endpoints.

- Hinge vectors `e_t = U_t − L_t`.
- Trim points `P_t^lo = L_t + δ e_t` and `P_t^hi = L_t + (1−δ) e_t`.
- Trimmed face `T_t = conv{P_t^lo, P_t^hi, P_{t+1}^hi, P_{t+1}^lo}`, vertices in this cyclic order.

## 2. Two elementary lemmas

**L1 (orientation and side transfer).** Let `Π` be a plane with unit normal `n̂`, direction space `Π₀ = {v : v·n̂ = 0}`, a unit `ê ∈ Π₀`, `H = [ê ; n̂ × ê]` (2×3) and `R ∈ SO(2)`; set `A = R H`. Then `A` restricted to `Π₀` is a linear isometry onto `R²`, and `cross2(A a, A b) = (a × b)·n̂` for all `a, b ∈ Π₀`, where `cross2(x, y) = x₁y₂ − x₂y₁`.

*Proof.* `ê` and `n̂ × ê` form an orthonormal basis of `Π₀`, which `H` sends to `(1,0)` and `(0,1)`. By Binet–Cauchy, `cross2(Ha, Hb) = (a×b)·(ê × (n̂×ê)) = (a×b)·n̂`, since `ê·ê = 1` and `ê·n̂ = 0`; and `det R = 1`. ∎

**L2 (existence and uniqueness).** Let `Π` have orientation `n̂`, let `L ≠ U` be points of `Π`, and let `p, q ∈ R²` with `|q − p| = |U − L|`. Exactly one isometry `Φ : Π → R²` preserves orientation with respect to `n̂` and has `Φ(L) = p`, `Φ(U) = q`.

*Proof.* Existence: `Φ(x) = p + R H (x − L)` with `ê = (U−L)/|U−L|` and `R` taking `(1,0)` to `(q−p)/|q−p|`; it preserves orientation by L1. Uniqueness: two such maps differ by an orientation-preserving isometry of `R²` fixing two distinct points, which is the identity. ∎

## 3. Definition `two_rim.ideal_development/1` of `D`

- **First face.** `Φ_k` is the orientation-preserving isometry of `plane(F_k)` with `Φ_k(P_k^lo) = (0,0)` and `Φ_k(P_k^hi) = ((1−2δ)|e_k|, 0)` (L2). This is the normalization **N0**: *first chain face's entry-hinge low trim point at (0, 0); that hinge along +x*.
- **Each next face.** For each step `t → t+1` with `t+1 ≠ k` (a **retained** hinge `E_{t+1}`), `Φ_{t+1}` is the orientation-preserving isometry of `plane(F_{t+1})` with `Φ_{t+1}(L_{t+1}) = Φ_t(L_{t+1})` and `Φ_{t+1}(U_{t+1}) = Φ_t(U_{t+1})`; well defined by L2. This is the orientation **outward**: *each face map preserves orientation with respect to that face's outward normal*.
- **The seam is open.** Nothing requires `Φ_{k−1}` to agree with `Φ_k` on `E_k`.
- `D_t = Φ_t(T_t)`; `D` is the family `(Φ_t, D_t)`.

**The question** for a pair `t ≠ t'` is whether `int D_t ∩ int D_{t'} = ∅`; boundary contact is allowed. The answer does not depend on `N0` or on the orientation convention (a global isometry or mirror), but explicit coordinates such as witness points do, so both are part of the subject.

`D` is an exact definition. Its coordinates involve square roots; `representation: exact` on the state means exact inputs and definition, not rational image coordinates.

## 4. Theorem S (retained neighbours)

Let `F_t` and `F_{t+1}` be consecutive chain faces sharing the retained hinge `E = E_{t+1}` (`t+1 ≠ k`), with `L = L_{t+1}`, `U = U_{t+1}`, `e = U − L`, and suppose:

| Check | Condition |
|---|---|
| S1 | `F_t.exit = E = F_{t+1}.entry`; both rings contain `L` and `U` as vertex IDs with the same exact coordinates; `E` is not the seam; the faces are consecutive in the chain |
| S2 | `L ≠ U`, and `n_t, n_{t+1} ≠ 0` |
| S3 | every ring vertex of each face satisfies its plane with equality (so `e·n_t = e·n_{t+1} = 0`) |
| S4 | with `σ_t(w) = (e × (w − L))·n_t` on the vertices of `T_t` and `σ_{t+1}(w) = (e × (w − L))·n_{t+1}` on those of `T_{t+1}`: one face has all `σ ≤ 0`, the other all `σ ≥ 0`, each with at least one strict value |

Then `int D_t ∩ int D_{t+1} = ∅`.

*Proof.* By definition `Φ_t(L) = Φ_{t+1}(L) =: p` and `Φ_t(U) = Φ_{t+1}(U) =: q`, both maps affine orientation-preserving isometries with linear parts `A_t`, `A_{t+1}`. For `w ∈ plane(F_t)`, L1 gives `cross2(q − p, Φ_t(w) − p) = (e × (w − L))·n̂_t = σ_t(w)/|n_t|`; the same holds for `F_{t+1}` against the same directed line `p → q`. So the two images lie in opposite closed half-planes of one line; their interiors lie in the disjoint open half-planes. ∎

**Use in the lane.** S1–S4 are exact rational computations (`exact_computation`). The inference from them to disjoint interiors is this theorem, together with L1 and L2; the claim that makes it names this file. Theorem S never yields `fail`: when S1–S4 do not all hold, the pair is decided, if at all, by §5.

**Scope.** For `δ > 0` the only material two faces share is their common retained hinge. The seam copies are not shared: the first and last chain faces are an ordinary pair. Pairs that share only a glued vertex arise only without trimming and are out of scope.

## 5. Enclosures and certificates for the other pairs

**Closed formulas (entry-hinge frames).** For face `t`, `H_t v = ((e_t·v)/|e_t|, ((n_t × e_t)·v)/(|n_t||e_t|))`, which is `[ê_t ; n̂_t × ê_t] v` and orientation-preserving by L1; `Φ_t(x) = O_t + Rot(C_t, S_t) H_t (x − L_t)`. Start: `(C_k, S_k) = (1, 0)`, `O_k = (−δ|e_k|, 0)`. Step `t → t+1`: `c_t = (e_t·e_{t+1})/(|e_t||e_{t+1}|)`, `s_t = (n_t·(e_t × e_{t+1}))/(|n_t||e_t||e_{t+1}|)`, `(C_{t+1}, S_{t+1}) = (C_t c_t − S_t s_t, S_t c_t + C_t s_t)`, `O_{t+1} = Φ_t(L_{t+1})`. Since `e_{t+1}` lies in `plane(F_t)`, `H_t e_{t+1} = |e_{t+1}|(c_t, s_t)`, and this is the unique L2 map agreeing on `E_{t+1}`. The only radicands are `e_t·e_t` and `(n_t·n_t)(e_t·e_t)`.

The enclosure arithmetic (exact interval endpoints, verified integer square roots, outward rounding) is stated in the checker's policy; higher precision only narrows intervals and never enters a containment argument.

**Separating-axis lemma (`pass`).** Let `V_t` be interval boxes containing `Φ_t` of the vertices of `T_t`. If for an exact rational axis `d` the value `max_{v ∈ V_t} sup(d·v)` is at most `min_{v' ∈ V_{t'}} inf(d·v')` (or symmetrically), then `D_t` and `D_{t'}` lie in opposite closed half-planes and their interiors are disjoint (equality allowed), because `D_t = conv(Φ_t(vertices))` for an affine `Φ_t`. The recorded `axis_gap` is `g = min inf − max sup ≥ 0`; a recorded Euclidean gap bound `b` is valid when `b ≥ 0` and `b²(d·d) ≤ g²`, since the Euclidean distance between the two sets is at least `g/|d|`.

**Interior-witness lemma (`fail`).** Let `y` be an exact rational point. If each of the two trimmed rings is exactly strictly convex and counterclockwise about its `n_t` (every turn `((v_{i+1}−v_i) × (v_{i+2}−v_{i+1}))·n_t > 0`) and every `cross2(v_{i+1} − v_i, y − v_i)` has a positive lower bound on the boxes, then by L1 each `D_t` is a strictly convex counterclockwise polygon with `y` strictly inside, so the interiors meet. A recorded `cross_lower_bound` `b` is valid when `0 < b ≤ m`, `m` the smallest recomputed lower bound.

**Otherwise `unknown`.** Candidate axes and witness points are proposals; only the certification counts. Arithmetic refusals and an exhausted schedule give `unknown`, never `pass` or `fail`.

## 6. Relation to the manuscript (L4, pinned at `ed135840`)

In exact real arithmetic, with `Ψ` the development defined like `D` but normalized at the untrimmed hinge (`Ψ_k(L_k) = (0,0)`, `Ψ_k(U_k) = (‖G_k‖, 0)`) and `ρ` the orientation-preserving isometry of `R²` aligning `ψ_k(L_k)`, `ψ_k(U_k)` with those points, the note derives, for every **chain position** `j` (face `F_{k+j}`, cyclic face index `k+j`):

- `Ψ_{k+j} = ρ∘𝒰_{k,j}` (L2 induction over the retained hinges), and
- `Φ^δ_{k+j} = τ_δ∘Ψ_{k+j} = τ_δ∘ρ∘𝒰_{k,j}`, with the **common translation** `τ_δ(y) = y − (δ‖G_k‖, 0)`; the translation depends on `δ` and never on the face, and for two trims `Φ^{δ₂}_{k+j} = Φ^{δ₁}_{k+j} − ((δ₂ − δ₁)‖G_k‖, 0)`.

With `F_i^δ = T_i(δ)` (manuscript §3.2, also derived in the note), interiors of `D` meet exactly when the manuscript's trimmed images `𝒰_{k,j}(F_{k+j}^δ)` meet, at that `(k, δ)`.

**Which trims a verdict covers.** For the same fixed maps `𝒰_k`, a `pass` at `δ₀` also holds on every **more-trimmed** domain `δ₀ ≤ δ < 1/2`, by restriction: `F_{k+j}^δ ⊆ F_{k+j}^{δ₀}`, and interiors of subsets lie in the interiors of the sets. It does **not** establish less-trimmed material (`δ < δ₀`), all positive trims, the untrimmed limit, or full safety. A certified `fail` shows that the fixed maps for that `k` are not safe on that trim.

L4 is not a premise of any claim about `D`; it is what relates `D` to the manuscript. Its manuscript dependencies (Proposition 3.1 and the definitions (3.1), (3.6), (4.1), (4.2)) are pinned in the note and not re-proved.

## 7. What the lane's results do not establish

- Verdicts concern `D` for the named ideal state only. They never apply to, or relabel, a float development or trimmed state; the float lane's evidence and its `unknown`s keep their meaning.
- A finite scan of specimens is not a universal theorem. No full or untrimmed safety, continuous motion, cap argument or proof-guided seam selection follows from it.
- `unknown` is never a safety pass. A refusal for unsupported input or missing prerequisites is not an overlap.
