---
title: L4 correspondence - the ideal development D and the manuscript's fixed full maps
author: Claude Code session (Claude Opus 5.5), outside the project's agent team
date: 2026-09-29
status: written argument; reviewed by System (an AI reviewer) and accepted under its listed dependencies; NOT machine-checked, NOT formally verified, NOT reviewed by a human mathematician
dg-publish: false
---

> **Export note (edition 1.1).** This is a sanitized copy made for the research export. Private repository locations, research-folder locations, branch names and commit identifiers were replaced by placeholders and `commit-NN` labels, and the author line names no private project. The mathematical text is unchanged. Git blob and SHA-256 identifiers pinned by the evidence policy refer to these export copies; the historical originals and their identifiers are retained privately.

# L4 correspondence: `D` and the manuscript's full maps `𝒰_k`

**Revision (2026-09-29), after System's review of `commit-62`,** which accepted the argument of blob `5976b026` under its listed dependencies. Two exposition clarifications, nothing else changed; Git history keeps the reviewed text:
1. The chain position `j` is used consistently: `F_{k+j}` is the face at chain position `j` (`0 ≤ j < n`, face indices mod `n`), with maps `Ψ_{k+j}`, `Φ^δ_{k+j}` and `𝒰_{k,j}`. A face index never stands in the position slot of `𝒰_{k,·}`.
2. §8 now states precisely which trims a `pass` covers: more-trimmed subdomains of the same fixed maps, and nothing less trimmed.

**Purpose.** System's Stage 4A review asked for the full written bridge from the probe's ideal trimmed development `D` to the manuscript's construction:
- oriented chart isometries
- agreement on the entire hinge line, including translation
- first-face normalization
- an induction using L2
- the trim-dependent normalization `N0` and the common translation between normalizations

This note gives that argument. It establishes nothing formally. It is a derivation for review, with its dependencies listed in §9.

## 0. Pinned sources

- **Manuscript:** `<research-record>/<historical-folder>/manuscript/DRAFT-02.md`, Git blob `8b9f7e1a4633c372053ba43e65208847d0ebb93d`, identical on the worker branch and on `origin/main`. Used:
  - §2.2 (the quotient `S_k`)
  - (2.2) (`Safe`), Theorem 2.1, (2.3) (trims `F_i^δ`, `0 < δ < 1/2`), (2.4) (quantifiers: one `k` and one `𝒰` for all δ)
  - Proposition 3.1 (facets `F(u)`, clockwise normal order)
  - (3.1) (`G_i`, `M_i`, `ℓ_i`, `ν_i`; `G_i` has vertical component `h`; `ν_i` horizontal)
  - (3.6) (`φ_i^±`, `q_i`)
  - §3.2 (clipped endpoints `L_i^δ`, `U_i^δ`)
  - (4.1) (`c_i`, `s_i`, `ξ_i`, `ψ_i`)
  - (4.2) and the composition `W_{k,0} = id`, `W_{k,j+1} = W_{k,j}∘T_{k+j}`, `𝒰_{k,j} = W_{k,j}∘ψ_{k+j}`
  - §4.3 (pole translation)
  - §9 ("the same Q-copies, full maps, and pole are retained" across trims)
- **Stage 4A design:** `engine/STAGE-4A-DESIGN.md`, blob `bb32b132469d0dfe5098f9d0d76ddde5113cc49d`:
  - §2.2: L1, side transfer `cross2(Aa, Ab) = (a×b)·n̂` for `A = R[ê ; n̂×ê]`; L2, existence and uniqueness of the orientation-preserving plane isometry with two prescribed point images
  - §2.3: definition of `D`
- **Geometry Lab conventions:** `engine/TWO-RIM-SCHEMA.md`, blob `5086d553`:
  - `F_t` lies between entry hinge `E_t` and exit hinge `E_{t+1}`
  - hinges and faces follow the clockwise merged normal order
  - `plane` carries the outward normal
  - lateral rings are counterclockwise about the outward normal

**Notation.** Faces `F_i` (indices mod `n`); hinges `E_i` from `L_i` (height 0) to `U_i` (height `h`); `G_i = U_i − L_i`. `n̂_i` is the outward unit normal of `aff(F_i)`, and `Π_i` is its direction plane. `cross2(x, y) = x₁y₂ − x₂y₁`.

## 1. The charts `ψ_i` preserve orientation with respect to the outward normals

**Claim 1.** Let `A_i := Dψ_i` be restricted to `Π_i`. Then `A_i` is a linear isometry onto `R²`, and `cross2(A_i a, A_i b) = (a × b)·n̂_i` for all `a, b ∈ Π_i`.

*Derivation.*

1. **Rows.** `ψ_i` has rows `r₁ = ν_i` and `r₂ = −ξ_i` (4.1).
   - `ν_i ∈ Π_i`, because `M_i` and `M_{i+1}` are midpoints of the two hinges of `F_i`.
   - `ξ_i ∈ Π_i`, because it is a combination of `G_i ∈ Π_i` and `ν_i`.
   - They are orthonormal by the construction in (4.1): `ξ_i` is the normalized component of `G_i` orthogonal to `ν_i`, and `s_i > 0`.

   So `A_i` is an isometry of `Π_i` onto `R²`.
2. **Orientation form.** By the Binet–Cauchy identity, `cross2(A_i a, A_i b) = (a×b)·(r₁ × r₂) = −(a×b)·(ν_i × ξ_i)`. It remains to show `ν_i × ξ_i = −n̂_i`.
3. **Vertical component of `ξ_i`.** `ξ_i = (G_i − c_iν_i)/s_i`, and `ν_i` is horizontal (3.1). So `ξ_i` has vertical component `h/s_i > 0`. Write `ξ_i = ξ_h + ξ_z ẑ` with `ξ_z > 0` and `ξ_h` horizontal.
4. **Split.** `ν_i × ξ_i = ν_i × ξ_h + ξ_z (ν_i × ẑ)`. The first term is vertical, since both factors are horizontal. The second is horizontal.
5. **Relating `ν_i` to the outward normal.**
   - `ν_i` is the forward direction of the middle-section edge `M_i → M_{i+1}` of `(A+B)/2`, in the manuscript's **clockwise** source order (Proposition 3.1; (3.2)).
   - For a convex polygon traversed clockwise, the outward edge normal is the edge direction turned by `+π/2`: `u_i = (−ν_{i,y}, ν_{i,x})`. Example: clockwise around a square, the downward right edge `ν = (0, −1)` has outward normal `(1, 0)`.
   - Hence `ν_i × ẑ = (ν_{i,y}, −ν_{i,x}, 0) = −u_i`.
6. **Conclusion.** The horizontal part of `ν_i × ξ_i` is `−ξ_z u_i`, a **negative** multiple of `u_i`.
   - The outward unit normal of `F_i` has a **positive** multiple of `u_i` as its horizontal part: the supporting plane `⟨u, x⟩ + ((σ_B − σ_A)/h) z = σ_B` of Proposition 3.1 has normal `(u, (σ_B−σ_A)/h)`, and it is outward.
   - `ν_i × ξ_i` is a unit normal of `Π_i`, so it is `±n̂_i`. The horizontal parts force the sign `−`.

   Therefore `r₁ × r₂ = n̂_i`. ∎

**Status.** Derivation only. The probe's exact per-instance check (`receipts/results/l4-hypotheses.json`) found the sign `−(m × ξ')·n = +1` for every face of E11 and of the square prism, which is consistent with Claim 1. That consistency is not a proof of it.

## 2. `T_i∘ψ_{i+1}` and `ψ_i` agree on the entire hinge line, rotation and translation

Let `ℓ_{i+1} = {M_{i+1} + λ G_{i+1} : λ ∈ R}`, and let `w_{i+1} = G_{i+1}/‖G_{i+1}‖`.

**Claim 2.** `T_i∘ψ_{i+1} = ψ_i` on `ℓ_{i+1}`.

*Derivation.* Both sides are affine, so it suffices to check one point and the direction of the line.

- **The point `M_{i+1}`.**
  - `ψ_{i+1}(M_{i+1}) = 0` (4.1), so `T_i(0) = (ℓ_i, 0)` (4.2).
  - `ψ_i(M_{i+1}) = (ν_i·(M_{i+1}−M_i), −ξ_i·(M_{i+1}−M_i)) = (ℓ_i, 0)`, because `M_{i+1} − M_i = ℓ_i ν_i` (3.1) and `ξ_i ⊥ ν_i`. This is the manuscript's identity `ψ_i(M_{i+1}) = (ℓ_i, 0)`.
- **The direction `w_{i+1}`, in chart `i+1`.**
  - `Dψ_{i+1}(w_{i+1}) = (ν_{i+1}·w_{i+1}, −ξ_{i+1}·w_{i+1})`.
  - By (3.6), `ν_{i+1}·w_{i+1} = cos φ_{i+1}^+`.
  - `ξ_{i+1}·w_{i+1} = s_{i+1}/‖G_{i+1}‖ = sin φ_{i+1}^+ > 0`, since `s = ‖G − cν‖ = ‖G‖ sin φ⁺`.
  - So `Dψ_{i+1}(w_{i+1}) = (cos φ⁺, −sin φ⁺)`.
- **The same direction, in chart `i`.**
  - `w_{i+1} ∈ Π_i = span(ν_i, ξ_i)`, so `w_{i+1} = cos φ_{i+1}^- ν_i + (ξ_i·w_{i+1}) ξ_i`, with `(ξ_i·w_{i+1})² = sin² φ_{i+1}^-`.
  - Its sign: the vertical component of `w_{i+1}` is `h/‖G_{i+1}‖ > 0`, and it equals `(ξ_i·w_{i+1}) ξ_{i,z}` with `ξ_{i,z} > 0`, as in §1 step 3. So `ξ_i·w_{i+1} = sin φ_{i+1}^- > 0`.
  - So `Dψ_i(w_{i+1}) = (cos φ⁻, −sin φ⁻)`.
- **The rotation matches them.** `R(q_{i+1})` turns angle `−φ⁺` into `−φ⁺ + q_{i+1} = −φ⁻`, because `q_{i+1} = φ⁺_{i+1} − φ⁻_{i+1}` (3.6). Hence `D(T_i∘ψ_{i+1})(w_{i+1}) = R(q_{i+1}) Dψ_{i+1}(w_{i+1}) = Dψ_i(w_{i+1})`. ∎

This re-derives the manuscript's sentence after (4.2), "Hence `T_i∘ψ_{i+1}` and `ψ_i` agree on the entire supporting hinge line". It pins each ingredient, and it keeps the **translation**: the point `M_{i+1}` goes to the same image, not merely the same direction.

## 3. The manuscript's full maps agree on every retained hinge

`W_{k,j}` is a finite composition of maps `T_m`, each a rotation followed by a translation. So each `W_{k,j}` is an orientation-preserving isometry of `R²`. By Claim 1, each `𝒰_{k,j} = W_{k,j}∘ψ_{k+j}` is an **orientation-preserving (with respect to `n̂_{k+j}`) affine isometry of `aff(F_{k+j})`**.

For `0 ≤ j < n−1`:

`𝒰_{k,j+1} = W_{k,j}∘T_{k+j}∘ψ_{k+j+1} = W_{k,j}∘ψ_{k+j} = 𝒰_{k,j}` on `ℓ_{k+j+1}`, by Claim 2.

These are exactly the retained hinges `E_{k+1}, …, E_{k+n−1}`. **No** agreement is claimed on the seam `E_k` between positions `n−1` and `0`, as in the quotient `S_k` (§2.2).

## 4. First-face normalization

**The trim-independent development `Ψ`.** Let `Ψ` be the development defined like `D` (design §2.3), with outward orientation, but with the normalization `N_L`: `Ψ_k(L_k) = (0,0)`, and `Ψ_k(U_k) = (‖G_k‖, 0)`. The recursion is:

for `j = 0, …, n−2`, `Ψ_{k+j+1}` is the unique orientation-preserving isometry of `aff(F_{k+j+1})` agreeing with `Ψ_{k+j}` at `L_{k+j+1}` and `U_{k+j+1}`.

This is well defined by L2.

**The map `ρ`.** `ψ_k` is an isometry, so `‖ψ_k(U_k) − ψ_k(L_k)‖ = ‖G_k‖`. Applying L2 to the plane `R²` gives a unique orientation-preserving isometry `ρ` of `R²` with:
- `ρ(ψ_k(L_k)) = (0,0)`
- `ρ(ψ_k(U_k)) = (‖G_k‖, 0)`

Then `ρ∘𝒰_{k,0} = ρ∘ψ_k` is an orientation-preserving isometry of `aff(F_k)` with the same values as `Ψ_k` at `L_k` and `U_k`. By the uniqueness in L2, `Ψ_k = ρ∘𝒰_{k,0}`.

## 5. Induction

**Claim 5.** `Ψ_{k+j} = ρ∘𝒰_{k,j}` for `j = 0, …, n−1`.

*Derivation.* The case `j = 0` is §4. Suppose the claim holds for `j < n−1`. Then:
- `ρ∘𝒰_{k,j+1}` is an orientation-preserving isometry of `aff(F_{k+j+1})`, by §3 and because `ρ` preserves orientation;
- by §3, it agrees with `ρ∘𝒰_{k,j} = Ψ_{k+j}` on the whole line `ℓ_{k+j+1}`, in particular at `L_{k+j+1}` and `U_{k+j+1}`.

`Ψ_{k+j+1}` is defined by exactly these two conditions. By the uniqueness in L2, `ρ∘𝒰_{k,j+1} = Ψ_{k+j+1}`. ∎

## 6. The trim-dependent normalization `N0` and the common translation

The probe's `D^δ` (design §2.3) normalizes at the **trimmed** low point:
- `Φ^δ_k(P_k^lo) = (0,0)` with `P_k^lo = L_k + δG_k`
- `Φ^δ_k(P_k^hi) = ((1−2δ)‖G_k‖, 0)` with `P_k^hi = L_k + (1−δ)G_k`

So `N0` **depends on δ**. System pointed this out.

Let `τ_δ(y) = y − (δ‖G_k‖, 0)`.

**Claim 6.** `Φ^δ_{k+j} = τ_δ∘Ψ_{k+j}` for every chain position `j = 0, …, n−1`. Hence `Φ^δ_{k+j} = τ_δ∘ρ∘𝒰_{k,j}`.

*Derivation.*
- `Ψ_k` is affine, so `Ψ_k(P_k^lo) = Ψ_k(L_k) + δ(Ψ_k(U_k) − Ψ_k(L_k)) = (δ‖G_k‖, 0)`. Applying `τ_δ` gives `(0,0)`.
- Likewise `Ψ_k(P_k^hi) = ((1−δ)‖G_k‖, 0)`, which `τ_δ` sends to `((1−2δ)‖G_k‖, 0)`.
- `τ_δ∘Ψ_k` is orientation-preserving. The points `P_k^lo ≠ P_k^hi` are distinct because `δ < 1/2`. By the uniqueness in L2, `Φ^δ_k = τ_δ∘Ψ_k`.
- For later positions, both families satisfy the same agreement recursion, and a global translation preserves agreement and orientation. The induction of §5 then gives `Φ^δ_{k+j} = τ_δ∘Ψ_{k+j}` for every `j`. ∎

**The common translation between normalizations.** For two trims `δ₁, δ₂ ∈ (0, 1/2)`:

`Φ^{δ₂}_{k+j} = Φ^{δ₁}_{k+j} − ((δ₂ − δ₁)‖G_k‖, 0)` for every chain position `j`.

The trim-normalized families are **one fixed map family `ρ∘𝒰_k`, followed by a δ-dependent global translation along `x`**. The translation never depends on the face. This matches System's remark that the initial offset is `−δ|e_k|` along x, with `|e_k| = ‖G_k‖`. In the probe's formulas: `O_k = (−δ|e_k|, 0)`, and `H_k(x − L_k) = Ψ_k(x)` by L1.

**Other translations.** The manuscript's pole centering (§4.3, "translating the entire development by `−O`") is another single global isometry. So are the historical frame and `N_L`. None of them changes which interiors meet.

## 7. The trimmed faces are the manuscript's `F_i^δ`

The probe's trimmed face is `T_i(δ) = conv{P_i^lo, P_i^hi, P_{i+1}^hi, P_{i+1}^lo}`, with `P^lo = L + δG = L_i^δ` and `P^hi = L + (1−δ)G = U_i^δ` (§3.2).

§3.2 states that the retained facet `F_i^δ = F_i ∩ {δh ≤ z ≤ (1−δ)h}` of (2.3) is exactly the convex hull of its four clipped endpoints. Here is a short independent argument:

- `F_i^δ` is convex, as an intersection of convex sets.
- Height `z` is a nonconstant affine function on `aff(F_i)`. So `F_i^δ` is the convex polygon `F_i` cut by two parallel lines.
- A convex polygon cut by two parallel lines equals the convex hull of its two line sections together with its vertices strictly between the lines.
- The vertices of `F_i` are rim points, at height 0 or `h` (Proposition 3.1). Since `δ > 0`, none lies strictly between the lines. So `F_i^δ = conv(section at δh ∪ section at (1−δ)h)`.
- Only the two hinges `E_i` and `E_{i+1}` cross interior heights; the rim runs sit at heights 0 and `h`. So the sections are `[L_i^δ, L_{i+1}^δ]` and `[U_i^δ, U_{i+1}^δ]`. This also holds for triangles, where one rim run is a point and the two hinges share an endpoint.

Hence `F_i^δ = T_i(δ)`.

## 8. Consequence (conditional on §9)

For chain positions `j ≠ j'` at seam `k` and trim `δ ∈ (0, 1/2)`:

`int Φ^δ_{k+j}(T_{k+j}(δ)) ∩ int Φ^δ_{k+j'}(T_{k+j'}(δ)) = ∅` holds exactly when `int 𝒰_{k,j}(F_{k+j}^δ) ∩ int 𝒰_{k,j'}(F_{k+j'}^δ) = ∅`.

This is because `Φ^δ = (τ_δ∘ρ)∘𝒰_k` (§§6–7), and `τ_δ∘ρ` is one bijective isometry of `R²`, which carries planar interiors to planar interiors.

What follows, and what does not:
- **The verdict transfers.** A probe verdict on `D` at `(k, δ)`, `pass` or `fail`, is the same verdict for the manuscript's trimmed family `𝒰_{k,·}|F^δ` at that `(k, δ)`, subject to §9.
- **What a `fail` means.** A certified `fail` shows that the manuscript's **fixed** maps for that `k` are not safe on that trim. So that `k` cannot be the hinge whose trimmed conclusion (2.4) holds for all δ. This is consistent with Theorem 2.1, which asserts only that **some** `k` exists.
- **What a `pass` covers, and what it does not.** For the same fixed maps `𝒰_k`, a `pass` at `δ₀` also holds on every **more-trimmed** subdomain `δ₀ ≤ δ < 1/2`:
  - the slab `[δh, (1−δ)h]` lies inside `[δ₀h, (1−δ₀)h]`, so `F_{k+j}^δ ⊆ F_{k+j}^{δ₀}` for every position `j`;
  - the fixed maps carry these subsets into the `δ₀` images, and interiors of subsets lie in the interiors of the sets, so disjoint interiors stay disjoint.

  It does **not** establish less-trimmed material (`δ < δ₀`), all positive trims, the untrimmed limit, or full safety. Neither verdict adds a motion claim or a new safety theorem.

## 9. Dependencies and what remains open

| Id | Dependency | Status |
|---|---|---|
| M1 | Manuscript statements used as given: Proposition 3.1 (facets, the clockwise order, rim vertices at heights 0 and `h`); the definitions (3.1), (3.6), (4.1), (4.2) and the `W`/`𝒰` compositions | pinned by blob; **not re-proved here** (Proposition 3.1 is the manuscript's own argument) |
| M2 | Claim 1: charts preserve orientation with respect to outward normals | derived in §1; not machine-checked. The per-instance exact sign check is consistent on E11 and the prism. |
| M3 | Claim 2: entire-line agreement, including translation | derived in §2 from (3.1), (3.6), (4.1), (4.2); not machine-checked |
| M4 | L1, L2 | design §2.2 (blob `d06000f8`); not machine-checked |
| M5 | Claims 5 and 6: induction, and the common translation | derived in §§5–6; not machine-checked |
| M6 | `F_i^δ = T_i(δ)` | derived in §7, and stated in manuscript §3.2; not machine-checked |
| G1 | Geometry Lab's material is the manuscript's facet cycle, in the same clockwise order, with outward normals and counterclockwise rings | Stage 2 v2 checker evidence (exact supporting-plane oracle, incidence and rings), carried as a prerequisite by every probe certificate. The index labels may be a cyclic rotation of the manuscript's; the correspondence is by coordinates. |
| O3 | the probe's interval implementation | controls and independent re-check; not formally verified |

**Not claimed:**
- a Lean or formal proof, or any `formal_proof` evidence
- a review by a human mathematician
- that any probe result proves Theorem 2.1 or refutes it
