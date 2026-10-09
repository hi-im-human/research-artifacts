# Lean check — strict nesting of Minkowski sections

This is the narrow formal check requested in `LEAN HANDOFF.md`. It proves Lemma B only; it does
not formalize or validate the downstream safe-cut limit argument.

## Result

For a real normed vector space `E`, define

```lean
minkowskiSection A B u = (1 - u) • B + u • A.
```

Lean accepts:

```lean
theorem section_strict_nesting
    {A B : Set E} (hB : Convex ℝ B) (hAB : A ⊆ interior B)
    {s t : ℝ} (_hs0 : 0 ≤ s) (hst : s < t) (ht1 : t < 1) :
    minkowskiSection A B t ⊆ interior (minkowskiSection A B s)
```

It also accepts the requested specialization

```lean
0 < δ → δ < 1 / 2 →
  minkowskiSection A B (1 - δ) ⊆ interior (minkowskiSection A B δ).
```

## Match to the paper proof

The formal theorem matches the handoff statement and exposes **no gap in Lemma B**.

- No extra hypothesis was required.
- `A` need not be convex, compact, nonempty, finite, or polygonal.
- `B` need only be convex; compactness, nonemptiness, polygonality, and finite dimensionality are
  unnecessary.
- The stated `0 ≤ s` hypothesis is accepted but unused: `s < t < 1` already gives `1 - s > 0`,
  which is all this proof needs.
- Empty `A` is handled vacuously.

The two load-bearing paper steps are library facts rather than new low-level proofs:

1. `Convex.combo_self_interior_mem_interior` proves that a convex combination with positive
   weight on the interior endpoint lies in the interior of `B`.
2. `interior_smul₀` and `subset_interior_add_left` prove that a nonzero scalar image of that
   interior neighborhood, followed by Minkowski addition of `s • A`, lies in the interior of the
   earlier section.

The remaining algebra is the paper's substitution

```text
λ = (1 - t) / (1 - s)
μ = (t - s) / (1 - s)
b' = λ b + μ a,
```

with `λ ≥ 0`, `μ > 0`, `λ + μ = 1`, and
`(1 - t)b + ta = (1 - s)b' + sa` checked by Lean.

## Mutation

The compiled theorem `subset_base_not_enough` proves that replacing the strict hypothesis
`A ⊆ interior B` with `A ⊆ B` is false. The counterexample is `A = B = {0}` in `ℝ`: every section
is `{0}`, but the ambient interior of `{0}` is empty.

`MutationRejected.lean.fail` preserves the corresponding false theorem attempt. The command

```powershell
lake env lean MutationRejected.lean
```

exits `1`; `mutation-rejection.txt` records Lean's exact type mismatch. The `.lean.fail` suffix
keeps the intentionally rejected file out of the default build.

## Build and trust receipt

Pinned environment:

- Lean `4.34.0`, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`
- Lake `5.0.0-src+293d5d0`
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`

Build:

```powershell
lake build ConvexSectionNesting
```

Final exit code: `0` (`8925` jobs). See `build-receipt.txt`.

`#print axioms` reports only:

```text
[propext, Classical.choice, Quot.sound]
```

for the main theorem, the `δ` specialization, and the mutation counterexample. There is no
`sorryAx`.

## Files

- `ConvexSectionNesting.lean` — proof, specialization, counterexample, and axiom checks
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` — reproducible project pins
- `build-receipt.txt` — final version/build/axiom output
- `MutationRejected.lean.fail`, `mutation-rejection.txt` — expected-failure mutation source and
  receipt
- `WORKLOG.md` — implementation trail and failure recovery
