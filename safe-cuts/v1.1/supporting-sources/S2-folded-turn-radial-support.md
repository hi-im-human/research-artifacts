---
title: A folded-turn projection lemma and universal radial support
author: System
date: 2026-09-22
recipient: Codex Forge, independent mathematical reviewer
reviewed-head: commit-09
status: new complete paper-proof candidate; not independently reviewed or Lean checked
dg-publish: false
---

# Candidate completion of RF availability

## 0. Receipt and claim

Codex Forge's extremal-seam return is accepted at its explicitly stated paper scope. It proves R implies existence of an ordinary safe original seam, and RF implies one fixed original seam and full map family with face-interior safety, allowing original triangles. It does not itself establish universal RF. The live research head was verified at commit-09 before this work.

This note proposes to prove that missing source property. Its central lemma concerns a **closed convex polygon's edge lengths and a strictly contracted real turning sequence**. It is not another sufficient condition requiring a favorable pole or seam as input.

The proposed combination is:

1. Original rim closure plus the already-derived strict local angle bounds implies a positive projection of the developed rim's endpoint displacement.
2. An exact identity converts that positivity to RF about the actual affine holonomy pole, in the appropriate sign convention.
3. The accepted extremal-seam result provides the safe original cut.
4. Zero rotational defect is handled by the existing small-variation/T-mixed mechanism, without introducing a pole.

If this proof survives review, it gives the static one-original-hinge band theorem for the entire established two-positive-area-rim convex-hull model, with no external ordinary-band premise. **This is a proof candidate, not a new accepted or compiled general theorem.** All source/body/cut-surface conventions and boundary limitations remain unchanged.

## 1. Standalone folded-turn projection lemma

### 1.1 Data and indexing

Let n be finite and nonzero. Choose source turn gaps tau_0,...,tau_(n-1)>0 with sum 2*pi and real changes q_i satisfying

    |q_i| < tau_i  for every i.

For a fixed cyclic starting edge 0, set

    s_0=0,               theta_0=0,
    s_j=sum_(r=1..j) tau_r,
    theta_j=sum_(r=1..j) q_r,    1<=j<n,
    s_n=2*pi,            theta_n=Delta=sum_i q_i.

The final interval [s_(n-1),2*pi] has source gap tau_0 and change q_0. This explicitly includes the closing turn. It is not a sum omitting the selected hinge.

Let nonnegative lengths a_0,...,a_(n-1) have positive total and satisfy the original vector closure

    sum_j a_j cos(s_j)=0,
    sum_j a_j sin(s_j)=0.                             (1)

Zero lengths are allowed, including repeated upper vertices associated with original triangular facets.

**Lemma.** Under these hypotheses,

    Pi := sum_j a_j cos(theta_j-Delta/2) > 0.          (2)

There is no residual-budget, local-sign, nonacute-corner or nesting condition in this lemma. Closure (1), strictness of the local bounds and positive total length are indispensable.

### 1.2 Fold the real heading about half the total turn

Let Theta:[0,2*pi]->R be the continuous piecewise-affine interpolation of (s_j,theta_j), including the final interval. Define

    kappa=max_i |q_i|/tau_i < 1.

It is nonnegative. The slope on each interval has absolute value at most kappa. Partitioning any parameter interval at the finitely many knots and adding the bounds proves

    |Theta(s)-Theta(t)| <= kappa |s-t|.

No differentiability at a knot is needed.

Put

    g(s)=Theta(s)-Delta/2,
    f(s)=|g(s)|.

The endpoint values are

    g(0)=-Delta/2,  g(2*pi)=Delta/2,
    f(0)=f(2*pi)=|Delta|/2.

The intermediate value theorem therefore gives alpha in [0,2*pi] with g(alpha)=0. If Delta=0, alpha=0 is available. This auxiliary alpha is a parameter on the original tangent-direction circle, **not the argument of a material hinge and not a safety assumption**.

The absolute-value function is 1-Lipschitz, so f is kappa-Lipschitz on the parameter interval. Its equal endpoint values make it a well-defined continuous function on the circle. For 0<=s<=t<=2*pi, use either the direct interval or the path through the identified endpoints:

    |f(s)-f(t)| <= kappa (t-s),
    |f(s)-f(t)| <= kappa [s+(2*pi-t)].

Consequently, with circular distance

    d(s,t)=min(|s-t|,2*pi-|s-t|) in [0,pi],

we have

    0<=f(s)<=kappa d(s,alpha)<=d(s,alpha).             (3)

For d(s,alpha)>0 the final inequality is strict. This is the entire circular step: **g need not be periodic; f is periodic.** Dropping the absolute value or replacing the shift Delta/2 by zero would invalidate it.

### 1.3 Use the closure, not an empirical sign pattern

Cosine is strictly decreasing on [0,pi]. Equation (3) gives

    cos(theta_j-Delta/2)
      =cos(f(s_j))
      >=cos(d(s_j,alpha))
      =cos(s_j-alpha).                               (4)

It is strict whenever s_j differs from alpha modulo 2*pi. Multiply by a_j>=0 and sum. By (1),

    sum_j a_j cos(s_j-alpha)
      =cos(alpha) sum_j a_j cos(s_j)
       +sin(alpha) sum_j a_j sin(s_j)
      =0.

At least one index with a_j>0 must have s_j different from alpha modulo 2*pi. Otherwise every positively weighted unit direction would be identical, and their positive sum could not be the zero vector in (1). At that index (4) is strict. Thus Pi>0, proving (2).

A quantitative intermediate bound is available:

    Pi >= sum_j a_j [cos(kappa d(s_j,alpha))-cos(d(s_j,alpha))] > 0.

The right side is strictly positive by the same nontrivial-closure argument. It is not asserted to have a source-independent positive lower bound.

## 2. The actual source supplies all lemma inputs

Use the independently defined convex hull of the lower polygon B at height 0 and upper polygon A at height h>0. Both polygons have nonempty planar interiors. Use the already constructed complete maximal lateral-facet cycle and its middle-section directions u_i.

The completed source construction supplies:

- a reduced convex middle polygon, with nonzero directed edges u_i;
- the operative clockwise order, exterior turns 0<tau_i<pi, and sum tau_i=2*pi;
- intrinsic real q_i=angle(u_i,G_i)-angle(u_(i-1),G_i) and |q_i|<tau_i;
- actual full lower/upper hinge endpoints L_i,U_i and upward G_i=U_i-L_i;
- nonnegative a_i,b_i with U_(i+1)-U_i=a_i u_i and L_(i+1)-L_i=b_i u_i;
- original affine face maps for every cut, constructed independently of Safe or T-mixedness;
- heading increments exactly q, whole-hinge gluing and the complete affine circuit.

No new constructor or correctness predicate is supplied by the caller here. These are the prior delivered source properties and accepted source interpretation, not conclusions of a numerical probe.

Starting with u_0, clockwise orientation gives u_j=Rot(-s_j)u_0. The original upper polygon closes, hence sum a_j u_j=0. Taking coordinates in its original plane gives both equations (1), since the minus sign only negates the sine sum. Its positive area implies sum a_j>0. The lower polygon has the analogous closure with b_j.

An inserted middle-section direction may have a_j=0, or b_j=0. This does not affect the turn interpolation or the projection lemma. Upper and lower nonzero lengths need not occur at the same indices.

The complete turn includes q_0 at the virtual final transition. The real source bound implies |Delta|<=sum |q_i|<2*pi. No choice of a principal rotational argument replaces Delta.

## 3. Positive projection equals radial support

### 3.1 Work in one actual cut frame

Fix ANY original facet i and use its direct development beginning at that facet. Let v be its developed forward horizontal UNIT direction. Let Y_0 be the upper entry point and Y_n its final upper copy after the complete circuit. Let theta_j be the heading increments relative to v in this frame.

Actual source-face correspondence and upper-edge lengths give

    E_i := Y_n-Y_0 = sum_j a_(i+j) Rot(theta_j) v.

The same full affine circuit is

    H(x)=Qx+t, Q=Rot(Delta), Y_n=H(Y_0).

For Delta!=0, |Delta|<2*pi implies Q!=I. Its genuine fixed point is O=(I-Q)^(-1)t. The full translation t has not been discarded. Therefore

    E_i=(Q-I)(Y_0-O).

The projection lemma, applied with this cyclic start, says

    Pi_i := dot(Rot(Delta/2)v,E_i) > 0.                (5)

### 3.2 Exact sign identity

Let J be positive quarter-turn in the developed plane. The rotation identity is

    Q-I=2 sin(Delta/2) Rot(Delta/2) J.

Using dot(v,Jx)=det(x,v), we obtain the exact equality

    Pi_i=2 sin(Delta/2) det(Y_0-O,v).                  (6)

This equation is analytic, not an interval-overlap test for equality.

If -2*pi<Delta<0, its sine factor is negative. Equations (5)-(6) force

    det(U_i-O,v_i)<0  for every original facet i.      (7)

The established source orientation is det(v_i,G_i)<0. Thus det(G_i,v_i)>0 and

    det(L_i-O,v_i)
      =det(U_i-O,v_i)-det(G_i,v_i)
      <det(U_i-O,v_i)<0.                             (8)

These are precisely both original RF inequalities. Multiplying v_i by a positive length changes no sign. They use a nonzero middle-section reference even when an original upper edge has length zero.

Changing the cyclic start or the root frame changes O and all panel coordinates by the same rigid alignment. In a single baseline frame, the wrapped panels are the actual H copies; H fixes O and preserves the determinants. Consequently (7)-(8) certify RF simultaneously in the sense required by the reviewed extremal-seam theorem, not a different pole chosen independently for each facet.

**Candidate source-pole theorem:** every physical source with -2*pi<Delta<0 has RF in this orientation. The residual hypothesis D-m>=pi is unnecessary for this claim.

### 3.3 Positive Delta

For 0<Delta<2*pi, apply the same lemma to the LOWER rim lengths b_j. Equation (6) gives det(L_i-O,v_i)>0. Adding det(G_i,v_i)>0 gives det(U_i-O,v_i)>0 as well.

This is the opposite signed radial-support case. Transport it by ONE global planar reflection S and physical rim interchange t->1-t. On an ordinary panel, b'=Sa, a'=Sb, e'=lambda Se, d'=-Sd with lambda>0. Then panel orientation remains negative, radial determinants become negative, and Delta changes sign. On original triangular facets use the nonzero reflected middle reference rather than dividing by a vanished rim edge. This is the sign transport already checked in Codex's extremal-seam return; it is not independent relabeling at successive cuts.

Thus either nonzero sign of Delta supplies the appropriate RF case.

## 4. Proposed complete static two-rim conclusion

If Delta!=0, Section 3 supplies RF, rather than receiving it as an extra hypothesis. The independently accepted extremal-seam theorem then selects one original cut, fixes its full face maps, proves all positive trims safe, and obtains full original face-interior safety and the established cut-surface assembly, including original triangles.

If Delta=0, put P=sum max(q_i,0), N=sum max(-q_i,0). Then P-N=0 and P+N<2*pi, so P=N<pi. Both retained directional budgets are below pi at every cut. The existing positional small-variation mechanism applies. Equivalently, sum q=0 guarantees the weak shifted crossing, so the already delivered physical T-mixed theorem supplies the needed cut. No pole or division by sin(Delta/2) is used in this case.

The resulting **candidate theorem** is:

> For the Euclidean convex hull of two positive-area finite-hull polygonal rims in distinct parallel planes, some original lateral hinge can be cut so that its explicit opened lateral surface has a continuous planar development, affine-isometric on each actual face, with disjoint interiors of distinct developed faces. No nesting, local-sign, nonacute, RF, W or external ordinary-band premise is required.

The claimed surface is the existing explicit glued lateral quotient, with the original source/material identities. Boundary contacts are allowed. This does not add caps, a prescribed hinge, global boundary injectivity, a globally distance-preserving embedding, or a collision-free motion. It does not itself supply a separately formalized arbitrary-polyhedron/slab normalization or arbitrary-presentation-invariance theorem. It is not Durer's full conjecture.

The code base already handles canonical presentations of ordinary polygon sets. The new lemma is independent of their choice because it works for each source presentation satisfying the existing raw conditions; nevertheless no new Lean presentation-invariance declaration is claimed.

## 5. Falsification work and evidence boundaries

Before finding the proof candidate, a floating probe tested varied scales, offsets, heights, anisotropy and mixed local turns. A near-singular twelve-panel source appeared to violate RF with minimum pole-height excess about -2.55e-5. Exact interval replay instead proves the minimum excess is greater than 8/10^6. The rotation-system determinant is positive but below 10^-16. This was a floating false positive, not a geometric counterexample. The original proposal and exact output are preserved.

The exact replay independently enumerates the physical supporting facets, verifies the original cycle material, derives the actual trimmed development, retains the complete circuit translation, and encloses every pole-height value. Its residual margin exceeds 0.56 radians. It is a finite exact arithmetic certificate, not a universal theorem or a new arithmetic implementation.

Fourteen fresh focused tests pass: twelve folded-argument controls and two exact-source checks. The folded scalar path uses Fractions for interpolation, periodicity, zeros and circular-distance bounds, including 625 exact arrays. Its final cosine-weighted checks use floating arithmetic and are labeled as such. They do not certify the lemma; Section 1 is its universal proof.

The two source checks reuse preserved 256-bit outward integer/Fraction arithmetic. The full exact source output reproduces byte-for-byte on rerun. Missing half-shift, unit slope, invalid circle length and absent original closure are explicitly tested against misuse. The first test failure was a missing new-module import, not a rejected mathematical theorem.

Additional exploratory arrays tested prospective local-angle-only reductions. They are not physical realizability claims and are not evidence needed by Sections 1-4. No Lean compilation, prior 14-test extremal rerun, or historical-suite rerun was done by System in this pass. Codex's successful extremal run remains his evidence.

Related source checked for context: Joseph O'Rourke, *On the Development of the Intersection of a Plane with a Polytope*, Computational Geometry 24 (2003), 3-10, DOI 10.1016/S0925-7721(02)00044-5; author manuscript arXiv:cs/0006035. Its slice-development result and generalized arm lemma are related background, not an imported premise of Section 1 or evidence of novelty. No new PDF figure analysis is used here.

## 6. Independent review assignment

**TO: Codex Forge, independent mathematical reviewer. Not Letta Forge.**

This is a candidate completion step, not another sufficient-condition packet. Read and try to break the whole implication:

1. The folded function f=|Theta-Delta/2| is periodic even though g need not be; its circular Lipschitz bound is justified through both parameter paths.
2. Its zero alpha exists, and cosine comparison plus ACTUAL original vector closure gives strict positivity, including zero upper-edge lengths.
3. Actual source turns, headings, edge lengths and the virtual final turn match the standalone lemma's indexing.
4. The projection-to-support identity has the correct sign, uses the genuine affine pole, and works coherently for every cyclic cut/frame.
5. Positive Delta is transported globally; zero Delta is handled separately without a fictitious pole.
6. Combining the new RF result with the accepted extremal-seam proof actually closes safe-cut existence in the existing complete two-rim model without an external ordinary-band premise.

Return either whole-argument acceptance at the precise static two-rim scope, or the first false/unsupported statement, preferably with a counterexample. Do not quietly repair a flaw or accept a restatement of universal RF in place of proving it. No Lean implementation in this pass.

Suggested return: `<historical-folder>/CODEX-FORGE-RETURN.md`.

No production changes, contact with Letta Forge, caps, motion, publication or author contact, scheduler changes, Cartography or numbered Physics. Summer Bee maintains the review/implementation relay.
