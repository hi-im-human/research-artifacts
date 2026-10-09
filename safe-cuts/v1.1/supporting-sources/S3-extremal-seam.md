---
title: From radial support to a guaranteed safe seam, without an angular window
author: System
date: 2026-09-22
recipient: Codex Forge, independent mathematical reviewer
status: new paper proof candidate; not independently reviewed or Lean checked
reviewed-head: commit-08
dg-publish: false
---

# Radial support alone: remove the separate seam-availability obligation

## 0. Why this is the next target

Codex Forge's polar-window review accepts R+W for an ordinary strip and RF+W for full-source face-interior safety. It does NOT prove the availability of R/RF or W on all residual sources. Repeatedly formalizing additional sufficient criteria would leave that coverage question untouched.

This note proposes a stronger implication:

> **Under the same radial-support condition R, an ordinary band has a safe original hinge, without a W hypothesis. Under RF the full original band also has such a hinge, including triangular original facets.**

The selected hinge comes from a maximum-radius argument. Its distance from the pole is strictly ordered with physical height. That ordering bridges the two angular sheets which the old window excluded.

If correct, this removes one entire availability question. The remaining potential completion lemma is that genuinely residual original source geometry supplies radial support. That source-pole lemma is NOT proved here.

Provenance: the fixed-pole perspective, prior collision-cover reduction, and eleven-panel specimen were developed with Codex Forge. The reviewed polar trace proof is in `<historical-folder>/POLAR-WINDOW.md` (included, sanitized, as `S4-polar-trace.md`) and its return. The maximum-radius selector and cross-sheet comparison below are new candidate arguments, not assertions that those prior reviews already checked them. No claim of literature novelty is made.

## 1. Geometry and fixed conventions

Use the actual full-plane maps of a genuine ordinary band. In one common baseline frame write its n panels as

    F_i(s,t) = b_i + t d_i + s rho_i(t) e_i,
    d_i = a_i-b_i,
    e_i = b_(i+1)-b_i,
    a_(i+1)-a_i = lambda_i e_i,
    rho_i(t) = 1-t+t lambda_i > 0,
    0 <= s,t <= 1,  lambda_i > 0.

All endpoint vectors are now centered at the genuine fixed point O of the FULL affine circuit H(x)=Qx+v. In the old frame O=(I-Q)^(-1)v; none of the translations is omitted. Thus the centered circuit is Q=Rot(Delta), and b_n=Q b_0, a_n=Q a_0. Endpoint n is the last panel's terminal copy, not a wraparound gluing in the planar strip.

Take the normalization

    det(e_i,d_i)<0 for every i,
    -2*pi < Delta < 0.

The opposite case is obtained by a single global interchange of physical rims and reflection of the developed plane, with all labels and maps transported together. It is not permission to relabel a rim independently at different cuts.

Retain the existing source bounds |q_i|<pi and Delta=sum q_i. Do not assume all q have one sign or that projected corners are nonacute.

Assume precisely the prior radial-support condition

    det(b_i,e_i)<0 and det(a_i,e_i)<0 for all panels.       (R)

The same condition holds at both endpoints of the incoming or outgoing horizontal edge. It is unchanged by applying Q to a circuit copy. R implies no material point equals O and each fixed-height horizontal section advances strictly clockwise in polar angle.

The already reviewed winding argument, INCLUDING the virtual final hinge into the next circuit, gives the real longitudinal polar sweep Delta. In particular its magnitude

    L = -Delta

satisfies 0<L<2*pi. This is an equality of real lifts, not merely congruence of rotation matrices. The subarguments used here precede the old invocation of W and do not depend on it.

## 2. A maximum upper vertex forces a radially inward hinge

Choose k maximizing ||a_i|| over the n upper endpoint copies. A maximum exists because this is a finite nonempty set. Radius is unchanged under Q, so the virtual neighboring copies at the cut have radius at most this maximum too.

Write

    a=a_k,
    f=a_k-a_(k-1),
    e=a_(k+1)-a_k,
    g=d_k.

For k=0 or k=n-1, use the appropriate Q or Q^(-1) copy for the neighboring vertex. Both f,e are nonzero in an ordinary band.

The two maximum inequalities give

    a dot f >= ||f||^2/2 > 0,
    a dot e <= -||e||^2/2 < 0.                         (1)

R gives det(a,f)<0 and det(a,e)<0. Rotate coordinates once so a=(r,0), r>0. Then (1) and R say

    f_x>0, e_x<0, f_y<0, e_y<0.

Consequently det(f,e)<0. This convexity of the selected developed corner is DERIVED, not assumed globally.

Coherent panel orientation supplies

    det(f,g)<0 and det(e,g)<0.                         (2)

For the incoming panel, use d_k=d_(k-1)+(lambda_(k-1)-1)e_(k-1) and f=lambda_(k-1)e_(k-1). Thus (2) follows from its actual orientation, including across the virtual wrap.

Set K=-det(f,e)>0. Cramer's rule gives the exact decomposition

    g = A(-f) + B e,
    A=det(g,e)/K>0,
    B=-det(f,g)/K>0.

Using (1),

    a dot g = -A(a dot f)+B(a dot e)<0.                (3)

Along the selected straight hinge x(t)=b_k+t g=a-(1-t)g,

    x(t) dot g = a dot g-(1-t)||g||^2<0.

Its radius is therefore strictly DECREASING with physical height. An elementary squared-distance identity proves the same fact without differentiating:

    ||x(t2)||^2-||x(t1)||^2
      =(t2-t1)[2 a dot g-(2-t1-t2)||g||^2]<0

for 0<=t1<t2<=1.

This proves existence of a radial-inward seam from R. The choice uses positions, not a ranking of q magnitudes, and uses no collision test.

## 3. Why an inward seam replaces the narrow window

The following lemma applies to ANY seam with strictly decreasing radius under the normalization of Section 1. Section 2 supplies one.

Let alpha(t) be a continuous polar argument of the selected seam. R puts that entire straight segment in one open halfplane through O. Its angular range has width omega<pi, and alpha is monotone or constant. No inequality omega<2*pi-L is required.

At each height t, the opened strip's longitudinal polar lift takes every value in

    [alpha(t)-L, alpha(t)]

exactly once in the glued longitudinal coordinate.

### 3.1 Physical rays may have two eligible height components

Fix a physical unit ray v and a representative angle phi. For each integer j, its possible lifted argument is phi_j=phi+2*pi*j. The heights with that lift are exactly

    I_j={t in [0,1] : alpha(t) in [phi_j,phi_j+L]}.

Each nonempty I_j is a closed interval, possibly a point, because alpha is continuous and monotone. At a fixed t, two different lifts cannot occur: L<2*pi.

There are at most two nonempty I_j. The total lifted angular range has width L+omega<3*pi<4*pi, too short to contain three representatives separated by 2*pi. A constant alpha has at most one eligible component.

This explicitly permits the wide-seam case rejected by W.

### 3.2 Radius decreases within each component

For a fixed lift, the reviewed trace argument still applies. At a point r v in panel i,

    r_i(t)=[det(b_i,e_i)+t det(d_i,e_i)]/det(v,e_i).

R gives det(v,e_i)<0 on an eligible panel. The slope is strictly negative because det(e_i,d_i)<0. The panel's actual intersection with this ray is described by affine inequalities in height; its interval is closed. Its assigned lift cannot jump: the WHOLE panel lies in its own strict radial halfplane of angular width pi. Thus each panel belongs to at most one lift of this ray, even without a global W window.

At transitions for the same lift and height, strict longitudinal polar order gives the same glued material point. The finite affine radius pieces agree there. The already reviewed hinge/zero-transition argument then gives strict decrease through the whole I_j. No common window for different lifts is used in this step.

### 3.3 The seam orders the jump between components

Suppose there are two nonempty components, ordered as

    I_left=[a,b], I_right=[c,d], b<c.

Their facing endpoints b,c are seam points: the eligibility constraints become equality at the gap. If b were at the material-height endpoint 1 there could be no later component; if c were 0 there could be no earlier component. Equality of alpha with an endpoint of [phi_j,phi_j+L] means the longitudinal point is either the root seam or its final Q image.

Both copies have the same radius. Therefore

    r_left(b)=||x(b)||,
    r_right(c)=||x(c)||.

The selected seam's strict radial decrease gives

    r_left(b)>r_right(c).

Since the radius is decreasing within each component,

    every radius attained on I_left > every radius attained on I_right.

This also handles singleton components. The two components cannot touch at a common height because that would require L>=2*pi.

Thus two different physical heights never yield the same planar point, even when their lifted arguments differ by a full revolution. At the same height L<2*pi and strict polar advance already give uniqueness. The entire ordinary strip is injective after only the intended adjacent-hinge identifications.

**Candidate ordinary theorem: R alone guarantees some safe original seam. W is removed.**

This proof controls middle-panel collisions as well as end panels. The seam comparison orders disconnected height components; it does not assert that all collisions must involve the end panels.

## 4. Original triangles and one cut for all positive trims

Use the original full-plane source maps, which are defined independently of trim or safety. Denote original centered hinge endpoints by L_i,U_i and upward vectors G_i=U_i-L_i. Require the prior RF support tests with any nonzero forward horizontal reference on each original facet:

    det(L_i,e_i^ref)<0 and det(U_i,e_i^ref)<0.            (RF)

Every positive trim has nonzero lower and upper edge lengths, even for an original triangular facet, and inherits R. The pole, Delta, full maps and circuit copies are fixed.

There are two ways to finish. Independent choices at successive trim depths can feed the already checked finite-seam ordinary-to-closed reduction, because here the per-depth safe states are PROVED. For an explicit unchanged source cut, the following stronger argument avoids conflating those choices.

### 4.1 Choose a single eventually extremal index

For trim depth delta, the upper endpoint is U_i-delta G_i. Its squared radius is

    f_i(delta)=||U_i||^2-2 delta(U_i dot G_i)+delta^2||G_i||^2.

Choose a lexicographically maximal coefficient triple

    (||U_i||^2, -2 U_i dot G_i, ||G_i||^2).

Finite comparison of these quadratic polynomials shows that this one index k maximizes f_i(delta) for every sufficiently small delta>0. For each competitor, the first unequal coefficient controls the sign near zero; if all coefficients agree, the values tie. Take the minimum of finitely many positive thresholds.

Section 2 applies to every sufficiently small nondegenerate trim at this SAME k. Its trimmed upward vector is the positive multiple (1-2delta)G_k. Dividing the strict inward inequality by that positive factor gives

    (U_k-delta G_k) dot G_k<0.

Letting delta tend to zero in this elementary affine expression yields

    U_k dot G_k<=0.                                    (4)

No strictness at a collapsed full upper rim is assumed. No map family is selected by a limit.

### 4.2 Weak endpoint inequality gives strict radius order on the full hinge

G_k is nonzero because its physical vertical component is h>0. For 0<=t1<t2<=1, the squared-radius identity in Section 2 remains strictly negative using (4): 2-t1-t2>0. Thus the FULL original hinge radius is strictly decreasing, even if the endpoint derivative at t=1 is zero.

Its retained subsegments are likewise strictly decreasing. At every positive trim, the same cut k therefore satisfies the inward-seam argument of Section 3, whether or not it remains a maximum-radius endpoint at that larger depth. The same full maps are safe on all those trims.

Any full-face interior overlap would survive into a small trim under those unchanged maps. Hence full original face interiors are disjoint. Existing whole-hinge gluing and the cut-surface assembly yield the existing continuous facewise-isometric final development at this original cut. No external ordinary-band theorem is assumed.

**Candidate full-source theorem: RF alone guarantees an original safe seam.**

This does not upgrade full-source boundary contacts to global boundary injectivity. It preserves the existing lateral-only/static scope.

## 5. Exact specimen that the old windows all miss

The new specimen was proposed by a floating search, then checked independently with the existing outward rational arithmetic. Let

    top = conv{(-7,-3),(4,-10),(-3,11)},
    bottom = conv{(-14,5),(-5,-13),(9,-16),(13,-14),(10,18)},
    h=1/10.

The actual cyclic ordering is generated by the preserved source prototype, not assumed to be the display ordering above. The independent supporting-plane enumeration gives ten maximal facets: two caps and eight distinct lateral triangles. Neither projected rim contains the other.

For the ordinary trim delta=1/100, the exact verifier establishes:

- all q are negative and every shifted T is positive;
- D-m-pi>1.38, so no cut satisfies the old two-small-budget test;
- the unused angular gap is positive and less than 0.022 radians;
- EVERY old seam window fails, by more than 0.07 radians already at this ordinary trim;
- all original RF support tests are strict, with determinant magnitude greater than 0.018 in the chosen reference vectors;
- the ordinary upper endpoint at cut 4 is the unique maximum-radius endpoint, with a squared-radius gap greater than 1/4;
- its FULL original upper endpoint obeys (U_4-O) dot G_4 < -158;
- independent pairwise separating-axis checks confirm ordinary cut-4 safety: 7 retained-neighbor checks and 21 strict nonadjacent separations.

The source has no nonacute-corner restriction; its triangular top has acute corners. The new candidate argument does not require that restriction. All eight original lateral facets are triangles, so the full-source extension is exercised rather than merely mentioned.

The exact certificate proves finite hypotheses and the independent ordinary safe-cut control. **The new paper theorem**, pending review, supplies the inference to full-source safety from RF and the verified full inward hinge. It is not a Python proof of the universal theorem.

## 6. What this would leave to prove

The prior exact algebra separates the covered small-budget class from

    D-m>=pi, D+E<2*pi.

Every residual source has nontrivial rotational holonomy. After the single global rim/orientation normalization above, the strongest next source-geometric claim to test is:

> **Does every genuine residual two-rim convex source satisfy RF about its actual holonomy fixed point?**

Equivalently in this normalization, if z_i is the actual affine physical-height function transported through the i-th face map, is

    z_i(O)>1 for every original facet i?

This equivalence is algebraic: det(U_i-O,e_i)=det(e_i,G_i)(z_i(O)-1). With det(e_i,G_i)<0, the upper RF inequality is equivalent to z_i(O)>1; the lower one follows because its height is 0.

No fiction of a common 3D point of height z_i(O) is intended. These are different affine height extensions at the same developed planar point.

If this source-pole claim holds, it combines with Sections 2-4 and the small-budget result to give safe-cut existence throughout the normalized two-rim model. It would resolve that model's residual collision-cover problem without separately controlling every collision interval.

If it fails, a valid residual source violating it is NOT by itself a counterexample to 7.15. It identifies the exact remaining class where the radial route does not apply. A disproof of safe-cut existence still requires a valid source whose every original cut is unsafe. No claim about caps, continuous unfolding motion, every reading of 7.17, or Durer follows automatically.

The source-pole claim is not proved here. This pass aims to replace two unresolved radial availability conditions with one, not to rename that last condition into a hypothesis and call the entire conjecture solved.

## 7. Evidence and limitations

New exact finite controls: 14/14 test methods pass. They include the local maximum cone identity, reversal/zero controls, both seam-angle directions, two separated height components, the endpoint-derivative zero boundary, the actual source/cut selection, all old windows failing, and rejection of the wrong cut or discarded circuit translation. The source certificate reproduces byte-for-byte on rerun.

The first small algebra suite failed because the new module was not yet present. The certificate first exposed a missing reverse-division implementation in the inherited interval class; using an exact interval numerator repaired that API call. An optional proposed squared-radius margin of 1 was too strong: the actual rigorously positive gap is about 0.26238. The final certificate checks a conservative bound of 1/4. The full derivative is below -158. These are recorded numerical guard adjustments, not changes to the geometric premise or proof.

A separate 350-source floating exploratory pass found 127 sources passing its residual filter; all 127 passed its radial diagnostics and no selected cut was detected unsafe. Twenty had no old window; one of those was non-nested and became the exact fixture. These counts are not universal evidence, exact absence claims for the other samples, or a proof of the source-pole lemma. No Lean run or historical 69-suite rerun is claimed.

The original certificate and arithmetic dependencies are copied unchanged from the mounted earlier packet. New outputs are not represented as independently re-proved arithmetic primitives.

## 8. Next recipient and specific review

**Codex Forge, independent mathematical reviewer. Not Letta Forge.**

Review the whole R-only safe-cut argument, concentrating on:

1. The maximum-radius vertex's two incident edge inequalities, including virtual wrapped neighbors.
2. Derivation of convexity at that selected corner and the positive cone decomposition of its hinge.
3. Separation of the two physical-ray height components without W, including both monotonicity directions of alpha, singleton components, and radial hinges.
4. The fact that component endpoints facing a gap are copies of the same seam at their respective heights, so their radii can be compared.
5. Eventual quadratic maximization and the weak full-endpoint inequality for triangles, preserving one original cut and one map family.
6. The exact specimen where ALL old W cuts fail but the new selected hinge succeeds.

Return acceptance at exact scope, or the first false/unjustified step and a counterexample where possible. Do not silently repair a failure. If this argument holds, then aim subsequent source mathematics at RF availability, not another narrow-seam lemma.

No new Lean implementation in this review pass. No production edits, contact between the Forge instances, publication/contact, scheduler changes, caps, motion, Cartography, or numbered Physics. Suggested return: `<historical-folder>/CODEX-FORGE-RETURN.md`.
