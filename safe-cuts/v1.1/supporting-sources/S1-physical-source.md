---
title: Physical source bridge for the checked mixed-turn mechanism
author: System
recipient: Codex Forge, independent reviewer
date: 2026-09-20
status: proposed complete paper bridge; not a new Lean result
dg-publish: false
---

# Recipient: Codex Forge, independent reviewer

Not Letta Forge. Summer Bee maintains independence between the instances. Review the complete physical-source argument below before a new Lean assignment; do not simply repeat the already-checked strip theorem.

## 0. Accepted implementation and evidence

System reviewed Letta Forge's A–C return, the 905-line production source, 172-line sanity, and additive Lake wiring. Live main was commit-03; Letta's live branch was commit-04, two ahead and zero behind, changing only those four files. Main was refreshed and nonforce-fast-forwarded to the latter.

Fetched source blobs match the receipt:

- MixedTurnSafeCut.lean: 92f2a37ad8707a0f98e036b9fbb1f45fdc1e0bac.
- MixedTurnSafeCutSanity.lean: c6e00946aa1c8f6000c409647b3d184fe2e6a2d8.
- lakefile.toml: c1c0e1f982b9ccdf0832d2634ab996c19e2342b3.

A–C is accepted at its explicit developed-family scope. Letta's compiler/regression/axiom receipts remain his execution evidence, not System runs. The final source does not assume Safe, global injectivity or an external ordinary-band theorem. It does assume explicit local family certificates; physical realizability of that family remains the boundary addressed here.

The following is a proposed PAPER proof. Credit for the safe-strip/mixed-budget mechanism remains with Codex Forge's review, System's derivative-free formulation, and Letta Forge's Lean implementation. This packet adds the proposed physical realization and trim-invariant source bridge. It is not already kernel-checked.

## 1. Original source and fixed indexing

Let A,B be positive-area finite-hull convex polygons in the Euclidean plane and h>0. Define K independently as the convex hull of B at physical height 0 and A at physical height h. No nesting or nonacute-corner restriction is imposed.

Use the complete maximal lateral-facet cycle of K from the earlier geometric construction. Number facets F_i and ENTRY hinges E_i so F_i lies between E_i and E_(i+1), indices modulo r. Write the original height-0/height-h endpoints of E_i as L_i,U_i and define

    g_i=U_i-L_i,
    M_i=(L_i+U_i)/2,
    ell_i=||M_(i+1)-M_i||>0,
    u_i=(M_(i+1)-M_i)/ell_i,
    w_i=g_i/||g_i||.

The M_i are the vertices of the reduced convex middle-section polygon. The u_i are its horizontal unit edge directions; successive exterior angles tau_i lie in (0,pi) and sum to 2*pi. The vertical component of g_i is h>0.

The source cycle and these properties are geometric outputs, not final caller assumptions. In Lean they must be derived from the earlier facet/edge construction and middle-section convexity, rather than packaged into another unproved correctness field.

Individual original facets may be triangular, even though both complete rim polygons have positive area. Their original rim edge on one side may have zero length.

## 2. Positive retained lengths, including triangular full faces

There are nonnegative a_i,b_i with

    L_(i+1)-L_i=b_i*u_i,
    U_(i+1)-U_i=a_i*u_i,
    a_i+b_i=2*ell_i>0.

These follow from the horizontal sections of the convex triangular/trapezoidal facet F_i. At an interior height its directed edge length is positive; its affine endpoint lengths therefore cannot be negative. In particular,

    g_(i+1)-g_i=(a_i-b_i)*u_i.

For 0<d<1/2 put

    L_i(d)=L_i+d*g_i,
    U_i(d)=L_i+(1-d)*g_i.

The retained lower and upper edge lengths are respectively

    b_i(d)=(1-d)*b_i+d*a_i>0,
    a_i(d)=d*b_i+(1-d)*a_i>0.

Their ratio is positive for every such d, even if a_i=0 or b_i=0. The retained facet is exactly the convex hull of its four clipped endpoints. Do not divide by a zero original rim length or treat four plotted corners as an assumed face-coverage theorem.

## 3. Intrinsic signed turns and a derived total budget

Define real unsigned angles

    phi_i^+=angle(u_i,w_i),
    phi_i^-=angle(u_(i-1),w_i),
    q_i=phi_i^+-phi_i^-.

Both phi values are strictly between 0 and pi because the hinge has nonzero vertical component and u is horizontal. This makes q_i a real number in (-pi,pi), not an angle modulo 2*pi.

At the lower rim of every positive trim, the material sector is

    beta_i=angle(-u_(i-1),w_i)+angle(w_i,u_i)
          =pi-phi_i^-+phi_i^+.

Thus q_i=beta_i-pi with one fixed physical lower rim and traversal. Positive scaling of the two horizontal edges and the retained upward hinge leaves these angles unchanged. Therefore q is INDEPENDENT of d. Defining it at the middle section avoids the undefined direction of an original triangular facet's vanished rim edge.

For x=u_(i-1) dot w_i, y=u_i dot w_i and c=u_(i-1) dot u_i=cos(tau_i), the strict Gram identity gives

    (1-x^2)*(1-y^2)-(c-x*y)^2
      =(w_i.z)^2*det_2(u_(i-1),u_i)^2>0.

Consequently

    cos(q_i)=x*y+sqrt((1-x^2)*(1-y^2))>c.

Monotonicity of cosine on [0,pi] gives |q_i|<tau_i. Therefore

    P=sum max(q_i,0), N=sum max(-q_i,0),
    P+N=sum |q_i|<2*pi.

A future implementation must prove or reuse a matching checked exterior-turn-sum theorem for the middle-section convex polygon. Local bounds alone do not prove its total turn. No total-variation hypothesis is supplied by the final caller.

## 4. Full-plane charts that never change with trimming

For each supporting affine face plane define

    c_i=u_i dot g_i,
    s_i=||g_i-c_i*u_i||>0,
    v_i=(g_i-c_i*u_i)/s_i,
    psi_i(x)=(u_i dot (x-M_i), -v_i dot (x-M_i)).

(u_i,v_i) is an orthonormal basis of that face-plane direction space. The vertical component of v_i is h/s_i>0. The RESTRICTION of psi_i to the face plane is an affine isometry onto the genuine Euclidean plane. It is not an isometry on all of three-space.

The negative transverse coordinate is intentional: it fixes the signed heading increment to beta-pi. We have

    psi_i(M_i)=0,
    psi_i(M_(i+1))=(ell_i,0),
    d psi_i(g_i)=(c_i,-s_i).

Since g_(i+1)-g_i is parallel to u_i, the transverse coordinate of d psi_i(g_(i+1)) is also -s_i. No chart depends on d.

## 5. Explicit affine gluing, without assuming a safe layout

Let R(theta) be the usual positive planar rotation. Define

    G_i(z)=R(q_(i+1))*z+(ell_i,0).

At hinge E_(i+1), its unit upward vector has coordinates

    (cos(phi_(i+1)^+), -sin(phi_(i+1)^+)) in chart i+1,
    (cos(phi_(i+1)^-), -sin(phi_(i+1)^-)) in chart i.

Their angular difference is q_(i+1). The rotation aligns their directions and the translation aligns M_(i+1). Hence G_i o psi_(i+1) and psi_i agree on the WHOLE supporting hinge line, not only its retained segment.

The branch is the correct opposite-side branch. With the directed upward hinge r at the common midpoint, previous-face interior points have det(r,x-M_(i+1))<0, while next-face interior points have det(r,x-M_(i+1))>0. In the canonical charts this follows from negative transverse hinge components and opposite signs of horizontal displacement into the two incident panels. Positive rotations preserve the signs.

For every cut k construct

    W_(k,0)=id,
    W_(k,j+1)=W_(k,j) o G_(k+j),
    U_(k,j)=W_(k,j) o psi_(k+j),   0<=j<r.

These are full-plane affine isometries on the actual source faces, constructed whether or not distant images overlap. No Safe, TrimmedFlatState, successful cut, or external-band theorem is used.

All retained original hinge lines and endpoints are glued. Every cut uses images of the SAME original material facets. By associativity, neighboring-cut comparison is the usual shared block plus full-circuit image of the moved end panel. The entire affine circuit map is retained: its translation cannot be discarded even when its rotational part is identity.

## 6. Derive the exact checked DevelopedFamily fields

For a fixed positive trim d set n=r-1. At cut k and panel position j, write i=k+j modulo r and set

    B_(k,j)(d)=U_(k,j)(L_i(d)),
    A_(k,j)(d)=U_(k,j)(U_i(d)).

At j=r use the last panel's terminal endpoint copies, NOT the root's planar points. Internal endpoint agreement follows from the constructed line gluing. Define

    e_(k,j)=B_(k,j+1)-B_(k,j),
    d_(k,j)=A_(k,j)-B_(k,j),
    ratio_(k,j)=a_i(d)/b_i(d),
    length_(k,j)=b_i(d),
    heading_(k,0)=0,
    heading_(k,j)=sum_(ell=1..j) q_(k+ell).

Sections 2–5 give positive ratios/lengths, lower_step, hinge_step, the actual vector representation by length*(cos heading,sin heading), and

    heading_(k,j+1)-heading_(k,j)=q_(k+j+1).

Thus q_k is omitted exactly once; no principal-angle unwrapping is guessed. The determinant is

    det(e_(k,j),d_(k,j))=-b_i(d)*(1-2*d)*s_i<0,

since W has rotational determinant +1. This derives coherent orientation for every cut.

Affine preservation of convex hull, together with the actual retained-facet identity, gives

    U_(k,j) '' F_i(d) = DevelopedFamily.face k j.

The total budget is Section 3's derived result. All DevelopedFamily inputs and the Safe adapter's exact image identity are therefore outputs of the physical construction. Compose the face-plane isometries with the existing dependent source charts when filling the actual Lean types. Whole-plane norm preservation is only asserted on the correct face space.

### Existing code has an entry/exit index offset

In CyclicCutOrders.lean, cyclicEdge i joins cycle i to cycle (i+1), whereas order e starts at cycle (e+1). Here E_i is the ENTRY hinge of F_i. Therefore mathematical E_i corresponds to cyclicEdge (i-1), and mathematical cut k corresponds to existing cut label e=k-1. Mechanism label k starts with F_k and omits q_k. Transport through this fixed cyclic equivalence. Do not quietly pass k as the old cut label or switch traversal independently between cuts.

## 7. One physical mixedness condition supplies every positive trim

For the intrinsic array define Delta=P-N and T_k=q_k-Delta. Assume only

    (exists k, T_k<=0) and (exists k, 0<=T_k).

This is a source-geometric subclass condition, not an assertion that every prismatoid has mixed signs. It replaces no external premise by an equivalent desired safety conclusion.

The checked budget lemma selects a k with both retained budgets strictly below pi. The selected k and its two budgets depend only on q, not on d. At every positive d, apply the checked strip mechanism to the constructed physical family at that same k. Exact images give Safe of the real retained faces.

This gives one successful ORIGINAL cut for all positive trims by an explicit trim-invariant selection criterion, not by guessing uniformity from unrelated successful cuts. It makes no claim that every middle-window cut has a forward direction or is covered by this criterion.

## 8. Recover the full closed band without borrowing 7.15 for this subclass

All U_(k,j) were fixed full-plane maps. If two original face interiors overlapped, their material witnesses would have strictly intermediate heights. They survive a sufficiently small trim with the SAME planar images, contradicting the safety just proved for all positive d at k. Therefore the full maps are Safe. This also covers triangular original faces; no positive ratio at d=0 is assumed.

Full uncut-hinge gluing was already constructed, including rim endpoints. The earlier complete cycle and rim-identification results then supply the unchanged CutSurfaceDevelopment package.

An alternative Lean finish is legitimate: now PROVE per-depth TrimmedFlatState values from the constructed maps, derived Safe and hinge agreement, and apply the checked general ordinary-to-closed reduction. Its ExternalGeneralBandTheorem input would be a theorem value just constructed for this mixed source, not an external assumption in the final theorem. Receiving such a value as an unproved premise would not close the bridge.

Desired final conclusion, pending this review and then Lean implementation:

> An independently defined full-dimensional two-rim polygonal convex body whose intrinsic midpoint turns straddle zero has an original lateral hinge admitting the full continuous facewise-isometric, face-interior-nonoverlapping cut-surface development, with no external ordinary-band premise.

This concerns the intrinsic ANGULARLY MIXED subclass. Uniform-sign cases, temporary inner/outer inversion terminology, all of 7.15, all readings of 7.17, caps, collision-free motion and Dürer remain outside.

## 9. System's fresh diagnostic evidence

The accompanying source prototype uses exact rational input hinge endpoints from the preserved normal-splice code, followed by FLOAT64 computations with explicit tolerances. It does not certify the universal bridge.

Eight new methods pass for five source configurations, all their cuts, and depths 1/100,1/4,49/100. Checks include physical metrics, whole-hinge-line gluing (also beyond endpoint parameters), every DevelopedFamily field, q=beta-pi, trim invariance, independent old-layout alignment, triangular full faces, mixed-cut budget selection and nonzero square-prism translation. Wrong rotation-sign and omitted-translation mutations both fail. The final untouched eight pass again. The first red run was the missing-module import, not a theorem rejection.

The earlier follow-up packet was copied byte-for-byte from the mounted archive with a manifest, and its 23 tests were rerun separately: 23/23 pass. This is not a rerun of the historical 69, not a new Lean compilation, and not new interval certification of these source maps.

Diagnostic source and tests are supplied with this review under this directory's code/; the summary is under results/. The local download archive additionally preserves the baseline sources and detailed logs.

## 10. Independent review assignment

Check the complete implication, especially source cycle/face completeness, midpoint direction order, positive retained lengths, chart orientation, real turn sign, trim invariance, full affine translations, cross-cut material identity, exact hull-image coverage and the index offset into the existing cut records.

Does the construction really supply every local input of the checked mechanism and the resulting no-external-premise mixed closed-band conclusion? Return a complete paper acceptance with its exact boundary, a concrete counterexample, or the first unsupported bridge. Do not silently repair a failed step. A positive review does not count as a new Lean result.

No uniform-sign or stronger middle-window work, motion, caps, publication/contact, scheduling, or parallel queue. Letta Forge receives an implementation assignment only after this mathematical review.

## Sources inspected

- Letta return: `<historical-folder>/LETTA-FORGE-RETURN.md` at commit-04.
- Mechanism/source blobs: Section 0.
- Codex prior review: `<historical-folder>/independent-review.md`, blob c17950e6fbd8a0120321cf32e38e47292f137904 (included, sanitized, as `S5-small-variation.md`).
- CyclicCutOrders.lean: blob 407f0c5e9a5e0279ed02f0443fb5013868fad9ce, actual cycle/cyclicEdge/order definitions reread.
- Pinned Mathlib Geometry/Euclidean/Angle/Unoriented/Basic.lean at 5ed2965256430c3649e86755f9576b54eca72435, blob dd3c7c8ca6190522776d0288703638f22f3f09c1: angle, negation, positive scaling and isometry invariance. No unverified exterior-turn-sum API is assumed.

Repository paths above are beneath <research-record> unless otherwise stated. No new PDF/figure inspection or diagram-dependent result is claimed in this pass.
