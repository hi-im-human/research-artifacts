---
title: "Author Self-Review: Safe Cuts for Two-Rim Convex Bands"
subtitle: "Draft 0.1 to draft 0.2 | Findings, changes, and verification limits"
author: "System (AI research agent)"
date: "27 September 2026"
status: author audit; not an independent review or Lean rebuild
dg-publish: false
---

# 1. Disposition

**The geometric proof architecture is retained. The manuscript required substantive exposition and scope clarifications, not just copyediting.** In the proof chain examined here I found no counterexample or false mathematical implication requiring a change to the pinned Lean implementation. This is my assessment as the manuscript's author, not an additional independent acceptance of the theorem.

The most important correction is the intermediate seam proposition. Draft 0.1 referred to a selected inward seam and a displayed group of inequalities, leaving the inherited source/circuit hypotheses and the distinction between existence and sufficiency too implicit. Draft 0.2 states those hypotheses and proves the two clauses separately: an extremal endpoint supplies an inward seam; every inward seam is sufficient. The restoration argument uses the second clause, not renewed maximality at every trim.

The rewritten source-facet proof and the strengthened explanations are new exposition. They are grounded in the existing constructor and source arguments, but have not themselves been independently reviewed or compiled as new Lean statements. No proof source, prior review, failed receipt, or draft 0.1 file was altered by this pass.

# 2. Review boundary and pins

The input manuscript was read in full: `DRAFT-01.md`, 924 lines, 54,221 bytes, Git blob `84381d7d228a4d00cbd974f36094e0f747915491`, created at `commit-15`. Its SHA-256 is `72dd201064d8b580568e53226d7c97decc74ce79960f96f2b197d2a9858fc550`. The attached PDF and source packet were also available; typesetting was not treated as mathematical verification.

The repository baseline for this pass was `commit-16`. The implementation remains pinned at `commit-11`. Earlier mathematical and formal-model reviews remain evidence about their recorded targets, not about the new prose.

The existing mathematical source route comprises the physical source manuscript, folded-turn/radial-support manuscript, polar trace manuscript, extremal-seam manuscript, and the proved small-variation argument, identified as [S1]--[S6] in the draft. I checked the manuscript's implications against those arguments. In addition, live pinned reads inspected these formal contracts:

| File | Range or declaration inspected | Purpose |
|---|---|---|
| `GeneralTwoRimEndpoint.lean` | Whole file | Exact public assumptions, set input, sign split |
| `GeneralTwoRimUnfolding.lean` | Whole file | Stored literal maps, every-positive-trim clause, zero branch |
| `OriginalFacetCertificates.lean` | Lines 1--250 | Positive normal rays, supporting halfspaces, equality with the physical hull |
| `NormalFanSplice.lean` | Lines 1--150 | Edge-ray classification, singleton support off the edge rays |
| `CutSurfaceQuotient.lean` | Lines 1--180 and 600--696 | Exact gluing relation, canonical inclusions, material projection, final record |
| `EXTREMAL-SEAM.md` | Lines 96--222 | Any-inward-seam sufficiency and its application to every trim |

The full implementation, all 73 modules, and dependency binaries were **not** recompiled or re-read line by line. No claim of a new kernel run is made.

# 3. Findings and changes

## R01. Main theorem assumptions

**Finding:** The theorem said “every input satisfying (2.1),” but (2.1) alone is the hull formula. Finite-hull status, nonempty planar interiors, and positive height were in surrounding prose rather than repeated in the theorem.

**Change:** Theorem 2.1 now states all three assumptions directly. The conclusion and permitted boundary contacts are unchanged. This prevents the theorem from being detached from the paragraph that supplied its hypotheses.

## R02. The exact cut relation

**Finding:** The description by retained-hinge identifications was accurate but did not expose the formal relation a skeptical reader would need to inspect.

**Change:** Added the characterization by equal physical location plus membership in every intervening face of the opened linear chain. Explained both directions of its equivalence to generated adjacent gluing. Equal material location alone does not reglue the chosen cut. The scope remains the explicit quotient, not a new disk-homeomorphism theorem.

## R03. Source geometry, now a proof rather than a pointer

**Finding:** Section 3.1 summarized the facet constructor without showing why all maximal facets, actual hinges, and the reduced midpoint polygon follow from the two rim sets. “Common support directions” could also be misread as requiring normals shared by both rims.

**Change:** Added Proposition 3.1 with a support-function proof. The normal set is the merged **union** of the rim edge normals. The proof derives the horizontal section, the exposed lateral face formula, supporting planes, uniqueness and completeness of facets, the shared original hinge segments, and the middle-section cycle. It explains why a zero rim run gives a triangle rather than a missing face. The strict-turn lemma becomes Lemma 3.2; existing numbered equations keep their identifiers.

**Evidence boundary:** This is an author's expanded derivation from the recorded geometry and selected formal constructors. It is not a new Lean implementation or the omitted arbitrary-slab normalization bridge.

## R04--R06. Notation, maps, and cyclic indexing

**Finding:** Draft 0.1's Markdown defined `u_i` where the subsequent proof used `nu_i`; its rendered version had corrected this separately. The transverse face-basis vector and a developed horizontal direction also used the same letter. The map composition and local cyclic relabeling were compressed, and the extra closing interpolation knot could be mistaken for another weighted edge.

**Change:** Unified the source direction as `nu_i`, renamed the transverse basis to `xi_i`, applied the previously documented article correction, displayed the map recurrence in its correct composition order, and supplied the opposite-side determinant explanation. Lemma 5.1 now explicitly assumes a nonempty finite index set and weights only the original n edges. The rooted projection sum explains the cyclic relabeling. No closing turn is deleted or counted as an extra weighted edge.

## R07--R08. The inward-seam proposition and the all-trim argument

**Finding:** Proposition 8.1 could be read too broadly when detached from its section. Its proof uses actual matching circuit copies, real heading increments, and local turn bounds, not just the inequalities in (7.2). Its wording also obscured which property survives when an endpoint ceases to maximize radius on a larger trim.

**Change:** Section 7 carries the inherited physical/circuit hypotheses explicitly and distinguishes trim-local height from original normalized height. Proposition 8.1 now has two clauses: any strictly inward seam is sufficient, and an extremal upper endpoint provides one. Section 9 invokes the sufficiency clause on all trims. Re-rooting uses the actual rotation copies, not a new arrangement of panels.

**Assessment:** The source argument already contains this distinction. This was a potentially consequential loss of clarity in the consolidated statement, not a newly found failure of the extremal-seam proof. The stronger auxiliary ordinary-strip injectivity statement is explicitly distinguished from the weaker public full-boundary conclusion.

## R09--R10. Trace and sign-transport details

**Finding:** The panel-height eligibility interval and the full positive-defect panel transport were asserted with only part of their algebra displayed.

**Change:** Added the affine ray horizontal-coordinate formula and its endpoint inequalities, explaining why a closed feasible set cannot contain a zero-radius material point. Added the transformed positive run ratio and the identity equating the reflected/reversed panel parameterization with the original one. These changes expose the denominator and sign obligations rather than replacing them with an algebra test.

## R11. Evidence and remaining-work language

**Change:** Updated draft status, the verification paragraph, source map, conclusion, and Appendix C to describe the second draft and this author audit. Prior source review, exact symbolic checks, Lean compilation, and outside review of the new manuscript remain distinct. The first draft's archive and the historical statuses remain unchanged.

## R12. Version-sensitive references

**Change:** Section 12 now records [OR26, Section 8(1)] explicitly rather than leaving the earlier listing unqualified. The corrected [OR03] version is pinned for the eventual lemma comparison. See the primary-source references below.

This was a bounded citation check, not a completed novelty audit. It does not establish priority for our theorem, individual lemmas, or formalization, and it does not turn correspondence or a literature correction into expert review of our proof.

# 4. Mathematical checklist

| Argument | Disposition and checked dependency |
|---|---|
| Physical source | Expanded the support-plane and incidence argument; positive-area rims retained |
| Local contraction | Checked the Gram expansion, nonzero vertical component, and cosine comparison |
| Full affine development | Checked map order, whole-hinge agreement, and coherent opposite-side orientation |
| Folded projection | Checked closing interval, periodicity of the absolute-value fold, both circle paths, and strictness from actual rim closure |
| Radial support | Checked half-angle identity, determinant sign, rim choice, and transport to one common pole |
| Winding | Checked real lifts and inclusion of the virtual last hinge; no inference from rotation modulo a full turn alone |
| Extremal seam | Checked both neighbor comparisons, incoming orientation, cone decomposition, and strict inward radius |
| Ray traces | Checked at-most-two eligible components, finite affine transitions, and separation across the gap at seam copies |
| Triangles and restoration | Checked fixed polynomial selector, weak limiting dot product, strict full-hinge order, and persistence of interior witnesses |
| Zero defect | Checked both variations below pi, common forward coordinate, Cartesian slope, and absence of a pole assumption |
| Positive defect | Checked one global reflection/rim swap, inverse run ratio, circuit conjugacy, and preserved orientation |
| Final scope | Same original cut and maps; full face interiors only; no caps, motion, prescribed hinge, or global boundary embedding |

The checklist is an author's proof audit. It is not a theorem prover's certificate and does not add independence to the earlier reviews.

# 5. Fresh calculations and artifact checks

`check_identities.py` performs twelve exact symbolic identity checks using SymPy 1.14.0. All twelve simplified to zero in this pass. They cover the scalar Gram expansion; the rotation half-angle matrix identity; the quarter-turn determinant sign; hinge squared-radius difference; Cramer's decomposition; straight-seam angular determinant; trim polynomial; ray radial and horizontal formulas; Cartesian trace slope; full positive-case panel transport; and its orientation determinant.

These are identity checks, **not** proofs of the geometric hypotheses, inequality signs, realizability, nonoverlap, or novelty. Denominator nonvanishing remains justified in the manuscript. The JSON records each residual and this limitation. No numerical experiment is presented as evidence of a universal theorem.

The artifact verification checks the original Markdown hash, the revised section and reference inventory, unique equation tags, mathematical delimiter balance, the generated PDF's page count, and the source/packet hashes. Rendering is inspected separately for pagination and mathematical glyphs. A successful PDF build is not a successful Lean build.

# 6. Readiness and remaining questions

**The next independent assessment should be of the mathematics and its interpretation, not another automatic compiler run commissioned because a draft was edited.** A specialist can read draft 0.2 as the current exposition, with this ledger showing exactly what changed. It should be described as an author-reviewed draft, not a submission-ready, human-endorsed final paper.

Remaining work includes the targeted literature comparison, checked explanatory figures, and a compact portable reproduction guide. These are not claims of defects in the pinned theorem. The open interpretation questions remain explicit: arbitrary-slab normalization, the thesis's exact boundary convention, and any additional cap-compatible cut requirement. A new contribution or substantive correction from an outside reviewer should receive its own attribution rather than being folded invisibly into the old record.

No external contact, publication, new agent assignment, or schedule change was performed.

# Primary-source and access record

**[OR26]** Joseph O'Rourke, *Prismatoid Band-Unfolding Revisited*, arXiv:2603.09813v3, September 18, 2026. [Version-specific text](https://arxiv.org/html/2603.09813v3), Sections 1.2 and 8(1); [version history](https://arxiv.org/abs/2603.09813). This check supports R12; it is not a review of our work.

**[OR03]** Joseph O'Rourke, *On the Development of the Intersection of a Plane with a Polytope*. [Corrected arXiv version 4](https://arxiv.org/abs/cs/0006035v4). Version history checked; detailed lemma equivalence not assessed.

**[Alo05]** Greg Aloupis, *Reconfigurations of Polygonal Structures*, Chapter 7, printed pages 119--122. [Library and Archives Canada copy](https://central.bac-lac.gc.ca/.item?app=Library&id=TC-QMM-85114&oclc_number=894086208&op=pdf). Relevant theorem text was available; page-image requests failed with cache-miss errors. No conclusion in this audit depends on an unseen thesis figure.

**[ADL+08]** Aloupis et al., *Edge-Unfolding Nested Polyhedral Bands*. [Author-hosted manuscript](https://erikdemaine.org/papers/BandUnfolding_CGTA/paper.pdf), Section 6, PDF page 18. The remarks were read in text and in a rendered page image.
