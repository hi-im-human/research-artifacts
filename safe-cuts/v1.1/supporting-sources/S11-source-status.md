---
title: Current status of the static two-rim theorem
author: System
updated: 2026-09-26
status: current reader-facing status; no new proof or compiler run
implementation: commit-11
independent-review: commit-14
dg-publish: false
---

# What is true now

Read this status together with THEOREM-NOTE.md (not included) for the current account. The theorem note remains the September 25 mathematical outline; its description of verification at that time is not silently rewritten. This separate status records the later independent review. For the development process, use the [numbered lineage](S11-lineage.md), not this summary as a substitute for original evidence.

## The result and its boundary

For the independently defined Euclidean convex hull of two finite-hull planar polygonal rims with nonempty interiors at heights 0 and h>0, an original lateral hinge can be cut to obtain the explicit continuous, facewise-isometric planar development with disjoint interiors of distinct face images. Individual lateral facets may be triangular. Boundary contacts are allowed. The raw and set-level public endpoints do not require nesting, T-mixedness, radial support, a supplied development/safety certificate or an external ordinary-band theorem.

The implementation is frozen for citation at `commit-11`, namespace `GeneralTwoRimUnfolding`, in `GeneralTwoRimEndpoint.lean`. `SameCutSameMapsResult` stores one original cut and the same full maps on every positive trim. Restricting an already safe full development also gives safe trims; this stored clause is not advertised as a separate mathematical strengthening beyond full safety.

The result does not include caps, a collision-free motion, an arbitrary-slab normalization theorem, a prescribed/RM-compatible cut, a separate slit-surface homeomorphism, global boundary injectivity or Durer's full conjecture. No literature-priority or novelty ruling is made here.

## Evidence, with authorship and chronology kept separate

| Layer | What the record supplies | Where to inspect it |
|---|---|---|
| Implementation | Letta Forge's foundations and Codex Forge's completion of the general endpoint; named target checks and explicit cache qualifications | [Codex implementation return](../evidence/S9-implementation-return.md) and its linked results; Letta's preserved return (not included) |
| Independent mathematical and definition review | Opus accepted the paper argument and the formal-model correspondence at the explicit scope | [Opus review](../evidence/S8-opus-review.md), Sections 1-2 and pre-receipt notes |
| Independent project-source rebuild | Opus reports all 73 project modules compiled into fresh outputs at the implementation pin; 356 axiom reports within propext, Classical.choice, Quot.sound | Opus Sections 3.2-3.7 |
| Independent checks on the meaning of the result | Opus's scratch Lean proofs establish nonempty planar face interiors, adjacent material gluing, restriction of safety, and an expanded set-level conclusion | Opus Section 3.4 and Appendix C |
| Integration and preservation | Implementation integrated without changing its bytes; active status separated from historical evidence | Integration receipt (not included), [lineage](S11-lineage.md), and Git commits |

Opus reused pinned Mathlib and companion-package binaries, did not rebuild those packages, and did not complete a separate `leanchecker` replay. He used direct Lean compilation rather than Lake because of a path-length problem, and did not read every large internal proof line by line. These qualifications remain part of the report. System has inspected the report and source headers; no new Lean or Python proof-verification run is claimed by this status update.

Codex's final implementation receipt is not an independent review of his own code. Opus's instance began without the development transcript and disclosed possible shared-model error. The independent review adds evidence; it is not a human expert review or a novelty assessment.

## Historical labels are not the current build status

System individually inspected the 14 headers listed by Opus. They are comments inside source modules and sanity sources that remain in the checked tree, not just separate archived diary notes. Most explicitly date themselves to September 19; several say "not compiled HERE" or "in this runtime". They record a draft/local verification posture. They are not a current failure verdict on the completed implementation.

The headers and full source files remain byte-for-byte unchanged. Their H01-H14 catalogue, literal labels, line locations and Git blob IDs are in the [source-status manifest](S11-source-status-manifest.json). The current status is the later compilation evidence above. A header's original date is not asserted to be the creation timestamp of every line in the final file.

Likewise, a historical conditional adapter can still have genuine conditional premises even though the general endpoint proves or avoids them. Do not delete its hypotheses or alter its definition to make an introductory comment sound current. The old `rotateCW` name and the explicitly documented counterclockwise formula are preserved as implementation provenance; the mathematics is not rotated differently to tidy a name.

The stopped 402.56-second negative-wrapper build remains a stopped run. Opus's later 1,190-second successful rebuild is a separate event. The first failed scratch check remains a failure; the later corrected success does not overwrite it. Mixed-line-ending fingerprints remain historical working-tree measurements. The new 14-file blob inventory does not claim to replace the complete 73-file fingerprint audit.

## Active writing, distinct from the archive

The current reader packet consists of this status, the theorem note and the [provenance/literature baseline](S10-contributions-and-literature.md). They are internal working documents, not a submitted paper. Future reader-facing revisions should absorb the four exposition clarifications in Opus Section 1.6 into one coherent presentation; the original reviewed manuscripts should remain untouched and linked in the lineage.

The next substantive deliverable remains the targeted literature/definition comparison, not another proof campaign or review loop. It has not been completed by this documentation pass. No new worker, external contact, publication or schedule is initiated here.

Summer Bee's preservation direction is explicit: retain what was recorded at the time, show the sequence, and write present truth separately. Before substantially revising an active document, preserve its displaced version and record why the new version supersedes it. Private correspondence stays private unless separately authorized for release.
