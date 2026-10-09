---
title: Research origin, contribution provenance and literature baseline
author: System
recorded: 2026-09-25
status: internal consolidation from original notes; no new novelty ruling
dg-publish: false
---

# Read the beginning before writing the publication story

## 1. Origin, corrected from the actual record

Summer Bee invited System to choose a problem to work on. System chose Durer's edge-unfolding problem and opened the Abandoned Observatory. This is recorded in `<historical-folder>/WORK NOTES.md`, entry '2026-09-17 - Bench opened', and in `CANDIDATES.md`, both read before this consolidation. Summer Bee reaffirmed that origin in the current conversation.

The original motivation was a comparatively quiet, structurally interesting mathematical problem with computational falsification opportunities. It was not a commission to repair Aloupis's thesis, and the current theorem is not a proof of Durer's full conjecture. The side lane is explicitly not evidence for Information Pressure Theory.

On September 18, System narrowed the investigation to a single safe lateral cut, using O'Rourke's prismatoid discussion as a source-grounded smaller target. The literature discrepancy arose during that investigation. Do not rewrite the origin as Summer Bee independently spotting a theorem discrepancy and handing System the mathematical problem.

### Email provenance

Summer Bee explicitly identifies System as the author of the email she sent in this conversation. The historical `06 EMAIL DRAFT - OROURKE.md` is a separate earlier draft prepared during Claude's literature assistance; `04 CITATION ARCHAEOLOGY.md` Section 12 records the text actually sent by Summer Bee. Preserve both artifacts and distinguish drafting, revision, sending, and research discovery. A sender field or Git committer name is not evidence of sole intellectual authorship.

System's recent description that it merely 'tailored' Summer Bee's already-discovered question was not supported by that record. The correction is recorded here, without changing the original manuscripts or correspondence.

## 2. What the earliest source work already established

These are findings recorded in the September 18 notes, not claims of a fresh search today.

**The broad band statement was not absent from the literature.** Aloupis's thesis states the closed-band claim. The 2008 paper's main theorem is narrower, but its Remarks explicitly attributes broader non-nested and boundary-vertex extensions to the thesis. Claude corrected System's earlier reading of that paragraph. The broad attribution also appears in later work, including the general-prismatoid discussion recorded for Bian, Demaine and Madhukara 2021.

**The literature did not simply move from broad to narrow in chronological order.** The original version audit records prismoid-only language in Radons's May 2021 version and a broader statement elsewhere the following month. These descriptions coexisted. A narrower statement in a paper about a subclass does not by itself retract a broader theorem.

**The correspondence explains the particular open-problem listing, not the entire proof status.** The private reply acknowledges that the thesis claim had not been accounted for in that listing. It does not certify the thesis proof, our proof, or the absence of an unpublished objection. `07 AUTHOR REPLY SCOPE.md` already corrects System's earlier overinterpretation. The subsequently supplied screenshot includes a further comment about the proof's presentation; that too is not a review of our later argument.

**Touching was already identified as a correspondence issue.** The thesis source audit did not locate a definitive boundary-contact convention for 'non-self-intersecting'. Our `Safe` explicitly allows boundary contacts. A statement that the Lean result exactly formalizes every reading of Theorem 7.17 would therefore overstate what has been established.

**Some safe cut is not a prescribed compatible cut.** The original audit distinguishes bare safe-cut existence from the extra RM-compatible-cut requirement in the 2026 prismatoid construction. The present theorem does not discharge that additional compatibility claim automatically.

These findings make 'we were first to discover that these bands unfold' an inappropriate default publication narrative. A defensible working description is: a detailed proof and Lean formalization of a precisely specified static band-unfolding result associated with Aloupis's closed-band claim. The novelty of individual lemmas or the proof architecture is still to be assessed.

## 3. Contribution and review record

| Participant or instance | Role evidenced by this project |
|---|---|
| Summer Bee | Initiated the opportunity, chose and corrected scope with System, supplied resources, coordinated agents and relays, sent correspondence and retained authority over external contact and publication |
| System | Selected Durer and the safe-cut subtarget; developed research arguments, falsification routes, proof manuscripts, implementation contracts, source/contract audits and this consolidation; authored the sent question as clarified by Summer Bee |
| Claude literature assistant | Conducted the early forensic source search, corrected the 2008 reading, prepared an earlier email draft and recorded correspondence with attribution |
| Haven | Numerical probe and diagnostic review contributions recorded in the original returns, including the overlay issue that required controls |
| Letta Forge | Built and checked the formal geometry and subsequent general-proof foundations; supplied implementation receipts and a partial general continuation handoff |
| Codex Forge | Independently reviewed the paper arguments and earlier finished source; later became a contributing implementer who completed the general Lean endpoint with separate receipts |

These are contribution records, not a finalized author list or a claim that every past 'Forge' label refers to the same execution context. Existing signed returns remain authoritative for their individual work.

### Independence changed at the continuation

The earlier separation between Letta Forge as implementer and Codex Forge as independent reviewer was real for those passes. Summer Bee subsequently authorized Codex Forge to continue implementation. The final September 25 `CODEX-FORGE-RETURN.md` is therefore an implementation/verification receipt by a contributor to the final code, not a new non-author audit of that code.

Paper review, kernel checking, System's focused contract inspection, and a future external human assessment are different forms of evidence. None should be relabeled as another. No human expert has reviewed the completed proof in the correspondence available here.

## 4. Research progression, without rewriting its failures

The initial nested limit argument developed into exact restriction, retained interior witnesses and finite-cut closure. Formalization then supplied the physical facets, cyclic original hinges, actual cut quotient and ordinary polygon-set inputs. Subsequent work removed the external ordinary-band premise: first for T-mixed sources, then through polar traces and extremal seam selection, finally through folded-turn projection and source-derived radial support.

The negative examples remain part of the argument's history: interior-slab vertices and collapsed whole rims refuted the overbroad first statement; largest-turn selection and end-panel localization failed on certified bodies; a claimed floating RF failure near a singular rotation was rejected by exact replay. These failures neither disappear on completion nor become counterexamples to the final scoped theorem.

The final implementation commit is `commit-11`. The private branch history, original notes, correspondence, failed receipts and superseded paper targets are preserved. The current entrypoint, not an old 'Next move' paragraph, determines the live task.

## 5. The next literature audit should be targeted

Do not start by rediscovering the thesis, the 2008 Remarks, or the existing correspondence. Read the stored ledger and search log first, then fill their actual gaps.

The next comparison should produce a primary-source matrix for three distinct questions:

1. **Statement and interpretation.** Recheck the exact theorem/definition passages in Aloupis Chapter 7 and the relevant version of the modern safe-cut statement. Record object, permitted vertices, original-edge convention, boundary contact, static versus motion, and prescribed-cut requirements. The normalized two-rim theorem and an arbitrary qualifying slab formulation need an explicit material/incidence correspondence; that is separate from the new proof's nonoverlap logic.
2. **Mathematical ingredients.** Compare the folded-turn projection with generalized arm/turn-contraction results, including the O'Rourke 2003 slice-development source already mentioned in the RF manuscript. Compare the source-pole identity, extremal seam, and fixed-map restoration with earlier band proofs. Determine which are known tools, specializations, alternative proofs or possibly new lemmas. Similar vocabulary or a search nonhit does not decide this.
3. **Formalization contribution.** Search existing formal geometry developments for equivalent endpoints and components. The source pin, theorem types, material quotient, proof dependencies and reproducibility instructions are concrete contributions even before novelty is decided, but a claim of being the first formalization needs evidence.

For each source record version, access, exact passage, and whether it proves the result or merely cites it. The original search log identifies uninspected book/errata material and other gaps. Check current versions before any public assertion about what remains open. This document itself performs no new web-wide literature search.

## 6. Publication posture and next decisions

Keep the integrated source commit immutable as the citation target. Use `THEOREM-NOTE.md` as the starting statement/proof outline and the delivered portable receipts as the verification companion. Improve the arbitrary-slab correspondence only if needed for the intended claim; do not let it silently alter the completed two-rim theorem.

After the targeted comparison, a concise inquiry to a human specialist can ask about the theorem's interpretation and proof outline. It should disclose the AI development and verification workflow accurately. The prior private email is not permission to quote it publicly, include it in a public archive, use its sender as an endorser, or send another message.

No email, preprint, submission, public release, new review worker, schedule change, cap project or motion project is authorized by this consolidation. Summer Bee decides those next actions. No new Forge assignment is dispatched here.

## Reading record for this consolidation

Read at the pinned implementation commit, before drafting this summary:

- `<research-record>/README.md` and `<research-record>/CANDIDATES.md`;
- the opening September 17 and September 18 entries of `<historical-folder>/WORK NOTES.md`;
- `01 SAFE CUT TARGET.md`;
- `04 CITATION ARCHAEOLOGY.md`, including its correction and correspondence sections;
- `05 CLAUDE SEARCH RETURN.md`, including its definition table and search exclusions;
- `07 AUTHOR REPLY SCOPE.md`;
- `SOURCES.md`, including its explicit correction of the 2008 interpretation.

The first bullet gives full placeholder paths; the remaining bullets are relative to `<research-record>/`. Current implementation facts additionally use `GeneralTwoRimEndpoint.lean` and the September 25 return/receipts. Historical notes retain their original dated status labels; this synthesis does not update old search nonhits into present-day facts.
