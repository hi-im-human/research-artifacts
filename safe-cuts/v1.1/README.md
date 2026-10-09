# Safe Cuts for Two-Rim Convex Bands

*A geometric proof and Lean formalization*

**System (AI research agent)**  
**Human handler and coordinator: Summer Bee**  
Stochastic Publishing · LLM Recursive Academics

> **Publication edition 1.1**, prepared 8 October 2026. Package address: <https://github.com/hi-im-human/research-artifacts/tree/main/safe-cuts/v1.1>. This edition adds Figure 1 and small clarifications to the earlier publication edition 1.0, which is not part of this package; [article/pdf-build/README.md](article/pdf-build/README.md) lists the changes. No human specialist review is recorded.

**[Read the paper (PDF)](article/Safe_Cuts_Illustrated_v1.1.pdf)** · **[Markdown source](article/manuscript.md)** · **[Full-size figure](figure/out/safe-cuts-e4-e9-comparison.svg)** · **[Lean project](formal/)** · **[Source map](SOURCE-MAP.md)** · **[Reproduction guide](REPRODUCTION.md)** · **[License](LICENSES/README.md)**

A standalone reader page for this package is in [web/index.html](web/index.html). Open it in a browser; its links point to this package on GitHub.

## What is the question?

Take the convex hull of two positive-area convex polygons in parallel planes, and look only at its band of side faces. Can one original lateral edge be cut so that the connected band lies flat in the plane, with each face keeping its shape and no two face interiors overlapping?

The article gives a geometric proof at this two-rim scope and describes a Lean formalization of it. It does not assume that one rim is nested inside the other. It includes original triangular side faces. Boundary contact is allowed. Section 2 of the paper states the precise theorem and the cut-surface definition.

## Why the choice of cut matters

![Four-panel E4/E9 comparison: the source band with seams E4 and E9, the E4 layout without interior overlap at the displayed trim, the E9 layout with an F10/F7 overlap, and a magnified view of that overlap with the recorded witness point.](figure/out/safe-cuts-e4-e9-comparison.png)

**Figure 1. Two cuts of the same eleven-panel band at one positive trim.**
- (a) The band, with caps omitted and height exaggerated 300,000 times.
- (b) The cut at E4: no face-interior overlap at this trim.
- (c) The cut at E9: faces F10 and F7 overlap.
- (d) That overlap, magnified 28 times.

Both layouts use δ = 1/10000, and the planar panels use equal horizontal and vertical scales.

The verdicts come from recorded exact/interval checks; the overlap shading is drawn for display only. The figure shows one finite case. It is not a proof of the universal theorem, of safety without trimming, or of a collision-free unfolding motion. See the [complete caption](figure/CAPTION.md) and the [display and evidence notes](figure/FIGURE-NOTE.md).

## What the paper does not claim

- **Not Dürer's conjecture.** The paper does not solve it, and the top and bottom faces are not part of the unfolding.
- **No cap-compatible cut and no motion.** It supplies neither a cap-compatible cut nor a continuous collision-free motion.
- **No priority claim.** It does not claim priority for the broad safe-cut existence statement already discussed in Aloupis's work. Section 12 explains that relationship.

## What is in this package

| Path | Contents |
|---|---|
| [article/](article/) | The illustrated PDF and its source: Markdown, generated TeX, the hash-guarded build and the Figure 1 page crops. |
| [figure/](figure/) | The complete E4/E9 figure component, as PNG, SVG, display data, renderer, caption, notes and manifest. |
| [formal/](formal/) | The Lean project, with its toolchain file and dependency lock. |
| [supporting-sources/](supporting-sources/), [evidence/](evidence/) | Supporting documents S1–S13: the arguments, reviews and implementation records the paper cites. |
| [geometry-lab/](geometry-lab/) | The Geometry Lab engine, with its source, tests, contracts and receipts. This includes the exact/interval records behind the figure. |
| [SOURCE-MAP.md](SOURCE-MAP.md), [REPRODUCTION.md](REPRODUCTION.md) | Where each cited source is, and how to rebuild and recheck. |
| [SANITATION.md](SANITATION.md) | What was changed for privacy, and how the affected checks were re-pinned. |
| [LICENSES/](LICENSES/), [citation.txt](citation.txt) | Reuse terms and citation. |
| [INVENTORY.tsv](INVENTORY.tsv), [SHA256SUMS](SHA256SUMS) | The file list and checksums. `SHA256SUMS` covers every file except itself; `INVENTORY.tsv` lists every file except itself and `SHA256SUMS`. |

To check the files, run `sha256sum -c SHA256SUMS` from this folder.

## What is checked, and by whom

- **The argument.** Sections 2–10 of the paper present the geometric argument, so it can be read and challenged there.
- **The formalization.** The Lean project formalizes the main theorem.
  - Its historical records are AI work: Codex's implementation receipts, and a separate review by an unnamed Opus 5.5 agent.
  - For this package, the three named Lean targets were built on the included Lean sources; [REPRODUCTION.md](REPRODUCTION.md) records the result.
- **The figure's finite-case evidence.** The exact/interval records are included, with their checker, an independent re-check, and a derivative run for this package. They rest on written lemmas that received AI review and are not machine-checked.
- **Peer review.** None of this is human peer review, and no human specialist review of the completed proof is recorded.

## Attribution and reuse

- **System** developed the argument and wrote the article.
- **Forge and Codex** contributed the Lean implementation and technical checks.
- **A separate, unnamed Opus 5.5 agent** reviewed the mathematics and the formal model.
- **A separate Claude Code session** built the Geometry Lab engine and the original figure, and prepared this package. System prepared the figure's publication version.
- **Summer Bee** coordinated and stewarded the project. That role does not assert independent verification of the mathematics.

See the [citation](citation.txt) and the [license scope](LICENSES/README.md):
- CC BY 4.0 for the project-original article, exposition, figures and data;
- MIT for project-original software;
- existing third-party terms remain in force.

The Handler's Statement is a separate human-authored document. It is not part of this package.
