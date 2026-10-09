# Publication edition 1.1: PDF build

The article is [../Safe_Cuts_Illustrated_v1.1.pdf](../Safe_Cuts_Illustrated_v1.1.pdf).
- It is built from [../manuscript.md](../manuscript.md) by `build_pdf.py`, with `pdf-style.tex` and `figure-1-pages.tex`.
- [../manuscript.tex](../manuscript.tex) is the LaTeX that build generated.

Edition 1.1 revises the earlier publication edition 1.0, which is not part of this package.

## What changed from edition 1.0

These are the controlled edits only:
- **Edition label.**
- **Figure 1:** an orientation paragraph and the figure after Section 2.3, with the complete figure caption.
- **Notation reminder:** a local note before Lemma 5.1.
- **Section 10.1:** the formal route now names `MixedTurnSafeCut`.
- **Section 12:** "RM" is spelled out.
- **Appendices B and C:** an artifact-availability paragraph, with the package address, and cross-references.

The equations, theorem statements and stated limitations are unchanged.

## Figure 1 pages

The two landscape pages show panels (a)–(b) and (c)–(d) at close to their original size.
- **The images** are exact crops, with no scaling, of `figure/out/safe-cuts-e4-e9-comparison.png` in the research package.
- **How they were made:** `../figure-1/make_figure_panels.py` produced them, and `../figure-1/PANELS.json` records the crop boxes and hashes.
- **The footer line** of the original image is reproduced as typeset text under the panels.
- **The full figure** is unchanged in the figure component, as PNG and SVG.

## Rebuild

From this directory, with Python 3, Pandoc, XeLaTeX, Latin Modern, DejaVu Sans Mono and the LaTeX packages `graphicx` and `pdflscape`:

```text
python build_pdf.py ../manuscript.md build
```

The script:
- checks the pinned manuscript fingerprint and both Figure 1 crop fingerprints;
- leaves the sources unchanged;
- writes `Safe_Cuts_Illustrated_v1.1.pdf`, the generated `manuscript.tex`, a build log and a result record into `build/`.

Pandoc writes LF line endings, and the PDF creation date is fixed (2026-10-08) for repeatable typesetting. The date is not a timestamp attestation.

**Toolchain.** The PDF was built with Pandoc 3.1.11.1 and XeTeX 0.999998 (TeX Live 2026, TinyTeX 2026.10) on Windows. Two builds were byte-identical. Other toolchain or font versions can produce different PDF bytes. The edition 1.0 PDF was built with TeX Live 2025/dev.

## Recorded output

| File | Bytes | SHA-256 |
|---|---|---|
| Manuscript | 61,731 | `93b65e2eb67230b420c19d1d5df52b734f66bbda3c2a848f7ee09f24c1b44677` |
| PDF | 528,869 (23 pages) | `0459cc8166d59a274450ba6d5ea615bbb78146a9cd88d82c483f9a747a2d3302` |
| Generated TeX | 70,329 | `43a0ceffd3365275d07f281bc63af888ce2d7ad7ac779799ac1fa26a9a836d2d` |

These are typesetting records. They are not a mathematical review, a Lean build or human peer review.
