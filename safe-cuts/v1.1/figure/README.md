# Safe Cuts: companion figure component

This component contains the E4/E9 figure, its display-data extract, renderer, caption, alt text and display notes. It is not the full article/formal-evidence release.

## Render the supplied display data

From this directory, using Python with Matplotlib and NumPy installed:

```bash
python -B render_figure.py figure-data.json out
```

The outputs are `out/safe-cuts-e4-e9-comparison.svg`, `out/safe-cuts-e4-e9-comparison.png` and `out/render-log.json`. The PNG is 3400×1160 pixels at 200 dpi. The SVG retains text as text and may use a different locally installed font when viewed elsewhere.

`BUILD-RECORD.json` records the environment actually used for these supplied outputs. `SHA256SUMS` identifies their exact bytes. Checksums establish file integrity, not mathematical correctness. Byte-identical rendering across other library or font versions is not promised.

## Read the evidence correctly

`CAPTION.md` contains the caption and alt text. `FIGURE-NOTE.md` describes display transformations and the boundary between rendering and the historical mathematical checks. `SANITATION.md` discloses derivative changes.

The flags in the JSON are historical extraction results, not new checks performed by this renderer. The full certificate records and the Lean project are not included in this figure-only component. No new license is granted by this README; reuse terms belong to the separately authorized publication terms, with applicable component terms preserved.
