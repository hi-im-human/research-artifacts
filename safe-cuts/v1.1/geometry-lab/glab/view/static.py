"""Static inspection renderer: view JSON -> SVG and polygon OBJ. Standard library only; no geometry.

Usage:  python -m glab.view.static VIEW.json OUT_PREFIX
"""
from __future__ import annotations

import html
import json
import sys
from pathlib import Path

__all__ = ["render_svg", "render_obj", "main"]

PALETTE = ["#4e79a7", "#f28e2b", "#59a14f", "#b07aa1", "#76b7b2", "#edc948", "#9c755f", "#e15759", "#bab0ac",
           "#86bcb6", "#8cd17d", "#d4a6c8"]
STATUS = {"pass": "#2e7d32", "fail": "#c62828", "unknown": "#b26a00", "not_run": "#616161"}


def _fit(points, box):
    x0, y0, w, h = box
    xs, ys = [p[0] for p in points], [p[1] for p in points]
    span = max(max(xs) - min(xs), max(ys) - min(ys), 1e-12)
    s = 0.92 * min(w / max(max(xs) - min(xs), 1e-12), h / max(max(ys) - min(ys), 1e-12), 1e300) if span else 1
    cx, cy = (max(xs) + min(xs)) / 2, (max(ys) + min(ys)) / 2
    return lambda p: (x0 + w / 2 + s * (p[0] - cx), y0 + h / 2 - s * (p[1] - cy))


def _pts(tf, pts):
    return " ".join(f"{tf(p)[0]:.2f},{tf(p)[1]:.2f}" for p in pts)


def render_svg(view: dict) -> str:
    W, H = 1280, 1280
    order = view["face_order"]
    color = {f: PALETTE[i % len(PALETTE)] for i, f in enumerate(order)}
    bad = {f for row in view["problem_pairs"] if row["outcome"] == "fail" for f in row["pair"]}
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" font-family="sans-serif" font-size="12">',
           '<rect width="100%" height="100%" fill="#ffffff"/>',
           f'<text x="20" y="28" font-size="17">Geometry Lab Stage 3 static inspection - {html.escape(view["state_kind"])}'
           f'{" delta=" + view["delta"] if view.get("delta") else ""} - seam {html.escape(view["seam"]["id"])}</text>',
           f'<text x="20" y="47" fill="#555">subject {view["subject_state"][:23]}... ; float64 placement of an exact '
           'source; numerical diagnostics only, not a certificate or a motion</text>']
    st = view.get("statuses")
    if st:
        out.append(f'<text x="840" y="28" font-size="13">local chain status: <tspan fill="{STATUS.get(st["local"], "#616161")}">'
                   f'{html.escape(st["local"])}</tspan>; source-linked status: <tspan fill="'
                   f'{STATUS.get(st["source_linked"], "#616161")}">{html.escape(st["source_linked"])}</tspan></text>')
    else:
        out.append('<text x="840" y="28" font-size="13" fill="#555">aggregate statuses not supplied</text>')
    # 3D band: display projection with height exaggerated for legibility (display only)
    h = float(view["height"].split("/")[0]) / (float(view["height"].split("/")[1]) if "/" in view["height"] else 1)
    allxy = [p for f in view["faces_3d"].values() for p in f["xyz"]]
    span = max(max(p[0] for p in allxy) - min(p[0] for p in allxy), max(p[1] for p in allxy) - min(p[1] for p in allxy))
    zs = 0.35 * span / h if h else 1.0

    def proj(p):
        return (p[0] + 0.4 * p[1], 0.3 * p[1] + p[2] * zs)
    band = {f: [proj(p) for p in view["faces_3d"][f]["xyz"]] for f in order}
    tf = _fit([q for ps in band.values() for q in ps], (20, 70, 560, 480))
    out.append('<text x="20" y="66">Original band (display projection; height exaggerated) - seam in red</text>')
    for f in order:
        out.append(f'<polygon points="{_pts(tf, band[f])}" fill="{color[f]}" fill-opacity="0.30" stroke="#333" '
                   'stroke-width="0.8"/>')
        cx = sum(tf(q)[0] for q in band[f]) / len(band[f])
        cy = sum(tf(q)[1] for q in band[f]) / len(band[f])
        out.append(f'<text x="{cx:.1f}" y="{cy:.1f}" text-anchor="middle" font-size="11">{f}</text>')
    a, b = (tf(proj(p)) for p in view["seam"]["xyz"])
    out.append(f'<line x1="{a[0]:.2f}" y1="{a[1]:.2f}" x2="{b[0]:.2f}" y2="{b[1]:.2f}" stroke="#d00" stroke-width="4"/>')
    # planar candidate
    tp = _fit([q for f in view["planar"].values() for q in f["xy"]], (620, 70, 640, 480))
    out.append('<text x="620" y="66">Planar candidate (exported images) - red lines: the two seam copies; '
               'red dashed outline: faces in a failing pair</text>')
    for f in order:
        xy = view["planar"][f]["xy"]
        out.append(f'<polygon points="{_pts(tp, xy)}" fill="{color[f]}" fill-opacity="0.40" stroke="#222" '
                   'stroke-width="0.8"/>')
    for f in order:
        if f in bad:
            out.append(f'<polygon points="{_pts(tp, view["planar"][f]["xy"])}" fill="none" stroke="#c62828" '
                       'stroke-width="2.5" stroke-dasharray="7,4"/>')
    for f in order:
        xy = view["planar"][f]["xy"]
        cx = sum(tp(q)[0] for q in xy) / len(xy)
        cy = sum(tp(q)[1] for q in xy) / len(xy)
        out.append(f'<text x="{cx:.1f}" y="{cy:.1f}" text-anchor="middle" font-size="12" font-weight="bold">{f}</text>')
    for copy_ in view["seam"]["copies"]:
        a, b = tp(copy_[0]), tp(copy_[1])
        out.append(f'<line x1="{a[0]:.2f}" y1="{a[1]:.2f}" x2="{b[0]:.2f}" y2="{b[1]:.2f}" stroke="#d00" '
                   'stroke-width="3.5"/>')
    # zoom inset: only the faces that appear in failing pairs (display only; same exported images)
    if bad:
        zoom = [f for f in order if f in bad]
        tz = _fit([q for f in zoom for q in view["planar"][f]["xy"]], (620, 590, 640, 300))
        out.append('<rect x="620" y="585" width="640" height="310" fill="none" stroke="#999"/>')
        out.append('<text x="626" y="603">Zoom: faces in failing pairs (same exported images)</text>')
        for f in zoom:
            xy = view["planar"][f]["xy"]
            out.append(f'<polygon points="{_pts(tz, xy)}" fill="{color[f]}" fill-opacity="0.35" stroke="#c62828" '
                       'stroke-width="1.5"/>')
        for f in zoom:
            xy = view["planar"][f]["xy"]
            cx = sum(tz(q)[0] for q in xy) / len(xy)
            cy = sum(tz(q)[1] for q in xy) / len(xy)
            out.append(f'<text x="{cx:.1f}" y="{cy:.1f}" text-anchor="middle" font-size="13" font-weight="bold">{f}</text>')
    # evidence and non-passing pairs
    y = 925
    out.append(f'<text x="20" y="{y}" font-size="14">Evidence for this state (outcome / method / coverage)</text>')
    for i, e in enumerate(view["evidence"]):
        col, row = i % 2, i // 2
        x, yy = 20 + col * 640, y + 22 + row * 19
        out.append(f'<rect x="{x}" y="{yy - 11}" width="12" height="12" fill="{STATUS.get(e["outcome"], "#616161")}"/>')
        out.append(f'<text x="{x + 18}" y="{yy}">{html.escape(e["claim"])}: {e["outcome"]} ({e["method"]}; '
                   f'{html.escape(e["coverage"])})</text>')
    y2 = y + 22 + ((len(view["evidence"]) + 1) // 2) * 19 + 12
    rows = view["problem_pairs"]
    fails = [r for r in rows if r["outcome"] == "fail"]
    out.append(f'<text x="20" y="{y2}" font-size="14">Non-passing face pairs: {len(fails)} fail, '
               f'{len(rows) - len(fails)} unknown</text>')
    for i, r in enumerate(fails[:6] + [r for r in rows if r["outcome"] != "fail"][:4]):
        out.append(f'<text x="20" y="{y2 + 20 + i * 17}" fill="{STATUS[r["outcome"]]}">{"/".join(r["pair"])}: '
                   f'{r["outcome"]} - {html.escape(r["reason"])}{" (shared " + r["shared"] + ")" if r["shared"] else ""}'
                   '</text>')
    out.append("</svg>")
    return "\n".join(out) + "\n"


def render_obj(view: dict):
    """Band OBJ shares material vertices; planar OBJ keeps one vertex per face occurrence (seam never welded)."""
    ids, band = {}, ["# original lateral band, polygon faces (not triangulated)"]
    for f in view["face_order"]:
        for v, p in zip(view["faces_3d"][f]["boundary"], view["faces_3d"][f]["xyz"]):
            if v not in ids:
                ids[v] = len(ids) + 1
                band.append(f"v {p[0]!r} {p[1]!r} {p[2]!r}  # {v}")
    for f in view["face_order"]:
        band += [f"g {f}", "f " + " ".join(str(ids[v]) for v in view["faces_3d"][f]["boundary"])]
    planar, k = ["# planar candidate; one vertex per face occurrence; coincident positions are not glued"], 0
    for f in view["face_order"]:
        first = k + 1
        for label, q in zip(view["planar"][f]["labels"], view["planar"][f]["xy"]):
            k += 1
            planar.append(f"v {q[0]!r} {q[1]!r} 0.0  # {f}@{label}")
        planar += [f"g {f}", "f " + " ".join(str(i) for i in range(first, k + 1))]
    return "\n".join(band) + "\n", "\n".join(planar) + "\n"


def main(argv):
    view = json.loads(Path(argv[1]).read_text(encoding="ascii"))
    prefix = Path(argv[2])
    Path(str(prefix) + ".svg").write_text(render_svg(view), encoding="utf-8", newline="\n")
    band, planar = render_obj(view)
    Path(str(prefix) + "-band.obj").write_text(band, encoding="ascii", newline="\n")
    Path(str(prefix) + "-planar.obj").write_text(planar, encoding="ascii", newline="\n")


if __name__ == "__main__":
    main(sys.argv)
