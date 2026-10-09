"""Render the first Safe Cuts comparison figure from figure-data.json (display only; no geometry decisions here).

Run (see README.md and BUILD-RECORD.json for the rendering environment):
    python -B render_figure.py figure-data.json OUT_DIR
Writes OUT_DIR/safe-cuts-e4-e9-comparison.svg, .png (200 dpi) and render-log.json (every display transformation).
Panels: (a) the source lateral band, orthographic view, height exaggerated by HEIGHT_EXAGGERATION and stated in the
figure; caps omitted. (b) E4 trimmed planar layout. (c) E9 trimmed planar layout with the F10/F7 overlap, plus a
magnified inset. Planar panels use equal x/y scale; the planar coordinates are the recorded enclosure-box midpoints.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt                                    # noqa: E402
from matplotlib.patches import Polygon, Rectangle                  # noqa: E402
from mpl_toolkits.mplot3d.art3d import Line3DCollection, Poly3DCollection   # noqa: E402

HEIGHT_EXAGGERATION = 300000        # display z = z * factor (material height 1/10000 -> 30 display units)
VIEW = {"elev": 28, "azim": -58, "proj_type": "ortho"}
SEAM_STYLE = {"E4": {"ls": (0, (6, 3)), "label": "E4"}, "E9": {"ls": (0, (8, 3, 2, 3)), "label": "E9"}}
ACCENT = "#b5450f"
# Data-unit label offsets (with leader lines) for the thin faces only; display placement, recorded in render-log.json.
INSET_STYLE = {"F10": {"ls": "-", "lw": 1.8, "hatch": "////"}, "F7": {"ls": "--", "lw": 1.8, "hatch": "\\\\"},
               "F8": {"ls": ":", "lw": 1.6, "hatch": None}, "F9": {"ls": "-.", "lw": 1.2, "hatch": None}}
LABEL_OFFSETS = {"E4": {"F8": (-16, 12), "F9": (8, 14)}, "E9": {"F9": (-8, -11), "F8": (10, -11)}}
plt.rcParams.update({"svg.fonttype": "none", "svg.hashsalt": "safe-cuts-first-figure", "font.size": 9,
                     "font.family": "DejaVu Sans"})


def centroid(pts):
    return sum(p[0] for p in pts) / len(pts), sum(p[1] for p in pts) / len(pts)


def clip(subject, clipper):
    """Sutherland-Hodgman for counterclockwise convex polygons (display of the overlap region only)."""
    out = list(subject)
    for i in range(len(clipper)):
        a, b = clipper[i], clipper[(i + 1) % len(clipper)]
        inp, out = out, []

        def side(p):
            return (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])
        for j in range(len(inp)):
            cur, prev = inp[j], inp[j - 1]
            sc, sp = side(cur), side(prev)
            if sc >= 0:
                if sp < 0:
                    t = sp / (sp - sc)
                    out.append((prev[0] + t * (cur[0] - prev[0]), prev[1] + t * (cur[1] - prev[1])))
                out.append(cur)
            elif sp >= 0:
                t = sp / (sp - sc)
                out.append((prev[0] + t * (cur[0] - prev[0]), prev[1] + t * (cur[1] - prev[1])))
        if not out:
            return []
    return out


def band(ax, mat, log):
    V = mat["vertices"]
    K = HEIGHT_EXAGGERATION
    P = {k: (x, y, z * K) for k, (x, y, z) in V.items()}
    polys, labels = [], []
    for fid, f in sorted(mat["faces"].items(), key=lambda kv: int(kv[0][1:])):
        ring = [P[v] for v in f["boundary"]]
        polys.append(ring)
        labels.append((fid, ring))
    ax.computed_zorder = False
    ax.add_collection3d(Poly3DCollection(polys, facecolor="#ececec", edgecolor="#555555", linewidths=0.6, alpha=0.55))
    for rim in ("top_rim", "bottom_rim"):
        ids = mat[rim]
        ax.add_collection3d(Line3DCollection([[P[ids[i]], P[ids[(i + 1) % len(ids)]]] for i in range(len(ids))],
                                             colors="#222222", linewidths=1.0))
    for fid, ring in labels:
        cx = sum(p[0] for p in ring) / len(ring)
        cy = sum(p[1] for p in ring) / len(ring)
        cz = sum(p[2] for p in ring) / len(ring)
        ax.text(cx, cy, cz, fid, fontsize=7, ha="center", va="center", color="black", zorder=10,
                bbox={"boxstyle": "round,pad=0.12", "fc": "white", "ec": "none", "alpha": 0.85})
    for seam, st in SEAM_STYLE.items():
        lo, hi = mat["hinges"][seam]
        ax.plot(*zip(P[lo], P[hi]), color="black", linewidth=2.8, linestyle=st["ls"], zorder=9)
        mid = [(a + b) / 2 for a, b in zip(P[lo], P[hi])]
        ax.text(mid[0], mid[1], mid[2] + 6, f"seam {seam}", fontsize=8.5, fontweight="bold", zorder=11,
                bbox={"boxstyle": "round,pad=0.2", "fc": "white", "ec": "black", "lw": 0.6})
    xs = [p[0] for p in P.values()]
    ys = [p[1] for p in P.values()]
    zs = [p[2] for p in P.values()]
    ax.set_box_aspect((max(xs) - min(xs), max(ys) - min(ys), max(zs) - min(zs)))
    ax.set_xlim(min(xs), max(xs))
    ax.set_ylim(min(ys), max(ys))
    ax.set_zlim(min(zs), max(zs))
    ax.view_init(elev=VIEW["elev"], azim=VIEW["azim"])
    ax.set_axis_off()
    ax.set_title("(a) Lateral band and the two seams\nheight exaggerated ×300,000; caps omitted", fontsize=9)
    log["panel_a"] = {"projection": "orthographic (matplotlib mplot3d proj_type='ortho')", **VIEW,
                      "height_exaggeration": K, "xy_scale": "equal (box aspect from data extents)",
                      "caps": "omitted (not part of the unfolded surface)",
                      "seam_line_styles": {"E4": "dashed", "E9": "dash-dot"}}


def layout(ax, seam, data, title, log, highlight=None):
    faces = data["faces"]
    for fid in data["chain"]:
        pts = faces[fid]
        hl = highlight and fid in highlight["faces"]
        ax.add_patch(Polygon(pts, closed=True, facecolor="#f2f2f2" if not hl else "white",
                             edgecolor="#333333", linewidth=0.7 if not hl else 1.3,
                             hatch=highlight["faces"][fid] if hl else None))
        cx, cy = centroid(pts)
        off = LABEL_OFFSETS.get(seam, {}).get(fid)
        if off:
            ax.annotate(fid, (cx, cy), xytext=(cx + off[0], cy + off[1]), fontsize=7.5, ha="center", va="center",
                        arrowprops={"arrowstyle": "-", "lw": 0.6}, bbox={"boxstyle": "round,pad=0.15", "fc": "white",
                                                                         "ec": "none", "alpha": 0.9})
        else:
            ax.text(cx, cy, fid, fontsize=7.5, ha="center", va="center",
                    bbox={"boxstyle": "round,pad=0.15", "fc": "white", "ec": "none", "alpha": 0.8})
    first = data["chain"][0]
    p0, p1 = faces[first][0], faces[first][1]
    ax.plot([p0[0], p1[0]], [p0[1], p1[1]], color="black", linewidth=2.4, linestyle=SEAM_STYLE[seam]["ls"])
    last = data["chain"][-1]
    q0, q1 = faces[last][3], faces[last][2]
    ax.plot([q0[0], q1[0]], [q0[1], q1[1]], color="black", linewidth=2.4, linestyle=SEAM_STYLE[seam]["ls"])
    xs = [p[0] for f in faces.values() for p in f]
    ys = [p[1] for f in faces.values() for p in f]
    pad = 6
    ax.set_xlim(min(xs) - pad, max(xs) + pad)
    ax.set_ylim(min(ys) - pad, max(ys) + pad)
    ax.set_aspect("equal")
    ax.tick_params(labelsize=7)
    ax.set_title(title, fontsize=9)
    log[f"panel_{seam}"] = {"label_offsets_data_units": LABEL_OFFSETS.get(seam, {}), "coordinates": "midpoints of recorded enclosure boxes (normalization N0), no rescaling",
                            "x_y_scale": "equal", "seam_copies": "thick lines at the first and last chain faces",
                            "x_range": [min(xs), max(xs)], "y_range": [min(ys), max(ys)]}


def main(data_path: Path, out: Path):
    d = json.loads(data_path.read_text(encoding="ascii"))
    out.mkdir(parents=True, exist_ok=True)
    log = {"label": "display transformations for safe-cuts-e4-e9-comparison", "matplotlib": matplotlib.__version__}
    fig = plt.figure(figsize=(17, 5.8))
    ax_a = fig.add_axes([0.0, 0.08, 0.26, 0.84], projection="3d", proj_type=VIEW["proj_type"])
    band(ax_a, d["material"], log)
    ax_b = fig.add_axes([0.27, 0.13, 0.24, 0.76])
    layout(ax_b, "E4", d["seams"]["E4"], "(b) Cut at E4, trimmed (δ = 1/10000)\nNo interior overlap at this trim", log)
    e9 = d["seams"]["E9"]
    w = next(x for x in e9["witnesses"] if sorted(x["pair"]) == ["F10", "F7"])
    ax_c = fig.add_axes([0.53, 0.13, 0.24, 0.76])
    hl = {"faces": {"F10": "////", "F7": "\\\\\\\\"}}
    layout(ax_c, "E9", e9, "(c) Cut at E9, trimmed (δ = 1/10000)\nInterior overlap: F10 and F7", log, highlight=hl)
    region = clip(e9["faces"]["F10"], e9["faces"]["F7"])
    ax_c.add_patch(Polygon(region, closed=True, facecolor=ACCENT, edgecolor="black", linewidth=0.8, hatch="xxxx",
                           alpha=0.85))
    ax_c.plot(*w["point"], marker="x", color="black", markersize=6, mew=1.6)
    rx = [p[0] for p in region]
    ry = [p[1] for p in region]
    span = max(max(rx) - min(rx), max(ry) - min(ry))
    cx, cy = (min(rx) + max(rx)) / 2, (min(ry) + max(ry)) / 2
    half = span * 0.9
    inset = fig.add_axes([0.79, 0.13, 0.20, 0.76])
    # Unfilled outlines: in D, F8 and F9 also overlap F10 and F7 (E9's other recorded witness pairs), so filled faces
    # would hide one another. Each face has its own line style; the legend names them (no colour needed).
    handles = []
    for fid in ("F10", "F7", "F8", "F9"):
        st = INSET_STYLE[fid]
        patch = Polygon(e9["faces"][fid], closed=True, facecolor="none", edgecolor="black", linewidth=st["lw"],
                        linestyle=st["ls"], hatch=st["hatch"])
        inset.add_patch(patch)
        handles.append(Polygon([[0, 0], [1, 0], [1, 1]], facecolor="none", edgecolor="black", linewidth=st["lw"],
                               linestyle=st["ls"], hatch=st["hatch"], label=fid))
    inset.add_patch(Polygon(region, closed=True, facecolor=ACCENT, edgecolor="black", linewidth=0.8, hatch="xxxx",
                            alpha=0.85))
    inset.plot(*w["point"], marker="x", color="black", markersize=7, mew=1.8)
    inset.annotate("recorded witness point", w["point"], xytext=(10, -28), textcoords="offset points", fontsize=7.5,
                   arrowprops={"arrowstyle": "-", "lw": 0.6},
                   bbox={"boxstyle": "round,pad=0.2", "fc": "white", "ec": "none"})
    window = [(cx - half, cy - half), (cx + half, cy - half), (cx + half, cy + half), (cx - half, cy + half)]
    inset_labels = {}
    for fid in ("F10", "F7", "F8", "F9"):
        part = clip(e9["faces"][fid], window)        # the face's visible part in the detail window
        if len(part) >= 3:
            lx, ly = centroid(part)
            inset_labels[fid] = [lx, ly]
    inset.legend(handles=handles, loc="lower left", fontsize=8, framealpha=1, handlelength=2.6, handleheight=1.4,
                 title="faces (outlines)", title_fontsize=8)
    ox, oy = centroid(region)
    inset.annotate("overlap F10 ∩ F7", (ox, oy), xytext=(40, 60), textcoords="offset points", fontsize=8,
                   arrowprops={"arrowstyle": "-", "lw": 0.7},
                   bbox={"boxstyle": "round,pad=0.2", "fc": "white", "ec": "none"})
    inset.set_xlim(cx - half, cx + half)
    inset.set_ylim(cy - half, cy + half)
    inset.set_aspect("equal")
    inset.set_xticks([])
    inset.set_yticks([])
    main_span = ax_c.get_xlim()[1] - ax_c.get_xlim()[0]
    mag = main_span / (2 * half)
    inset.set_title(f"(d) Detail of (c): F10/F7 interior overlap\n(dotted box in (c), magnified ×{mag:.0f}; equal x/y scale)",
                    fontsize=9)
    ax_c.add_patch(Rectangle((cx - half, cy - half), 2 * half, 2 * half, fill=False, edgecolor="black",
                             linewidth=0.8, linestyle=":"))
    fig.text(0.5, 0.015, "Eleven-panel specimen, ideal trimmed development D, δ = 1/10000. Planar panels: equal x/y "
             "scale, recorded exact/interval checks. A finite positive-trim illustration, not an "
             "untrimmed-safety or motion proof.", ha="center", fontsize=7.5)
    log["panel_E9"]["overlap_region"] = {"faces": ["F10", "F7"], "bbox_x": [min(rx), max(rx)],
                                         "bbox_y": [min(ry), max(ry)],
                                         "method": "float clip of the displayed face polygons (display only; the "
                                                   "certificate is the recorded interior witness)"}
    log["panel_E9"]["witness_point_exact"] = w["point_exact"]
    log["panel_E9"]["inset_faces_visible"] = sorted(inset_labels)
    log["panel_E9"]["inset_face_styles"] = INSET_STYLE
    log["panel_E9"]["inset"] = {"x_range": [cx - half, cx + half], "y_range": [cy - half, cy + half],
                                "magnification_vs_panel": round(mag, 3), "x_y_scale": "equal"}
    svg, png = out / "safe-cuts-e4-e9-comparison.svg", out / "safe-cuts-e4-e9-comparison.png"
    fig.savefig(svg, metadata={"Date": None, "Creator": "render_figure.py"})
    fig.savefig(png, dpi=200, metadata={"Software": "render_figure.py"})
    (out / "render-log.json").write_text(json.dumps(log, indent=1, sort_keys=True) + "\n", encoding="ascii",
                                         newline="\n")
    print(json.dumps(log["panel_E9"], indent=1))


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
