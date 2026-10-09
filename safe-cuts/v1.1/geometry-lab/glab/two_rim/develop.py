"""Static full-affine development of an opened chain (float64; standard library `math` only).

Port of the chart/turn/transition formulas of the historical floating diagnostic
`<historical-folder>/code/midsection_bridge.py` (blob cce8c34f), reviewed against DRAFT-02
section 4. PhysicalBridge is never imported; the construction reads the stored Stage 2 material
(exact coordinates converted to float64) and never re-hulls the source.

  chart psi_i  : rows [nu_i, -xi_i], origin M_i (midpoint of hinge E_i)
  turn  q_i    = phi(nu_i) - phi(nu_{i-1}),  phi(w) = angle between w and G_i
  T_i(z)       = R(q_{i+1}) z + (l_i, 0)
  maps(k)      : W_0 = id, U_j = W_j o psi_{k+j}, W_{j+1} = W_j o T_{k+j}   (translation retained)
"""
from __future__ import annotations

import math
from fractions import Fraction

from .cut import DevelopmentInputError

__all__ = ["chart_data", "develop_static", "MAP_CONVENTION"]

MAP_CONVENTION = ("image = linear @ [x, y, z] + offset; linear is 2x3 row-major; x, y, z are the exact "
                  "material coordinates converted to float64")


def _sub(a, b):
    return [x - y for x, y in zip(a, b)]


def _dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def _norm(a):
    return math.sqrt(_dot(a, a))


def _cross(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def _angle(w, g):
    return math.atan2(_norm(_cross(w, g)), _dot(w, g))


def chart_data(material: dict) -> dict:
    """Per-hinge/face float data in material order (face i lies between hinges i and i+1)."""
    xyz = {v["id"]: [float(Fraction(c)) for c in v["xyz"]] for v in material["vertices"]}
    low = [xyz[e["lower"]] for e in material["hinges"]]
    high = [xyz[e["upper"]] for e in material["hinges"]]
    n = len(low)
    hinge = [_sub(high[i], low[i]) for i in range(n)]
    mid = [[(a + b) / 2 for a, b in zip(low[i], high[i])] for i in range(n)]
    nu, length, chart = [], [], []
    for i in range(n):
        edge = _sub(mid[(i + 1) % n], mid[i])
        ell = _norm(edge)
        u = [c / ell for c in edge]
        d = _dot(hinge[i], u)
        trans = [h - d * c for h, c in zip(hinge[i], u)]
        tn = _norm(trans)
        xi = [c / tn for c in trans]
        nu.append(u)
        length.append(ell)
        chart.append([u, [-c for c in xi]])
    q = [_angle(nu[i], hinge[i]) - _angle(nu[i - 1], hinge[i]) for i in range(n)]
    return {"faces": [f["id"] for f in material["faces"]], "chart": chart, "mid": mid, "length": length, "q": q}


def _matmul2(a, b):
    return [[a[0][0] * b[0][0] + a[0][1] * b[1][0], a[0][0] * b[0][1] + a[0][1] * b[1][1]],
            [a[1][0] * b[0][0] + a[1][1] * b[1][0], a[1][0] * b[0][1] + a[1][1] * b[1][1]]]


def develop_static(cut: dict) -> dict:
    """two_rim.development/1 payload: one full affine map per face, in chain order."""
    if cut.get("schema") != "two_rim.cut/1":
        raise DevelopmentInputError(f"unsupported cut schema {cut.get('schema')!r}")
    material = cut["material"]
    data = chart_data(material)
    n = len(data["faces"])
    k = data["faces"].index(cut["face_order"][0])
    rot = [[1.0, 0.0], [0.0, 1.0]]
    t = [0.0, 0.0]
    maps = []
    for j in range(n):
        i = (k + j) % n
        lin = [[rot[r][0] * data["chart"][i][0][c] + rot[r][1] * data["chart"][i][1][c] for c in range(3)]
               for r in range(2)]
        offset = [t[r] - _dot(lin[r], data["mid"][i]) for r in range(2)]
        maps.append({"face": data["faces"][i], "linear": lin, "offset": offset})
        t = [t[0] + rot[0][0] * data["length"][i], t[1] + rot[1][0] * data["length"][i]]
        qn = data["q"][(i + 1) % n]
        c, s = math.cos(qn), math.sin(qn)
        rot = _matmul2(rot, [[c, -s], [s, c]])
    if [m["face"] for m in maps] != cut["face_order"]:
        raise DevelopmentInputError("chain order in the cut does not follow the material's hinge order")
    return {"schema": "two_rim.development/1", "numeric_domain": "float64", "map_convention": MAP_CONVENTION,
            "maps": maps, "cut": cut,
            "generator": {"name": "glab.two_rim.develop", "port_of": "midsection_bridge.py blob cce8c34f",
                          "turns_q": data["q"], "sum_q": math.fsum(data["q"])}}
