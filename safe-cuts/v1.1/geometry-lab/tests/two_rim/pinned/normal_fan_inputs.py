"""Exact finite tests of the normal-direction construction in checkpoint 39.

This constructs rational examples, not a universal theorem or an unfolding.
The independent 3D hull check enumerates supporting planes from raw vertex
triples. No GEOS, floating-point predicates, or Lean execution is involved.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cmp_to_key
from itertools import combinations
from math import gcd, lcm
from typing import Iterable, Sequence

Point2 = tuple[F, F]
Point3 = tuple[F, F, F]
Ray = tuple[int, int]
Plane = tuple[int, int, int, int]


def cross2(a: Sequence[F], b: Sequence[F]) -> F:
    return a[0]*b[1]-a[1]*b[0]


def hull2(points: Iterable[Sequence[int | F]]) -> list[Point2]:
    """Monotone-chain convex hull with straight-through boundary points removed."""
    pts = sorted(set((F(p[0]),F(p[1])) for p in points))
    if len(pts) < 3:
        raise ValueError('A polygon needs at least three noncollinear points')
    def turn(a: Point2,b: Point2,c: Point2) -> F:
        return cross2((b[0]-a[0],b[1]-a[1]),(c[0]-a[0],c[1]-a[1]))
    lower: list[Point2] = []
    upper: list[Point2] = []
    for p in pts:
        while len(lower)>=2 and turn(lower[-2],lower[-1],p)<=0:
            lower.pop()
        lower.append(p)
    for p in reversed(pts):
        while len(upper)>=2 and turn(upper[-2],upper[-1],p)<=0:
            upper.pop()
        upper.append(p)
    hull=lower[:-1]+upper[:-1]
    if len(hull)<3:
        raise ValueError('The polygon has empty planar interior')
    return hull


def primitive(values: Sequence[int | F]) -> tuple[int,...]:
    q=tuple(F(v) for v in values)
    den=lcm(*(v.denominator for v in q))
    ints=tuple(int(v*den) for v in q)
    g=gcd(*ints)
    if not g:
        raise ValueError('Zero does not determine a direction/plane')
    # Keep the sign: opposite outward normals are different positive rays.
    return tuple(v//g for v in ints)


def edge_normals(polygon: Sequence[Point2]) -> list[Ray]:
    return [primitive((polygon[(i+1)%len(polygon)][1]-p[1],
                       p[0]-polygon[(i+1)%len(polygon)][0]))
            for i,p in enumerate(polygon)]  # type: ignore[return-value]


def angle_cmp(u: Ray,v: Ray) -> int:
    def half(w: Ray) -> int:
        return 0 if w[1]>0 or (w[1]==0 and w[0]>=0) else 1
    if half(u)!=half(v):
        return -1 if half(u)<half(v) else 1
    cr=cross2(u,v)
    return -1 if cr>0 else (1 if cr<0 else 0)


def merged_normals(top: Sequence[Point2],bottom: Sequence[Point2]) -> list[Ray]:
    rays=set(edge_normals(top)) | set(edge_normals(bottom))
    return sorted(rays,key=cmp_to_key(angle_cmp))


def dot(a: Sequence[int | F],b: Sequence[int | F]) -> F:
    return sum((F(x)*F(y) for x,y in zip(a,b)),F(0))


def support(polygon: Sequence[Point2],u: Sequence[int | F]) -> F:
    return max(dot(u,p) for p in polygon)


def support_vertex(polygon: Sequence[Point2],w: Sequence[int | F]) -> Point2:
    s=support(polygon,w)
    vs=[p for p in polygon if dot(w,p)==s]
    if len(vs)!=1:
        raise ValueError('A merged-normal gap must have a unique support vertex')
    return vs[0]


def mix(a: Sequence[int | F],b: Sequence[int | F],t: int | F) -> tuple[F,...]:
    t=F(t)
    return tuple((1-t)*F(x)+t*F(y) for x,y in zip(a,b))


@dataclass(frozen=True)
class BandModel:
    top: list[Point2]
    bottom: list[Point2]
    h: F
    normals: list[Ray]
    gap_vertices: list[tuple[Point2,Point2]]  # (bottom, top)
    facets: list[tuple[Point3,...]]
    edges: list[tuple[Point3,Point3]]
    vertices: tuple[Point3,...]

    @property
    def r(self) -> int:
        return len(self.normals)


def build_band(top: Iterable[Sequence[int | F]],bottom: Iterable[Sequence[int | F]],
               h: int | F) -> BandModel:
    A,B,h=hull2(top),hull2(bottom),F(h)
    if h<=0:
        raise ValueError('Physical height must be positive')
    for u in edge_normals(B):
        if not all(dot(u,a)<support(B,u) for a in A):
            raise ValueError('The top projection must be strictly inside the base')
    N=merged_normals(A,B)
    pairs=[]
    for i,u in enumerate(N):
        v=N[(i+1)%len(N)]
        if cross2(u,v)<=0:
            raise ValueError('Merged consecutive normals must bound an angle in (0, pi)')
        w=(u[0]+v[0],u[1]+v[1])
        pairs.append((support_vertex(B,w),support_vertex(A,w)))
    edges=[((b[0],b[1],F(0)),(a[0],a[1],h)) for b,a in pairs]
    facets=[tuple(sorted(set(edges[i-1]+edges[i]))) for i in range(len(N))]
    vertices=tuple((b[0],b[1],F(0)) for b in B)+tuple((a[0],a[1],h) for a in A)
    return BandModel(A,B,h,N,pairs,facets,edges,vertices)


def side_plane(m: BandModel,i: int) -> Plane:
    u=m.normals[i]
    sb,sa=support(m.bottom,u),support(m.top,u)
    return primitive((u[0],u[1],(sb-sa)/m.h,sb))  # type: ignore[return-value]


def plane_value(plane: Plane,p: Point3) -> F:
    """Nonnegative is the inside of the supporting halfspace."""
    return F(plane[3])-dot(plane[:3],p)


def supporting_facets(vertices: Sequence[Point3]) -> dict[Plane,set[Point3]]:
    """Independent exact 3D hull oracle by all noncollinear vertex triples."""
    result={}
    for a,b,c in combinations(vertices,3):
        u=tuple(b[i]-a[i] for i in range(3))
        v=tuple(c[i]-a[i] for i in range(3))
        n=(u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0])
        if n==(0,0,0):
            continue
        k=dot(n,a)
        residual=[k-dot(n,p) for p in vertices]
        if all(r>=0 for r in residual):
            plane=primitive((*n,k))
        elif all(r<=0 for r in residual):
            plane=primitive(tuple(-x for x in (*n,k)))
        else:
            continue
        result[plane]={p for p in vertices if plane_value(plane,p)==0}
    return result


def section_hull(top: Sequence[Point2],bottom: Sequence[Point2],t: int | F) -> list[Point2]:
    """Reference section via all pairwise sums, not the merged-normal code."""
    return hull2(mix(b,a,t) for b in bottom for a in top)


def connected_components(vertices: set[int],edges: Iterable[tuple[int,int]]) -> int:
    graph={v:set() for v in vertices}
    for a,b in edges:
        if a not in graph or b not in graph:
            raise ValueError('An incidence link left its claimed vertex fan')
        graph[a].add(b)
        graph[b].add(a)
    unseen=set(vertices)
    count=0
    while unseen:
        stack=[unseen.pop()]
        count+=1
        while stack:
            v=stack.pop()
            for w in graph[v]&unseen:
                unseen.remove(w)
                stack.append(w)
    return count


def section_from_merged_rows(m: BandModel, t: int | F) -> list[Point2]:
    """Reconstruct one section using only the merged support halfspaces.

    This is an independent finite contract check for the formal theorem that
    the merged rows are complete. It enumerates boundary-line intersections,
    retains points satisfying every merged row, and takes their exact hull.
    """
    t = F(t)
    bounds = [
        (1-t)*support(m.bottom, u) + t*support(m.top, u)
        for u in m.normals
    ]
    pts: list[Point2] = []
    for i, j in combinations(range(m.r), 2):
        u, v = m.normals[i], m.normals[j]
        det = F(u[0]*v[1] - u[1]*v[0])
        if det == 0:
            continue
        bi, bj = bounds[i], bounds[j]
        x = (bi*F(v[1]) - F(u[1])*bj) / det
        y = (F(u[0])*bj - bi*F(v[0])) / det
        p = (x, y)
        if all(dot(w, p) <= b for w, b in zip(m.normals, bounds)):
            pts.append(p)
    return hull2(pts)
