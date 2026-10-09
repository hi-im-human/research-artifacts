"""Exact rational prototype of a raw-cycle insertion construction.

This is finite diagnostic code, NOT a universal proof or a Lean compiler run.
It keeps the actual clockwise raw convention. The first polygon's existing
cycle supplies the outer order; only real scalar insertion parameters within
its vertex cones are sorted. No angle, global normal sorter, or hull oracle is
used by the construction. Signed primitive integer rays represent positive
ray classes for these rational fixtures; Lean uses the existing unitRay.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from typing import Sequence
from normal_fan_inputs import cross2, dot, primitive

Scalar = int | F
Point = tuple[F,F]
Ray = tuple[int,int]
Point3 = tuple[F,F,F]


def subtract(a: Point,b: Point) -> Point:
    return a[0]-b[0],a[1]-b[1]


def raw_normals(v: Sequence[Point]) -> tuple[Point,...]:
    """Actual Lean convention: rotate each clockwise edge by (-y,x)."""
    result=[]
    for i,p in enumerate(v):
        e=subtract(v[(i+1)%len(v)],p)
        result.append((-e[1],e[0]))
    return tuple(result)


def _raw_polygon(vertices: Sequence[Sequence[Scalar]]) -> tuple[Point,...]:
    if len(vertices)<3:
        raise ValueError('At least three raw vertices are required')
    out=[]
    for p in vertices:
        if len(p)!=2 or any(not isinstance(x,(int,F)) for x in p):
            raise ValueError('Use exact rational planar vertices')
        out.append((F(p[0]),F(p[1])))
    v=tuple(out)
    for i,u in enumerate(raw_normals(v)):
        if u==(0,0):
            raise ValueError('Raw cyclic edges must be nonzero')
        for j,p in enumerate(v):
            z=dot(u,subtract(p,v[i]))
            if z>0 or (z==0 and j not in (i,(i+1)%len(v))):
                raise ValueError('Raw clockwise support/reducedness condition failed')
    return v


def _ray(w: Point) -> Ray:
    q=primitive(w)
    return q[0],q[1]


def _maximizers(v: tuple[Point,...],w: Point) -> tuple[int,...]:
    values=tuple(dot(w,p) for p in v)
    m=max(values)
    return tuple(i for i,x in enumerate(values) if x==m)


def _blend(u: Point,v: Point,t: F) -> Point:
    return (1-t)*u[0]+t*v[0],(1-t)*u[1]+t*v[1]


@dataclass(frozen=True)
class SpliceBlock:
    vertex: int
    knots: tuple[F,...]   # Closed [0,1] for gap construction.
    rays: tuple[Ray,...] # Left endpoints only: [0,1) ownership.
    support_pairs: tuple[tuple[int,int],...]


@dataclass(frozen=True)
class SplicedCycle:
    a: tuple[Point,...]
    b: tuple[Point,...]
    blocks: tuple[SpliceBlock,...]
    rays: tuple[Ray,...]
    support_pairs: tuple[tuple[int,int],...]

    def original_edges(self,h: Scalar) -> tuple[tuple[Point3,Point3],...]:
        h=F(h)
        if h<=0:
            raise ValueError('Physical height must be positive')
        return tuple(((self.b[j][0],self.b[j][1],F(0)),
                      (self.a[i][0],self.a[i][1],h))
                     for i,j in self.support_pairs)

    def facets(self,h: Scalar) -> tuple[tuple[Point3,...],...]:
        edges=self.original_edges(h)
        return tuple(tuple(sorted(set(edges[i-1]+edges[i]))) for i in range(len(edges)))

    def section_vertices(self,t: Scalar) -> tuple[Point,...]:
        t=F(t)
        if not 0<=t<=1:
            raise ValueError('Section height must lie in [0,1]')
        return tuple(((1-t)*self.b[j][0]+t*self.a[i][0],
                      (1-t)*self.b[j][1]+t*self.a[i][1])
                     for i,j in self.support_pairs)

    def cut_order(self,k: int) -> tuple[int,...]:
        r=len(self.rays)
        if not 0<=k<r:
            raise ValueError('The cut must name an original cyclic edge')
        return tuple((k+1+j)%r for j in range(r))


def splice_cycles(a_raw: Sequence[Sequence[Scalar]],
                  b_raw: Sequence[Sequence[Scalar]]) -> SplicedCycle:
    """Insert B-only normal directions into A's derived local normal cones.

    A and B are raw clockwise lists, not a supplied combined fan. The returned
    support pairs describe each open gap following its corresponding ray.
    Strict nesting is not used by this geometric construction; no unfolding
    conclusion is computed.
    """
    a,b=_raw_polygon(a_raw),_raw_polygon(b_raw)
    na,nb=raw_normals(a),raw_normals(b)
    a_rays={_ray(u) for u in na}
    knots=[{F(0),F(1)} for _ in a]
    for w in nb:
        if _ray(w) in a_rays:
            continue  # Already owned by exactly one A-block left endpoint.
        owners=_maximizers(a,w)
        if len(owners)!=1:
            raise ArithmeticError('A B-only ray did not have a unique A vertex')
        i=owners[0]
        back=subtract(a[i-1],a[i]);ahead=subtract(a[(i+1)%len(a)],a[i])
        D=cross2(back,ahead)
        if D<=0:
            raise ArithmeticError('Derived clockwise corner determinant failed')
        lam=-dot(w,ahead)/D;mu=-dot(w,back)/D
        if lam<=0 or mu<=0:
            raise ArithmeticError('A B-only ray did not lie in a strict A cone')
        t=mu/(lam+mu)
        q=_blend(na[i-1],na[i],t)
        if _ray(q)!=_ray(w):
            raise ArithmeticError('Local positive-ray reconstruction failed')
        knots[i].add(t)
    blocks=[]
    for i,K in enumerate(knots):
        ts=tuple(sorted(K))  # Scalar sort ONLY, within one already-ordered A corner.
        rays=[];pairs=[]
        for left,right in zip(ts,ts[1:]):
            w=_blend(na[i-1],na[i],(left+right)/2)
            ma,mb=_maximizers(a,w),_maximizers(b,w)
            if ma!=(i,) or len(mb)!=1:
                raise ArithmeticError('An open merged subgap lacked unique support')
            rays.append(_ray(_blend(na[i-1],na[i],left)))
            pairs.append((i,mb[0]))
        blocks.append(SpliceBlock(i,ts,tuple(rays),tuple(pairs)))
    return SplicedCycle(a,b,tuple(blocks),
        tuple(u for block in blocks for u in block.rays),
        tuple(p for block in blocks for p in block.support_pairs))
