"""Midsection-anchored full-plane developments from a physical prismatoid.

Floating diagnostic realization of a proposed paper bridge, not certified
arithmetic or Lean. Exact rational source edges come from the preserved
cyclic-normal-splice prototype. No safe-state constructor is used.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
import sys
from pathlib import Path
import numpy as np
_root = Path(__file__).resolve().parents[1]
_candidates = [
    _root/'baseline'/'code',
    _root.parent/'<historical-folder>'/'verification'/'packet'/'code',
]
for _candidate in _candidates:
    if (_candidate/'normal_fan_inputs.py').is_file():
        sys.path.insert(0, str(_candidate))
        break
else:
    raise ImportError('Preserved normal-splice diagnostic baseline was not found')
from normal_fan_inputs import hull2
from cyclic_normal_splice import splice_cycles

@dataclass(frozen=True)
class PlaneMap:
    linear: np.ndarray
    offset: np.ndarray
    def __call__(self, points: np.ndarray) -> np.ndarray:
        return np.asarray(points)@self.linear.T+self.offset

class PhysicalBridge:
    def __init__(self,top,bottom,height):
        if F(height)<=0: raise ValueError('Physical height must be positive')
        a=list(reversed(hull2(top)));b=list(reversed(hull2(bottom)))
        if len(a)<3 or len(b)<3: raise ValueError('Both rims must have positive area')
        pairs=splice_cycles(a,b).original_edges(F(height))
        self.low=np.array([p for p,q in pairs],dtype=float)
        self.high=np.array([q for p,q in pairs],dtype=float)
        self.n=len(pairs);self.hinge=self.high-self.low
        self.mid=(self.low+self.high)/2
        edge=np.roll(self.mid,-1,axis=0)-self.mid
        self.mid_length=np.linalg.norm(edge,axis=1)
        u=edge/self.mid_length[:,None]
        dot=np.einsum('ij,ij->i',self.hinge,u)
        transverse=self.hinge-dot[:,None]*u
        v=transverse/np.linalg.norm(transverse,axis=1)[:,None]
        # Negative transverse chart orientation makes q = beta - pi.
        self.chart=np.stack([u,-v],axis=1)
        def phi(vectors):
            c=np.einsum('ij,ij->i',vectors,self.hinge)
            s=np.linalg.norm(np.cross(vectors,self.hinge),axis=1)
            return np.arctan2(s,c)
        self.q=phi(u)-phi(np.roll(u,1,axis=0))
        self._rot=[]
        for i in range(self.n):
            q=self.q[(i+1)%self.n];c,s=np.cos(q),np.sin(q)
            self._rot.append(np.array([[c,-s],[s,c]]))
    def rims(self,depth):
        d=float(depth)
        if not 0<d<.5: raise ValueError('An ordinary inward trim needs 0<depth<1/2')
        return self.low+d*self.hinge,self.low+(1-d)*self.hinge
    def maps(self,cut:int):
        if not 0<=cut<self.n: raise ValueError('Invalid original seam index')
        R=np.eye(2);t=np.zeros(2);out=[]
        for j in range(self.n):
            i=(cut+j)%self.n
            L=R@self.chart[i]
            out.append(PlaneMap(L,t-L@self.mid[i]))
            # Full affine composition: do not discard the translation.
            t=t+R@np.array([self.mid_length[i],0.])
            R=R@self._rot[i]
        return out
    def family(self,depth,cut):
        low,high=self.rims(depth);maps=self.maps(cut)
        B=[];A=[];faces=[];heading=[0.]
        for j in range(self.n):
            i=(cut+j)%self.n;ip=(i+1)%self.n;U=maps[j]
            f=U(np.array([low[i],high[i],high[ip],low[ip]]))
            faces.append(f);B.append(f[0]);A.append(f[1])
            if j+1<self.n: heading.append(heading[-1]+self.q[ip])
        B.append(faces[-1][3]);A.append(faces[-1][2])
        B=np.array(B);A=np.array(A);e=np.diff(B,axis=0)
        length=np.linalg.norm(e,axis=1)
        ratio=np.linalg.norm(np.diff(A,axis=0),axis=1)/length
        return dict(B=B,e=e,d=A-B,length=length,ratio=ratio,
                    heading=np.array(heading),faces=np.array(faces))
