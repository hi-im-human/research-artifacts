"""Exact algebra checks for selected manuscript identities, not a geometry proof.
Requires SymPy. Denominator nonvanishing and geometric signs are manuscript
hypotheses, not established by these calculations. No Lean compiler is invoked.
"""
from pathlib import Path
import json
import sympy as s
R=lambda t:s.Matrix([[s.cos(t),-s.sin(t)],[s.sin(t),s.cos(t)]])
J=s.Matrix([[0,-1],[1,0]])
D=lambda a,b:a[0]*b[1]-a[1]*b[0]
norm2=lambda a:a.dot(a)
results=[]
def check(name, expr, note='Polynomial/rational identity; geometric hypotheses checked in prose.'):
    entries=list(expr) if isinstance(expr,s.MatrixBase) else [expr]
    values=[s.trigsimp(s.expand_trig(s.cancel(s.expand(e)))) for e in entries]
    ok=all(v==0 for v in values)
    results.append({'name':name,'passed':ok,'residuals':[str(v) for v in values],'scope':note})
    if not ok: raise AssertionError((name,values))
x,y,c,z=s.symbols('x y c z', real=True)
check('Gram scalar expansion', (1-x*x)*(1-y*y)-(c-x*y)**2-(1+2*c*x*y-x*x-y*y-c*c))
q=s.symbols('q',real=True)
check('Full rotation half-angle identity', R(q)-s.eye(2)-2*s.sin(q/2)*R(q/2)*J,'Exact trigonometric matrix identity; excludes no q by itself.')
a=s.Matrix(s.symbols('a0 a1',real=True)); g=s.Matrix(s.symbols('g0 g1',real=True))
v=s.Matrix(s.symbols('v0 v1',real=True)); e=s.Matrix(s.symbols('e0 e1',real=True)); f=s.Matrix(s.symbols('f0 f1',real=True)); b=s.Matrix(s.symbols('b0 b1',real=True))
check('Quarter-turn determinant sign', v.dot(J*a)-D(a,v))
t,t1,t2,delta,lam,ss,xx,ww=s.symbols('t t1 t2 delta lam ss xx ww',real=True)
check('Full-hinge squared-radius difference', norm2(a-(1-t2)*g)-norm2(a-(1-t1)*g)-(t2-t1)*(2*a.dot(g)-(2-t1-t2)*norm2(g)))
C=-D(f,e)
check('Inward-cone Cramer decomposition',g-((-D(g,e)/C)*f+(-D(f,g)/C)*e),'Rational identity requiring det(f,e) != 0.')
check('Straight-seam angular determinant',D(b+t1*g,b+t2*g)-(t2-t1)*D(b,g))
check('Trimmed upper squared radius',norm2(a-delta*g)-(norm2(a)-2*delta*a.dot(g)+delta**2*norm2(g)))
B=b+t*g
check('Ray radial coefficient',D(B+ww*e,e)-(D(b,e)+t*D(g,e)))
wsol=-D(v,B)/D(v,e)
check('Ray horizontal coefficient',D(v,B+wsol*e),'Rational identity requiring det(v,e) != 0.')
Y=b[1]+t*g[1]+(xx-b[0]-t*g[0])*e[1]/e[0]
check('Cartesian trace slope',s.diff(Y,t)-D(e,g)/e[0],'Rational identity requiring e_x != 0.')
S=s.diag(1,-1); anew=b+g
bp=S*anew; gp=-S*g; ep=lam*S*e
new=bp+t*gp+ss*(1-t+t/lam)*ep
old=S*(b+(1-t)*g+ss*(1-(1-t)+(1-t)*lam)*e)
check('Positive-case full panel transport',new-old,'One reflection and rim reversal; lambda != 0, positive in geometry.')
check('Positive-case coherent determinant',D(ep,gp)-lam*D(e,g))
summary={'method':'exact symbolic simplification with SymPy','sympy_version':s.__version__,'total':len(results),'passed':sum(r['passed'] for r in results),'failed':sum(not r['passed'] for r in results),'not_checked':['geometric realization','global nonoverlap','inequality hypotheses','Lean compilation','dependency rebuild','novelty'],'checks':results}
out=Path(__file__).resolve().with_name('identity_checks.json');out.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
