import sympy as sp
from math import comb
x,y,t,U,V=sp.symbols('x y t U V')
Q=(1-t)**2+x**2*t*(sp.Rational(19,10)-y**2*t)
C={2:sp.Rational(4),3:sp.Rational(264,35),4:sp.Rational(24),5:sp.Rational(56),6:sp.Rational(28),7:sp.Rational(8),8:sp.Rational(1)}
ell={2:3,3:2,4:2,5:1,6:1,7:0,8:0}
E=0
for m in range(2,9):
    E += C[m]*x**(m-2)*y**m*sp.integrate(t**m*Q**ell[m],(t,0,1-x**2))
P=sp.expand(sp.Rational(1,9)+y**2/sp.Integer(18)-sp.Rational(1,1000)-E)
poly=sp.Poly(P,x,y)
print('degree',poly.degree(x),poly.degree(y),'terms',len(poly.terms()))
# Exact Bernstein conversion by direct monomial identity, independently from verifier storage.
scaled=sp.Poly(sp.expand(P.subs({x:sp.Rational(8,25)*U,y:sp.Rational(7,5)*V})),U,V)
b={}
for k in range(25):
  for l in range(9):
    total=sp.Rational(0)
    for (i,j),coef in scaled.terms():
      if i<=k and j<=l:
        total += coef*sp.Rational(comb(k,i),comb(24,i))*sp.Rational(comb(l,j),comb(8,j))
    b[k,l]=sp.factor(total)
key=min(b,key=lambda z:b[z])
print('min key',key)
print('min',b[key])
print('minus .01',sp.factor(b[key]-sp.Rational(1,100)))
print('all',all(v>=sp.Rational(1,100) for v in b.values()))
# Reconstruct polynomial from Bernstein basis and prove exact equality.
recon=0
for (k,l),coef in b.items():
    recon += coef*sp.binomial(24,k)*U**k*(1-U)**(24-k)*sp.binomial(8,l)*V**l*(1-V)**(8-l)
print('reconstruction zero?',sp.Poly(sp.expand(recon-scaled.as_expr()),U,V).is_zero)
# Constants checks
m=sp.Rational(681,1000)
print('trig cert',sp.factor(3-(3*m-m**3)**2))
print('nu4 gap',sp.factor(9-16*m**4))
print('nu5 gap',sp.factor(32*m**3-9))
print('sig1 gap',sp.factor(sp.Rational(647,100)-3/m**2))
print('sig2 gap',sp.factor(sp.Rational(8,25)-256*m**6/81))
print('radical integer gap',1629**2*10**10-200**2*19**9)
