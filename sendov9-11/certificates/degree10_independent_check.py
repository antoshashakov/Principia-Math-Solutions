#!/usr/bin/env python3
"""Independent SymPy reconstruction of the degree-10 Sendov certificates.

This implementation does not import the primary verifier.  It reconstructs the
integrals symbolically in SymPy, performs the affine substitutions, converts
monomial coefficients to tensor Bernstein coefficients, and checks exact
positivity on all 50 interior boxes and the boundary box.
"""
import sympy as sp
from math import comb

Q = sp.Rational
a, y, v, u, w, x, Yvar = sp.symbols('a y v u w x Y')
M0 = Q(309,500)
C = {
    2: Q(9,2), 3: Q(9), 4: Q(2201,100), 5: Q(2201,100),
    6: Q(877,50), 7: Q(217,20), 8: Q(481,100), 9: Q(1),
}


def sigma_bound(M):
    M=sp.Rational(M)
    nu=next(j for j in range(10) if M**j*M0**(9-j)>=10)
    S=(9-nu)/M0**2+(nu-1)/M**2+(M**(nu-1)*M0**(9-nu)/10)**2
    return nu, sp.factor(S)


def bernstein_univariate(poly, z, z0, z1, degree):
    p=sp.Poly(sp.expand(poly.subs(z,z0+(z1-z0)*u)),u)
    coeff=[p.nth(k) for k in range(degree+1)]
    return [sp.factor(sum(coeff[k]*Q(comb(i,k),comb(degree,k)) for k in range(i+1)))
            for i in range(degree+1)]


def largest_lambda(S,a0,a1,D=100000):
    lo,hi=0,D
    while lo<hi:
        mid=(lo+hi+1)//2
        lam=Q(mid,D)
        B=bernstein_univariate(S*a*a-9*lam*a+9-S,a,a0,a1,2)
        if min(B)>=0: lo=mid
        else: hi=mid-1
    return Q(lo,D)


def smallest_sqrt_upper(q,D=100000):
    lo,hi=0,D
    while lo<hi:
        mid=(lo+hi)//2
        if Q(mid,D)**2>=q:hi=mid
        else:lo=mid+1
    return Q(lo,D)


def Ppoly(S,lam):
    q=1-Q(2,9)*(9-S+S*a*a)*v+a*a*(1-y*y)*v*v
    h=(Q(2)*S/9-1)*(1-a*a)-a*a*y*y
    P=(1-a)/10+y*y/20-h**5/(10*lam)
    for m in range(2,10):
        ell=(9-m)//2
        integ=sp.integrate(v**m*q**ell,(v,0,1))
        P-=C[m]*a**(m+1)*y**m*integ
    return sp.Poly(sp.expand(P),a,y)


def tensor_bernstein(poly, z1,z2, z10,z11,z20,z21):
    expr=sp.expand(poly.as_expr().subs({z1:z10+(z11-z10)*u,z2:z20+(z21-z20)*w}))
    p=sp.Poly(expr,u,w)
    nx,ny=p.degree(u),p.degree(w)
    coeff={(i,j):p.coeff_monomial(u**i*w**j) for i in range(nx+1) for j in range(ny+1)}
    B={}
    for i in range(nx+1):
        for j in range(ny+1):
            B[i,j]=sp.factor(sum(coeff[k,l]*Q(comb(i,k),comb(nx,k))*Q(comb(j,l),comb(ny,l))
                                   for k in range(i+1) for l in range(j+1)))
    return B


def main():
    assert (2*M0+1)**2<5
    for m in range(4,9):
        rhs=Q(9**9,m**m*(9-m)**(9-m))
        assert C[m]**2>=rhs

    # Low ranges.
    assert Q(129,100)**9<10
    _,Ss=sigma_bound(Q(7,5))
    assert min(bernstein_univariate(Ss*a*a-9*a+9-Ss,a,Q(29,100),Q(2,5),2))>0

    global_min=None
    global_where=None
    for i in range(40,90):
        a0,a1=Q(i,100),Q(i+1,100)
        _,S=sigma_bound(1+a1)
        lam=largest_lambda(S,a0,a1)
        Yu=smallest_sqrt_upper(1-lam**2)
        P=Ppoly(S,lam)
        B=tensor_bernstein(P,a,y,a0,a1,0,Yu)
        key=min(B,key=B.get); val=B[key]
        assert val>0
        if global_min is None or val<global_min:
            global_min,global_where=val,(a0,a1,key)

    # Boundary: substitute a=1-x^2, y=xY and divide by x^2.
    _,Sb=sigma_bound(2)
    lamb=Q(22,25)
    P=Ppoly(Sb,lamb).as_expr()
    expr=sp.cancel(sp.expand(P.subs({a:1-x*x,y:x*Yvar}))/x**2)
    assert sp.denom(expr)==1
    Pb=sp.Poly(sp.expand(expr),x,Yvar)
    B=tensor_bernstein(Pb,x,Yvar,0,Q(8,25),0,Q(31,20))
    kb=min(B,key=B.get); vb=B[kb]
    assert vb>0

    print('INDEPENDENT CHECK PASSED')
    print('interior minimum:',global_where,global_min)
    print('boundary minimum:',kb,vb)

if __name__=='__main__':
    main()
