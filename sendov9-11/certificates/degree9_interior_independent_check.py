#!/usr/bin/env python3
"""Independent SymPy reconstruction of the 18 degree-9 interior certificates."""

import sympy as sp
from math import comb

R = sp.Rational
a, y, v, u, w = sp.symbols('a y v u w')

C = {2:R(4),3:R(264,35),4:R(24),5:R(56),6:R(28),7:R(8),8:R(1)}
ELL = {2:3,3:2,4:2,5:1,6:1,7:0,8:0}

INTERVALS = [
    (R(9,20),R(19,40),R(11043,2000),R(49,50),R(199,1000)),
    (R(19,40),R(1,2),R(2783,500),R(239,250),R(587,2000)),
    (R(1,2),R(21,40),R(2257,400),R(1863,2000),R(91,250)),
    (R(21,40),R(11,20),R(1151,200),R(1811,2000),R(849,2000)),
    (R(11,20),R(23,40),R(11819,2000),R(879,1000),R(477,1000)),
    (R(23,40),R(3,5),R(764,125),R(1699,2000),R(66,125)),
    (R(3,5),R(5,8),R(637,100),R(817,1000),R(577,1000)),
    (R(5,8),R(13,20),R(13093,2000),R(401,500),R(239,400)),
    (R(13,20),R(27,40),R(13113,2000),R(81,100),R(1173,2000)),
    (R(27,40),R(7,10),R(3289,500),R(409,500),R(1151,2000)),
    (R(7,10),R(29,40),R(529,80),R(413,500),R(141,250)),
    (R(29,40),R(3,4),R(6661,1000),R(1669,2000),R(1103,2000)),
    (R(3,4),R(31,40),R(1681,250),R(843,1000),R(269,500)),
    (R(31,40),R(4,5),R(1701,250),R(213,250),R(131,250)),
    (R(4,5),R(33,40),R(2761,400),R(1723,2000),R(127,250)),
    (R(33,40),R(17,20),R(14041,2000),R(109,125),R(49,100)),
    (R(17,20),R(7,8),R(7161,1000),R(221,250),R(187,400)),
    (R(7,8),R(9,10),R(3663,500),R(359,400),R(883,2000)),
]

mins=[]
for idx,(lo,hi,S,lam,Y) in enumerate(INTERVALS,1):
    q = 1 - (8-S+S*a*a)*v/4 + a*a*(1-y*y)*v*v
    E = sum(C[m]*a**(m+1)*y**m*sp.integrate(v**m*q**ELL[m],(v,0,1)) for m in range(2,9))
    h = (S/4-1)*(1-a*a)-a*a*y*y
    P = sp.expand((1-a)/9+y*y/18-h**4/(9*lam)-E)
    expr = sp.expand(P.subs({a:lo+(hi-lo)*u,y:Y*w}))
    poly = sp.Poly(expr,u,w)
    nx,ny=poly.degree(u),poly.degree(w)
    coeff={(i,j):poly.coeff_monomial(u**i*w**j) for i in range(nx+1) for j in range(ny+1)}
    B={}
    for i in range(nx+1):
        for j in range(ny+1):
            B[i,j]=sum(coeff[k,l]*R(comb(i,k),comb(nx,k))*R(comb(j,l),comb(ny,l))
                         for k in range(i+1) for l in range(j+1))
    where,minimum=min(B.items(),key=lambda kv:kv[1])
    assert minimum>0
    # Reconstruct the original polynomial from the Bernstein coefficients.
    reconstructed=sum(
        b*sp.binomial(nx,i)*u**i*(1-u)**(nx-i)*sp.binomial(ny,j)*w**j*(1-w)**(ny-j)
        for (i,j),b in B.items()
    )
    assert sp.expand(reconstructed-expr)==0
    mins.append((minimum,idx,where))
    print(idx, minimum, where)

minimum,idx,where=min(mins)
assert minimum>R(1,2100)
print('GLOBAL',idx,where,minimum)
print('CERTIFIED independently by SymPy; global minimum > 1/2100.')
