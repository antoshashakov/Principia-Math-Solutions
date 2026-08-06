#!/usr/bin/env python3
"""Exact rational certificate generator/verifier for the degree-11 Sendov proof.

Run as written to check all 530 interior boxes and the boundary box.  The
calculation uses only Python integers, fractions, and binomial coefficients.
It can take several minutes; the same loop may be split into subranges without
changing any certificate.
"""
from collections import defaultdict
from fractions import Fraction as F
from math import comb

# Polynomial in (a,y)
def add(P,Q):
    R=defaultdict(F)
    for k,v in P.items():R[k]+=v
    for k,v in Q.items():R[k]+=v
    return {k:v for k,v in R.items() if v}
def scale(P,c):
    c=F(c);return {k:v*c for k,v in P.items() if v*c}
def mul(P,Q):
    R=defaultdict(F)
    for (i,j),c in P.items():
        for (k,l),d in Q.items():R[(i+k,j+l)]+=c*d
    return {k:v for k,v in R.items() if v}
def power(P,n):
    R={(0,0):F(1)};B=P
    while n:
        if n&1:R=mul(R,B)
        B=mul(B,B);n//=2
    return R
def monomial(i,j,c=1):return {(i,j):F(c)}

def affine_rectangle(P,x0,x1,y0,y1):
    x0,x1,y0,y1=map(F,(x0,x1,y0,y1));dx=x1-x0;dy=y1-y0
    R=defaultdict(F)
    for (i,j),c in P.items():
        for k in range(i+1):
            cx=F(comb(i,k))*x0**(i-k)*dx**k
            for l in range(j+1):
                R[(k,l)]+=c*cx*F(comb(j,l))*y0**(j-l)*dy**l
    return {k:v for k,v in R.items() if v}

def bernstein(P,nx=None,ny=None):
    if nx is None:nx=max((i for i,j in P),default=0)
    if ny is None:ny=max((j for i,j in P),default=0)
    B={}
    for i in range(nx+1):
        for j in range(ny+1):
            s=F(0)
            for (k,l),c in P.items():
                if k<=i and l<=j:
                    s+=c*F(comb(i,k),comb(nx,k))*F(comb(j,l),comb(ny,l))
            B[(i,j)]=s
    return B

def univ_bern(coeffs,x0,x1,degree=None):
    coeffs=list(map(F,coeffs));x0=F(x0);x1=F(x1);d=x1-x0
    if degree is None:degree=len(coeffs)-1
    mono=defaultdict(F)
    for k,c in enumerate(coeffs):
        for j in range(k+1):mono[j]+=c*comb(k,j)*x0**(k-j)*d**j
    out=[]
    for i in range(degree+1):
        s=F(0)
        for k,c in mono.items():
            if k<=i:s+=c*F(comb(i,k),comb(degree,k))
        out.append(s)
    return out

M0=F(563,1000)
C={2:F(5),3:F(10),4:F(1447,50),5:F(32),6:F(3125,108),7:F(2121,100),8:F(3125,256),9:F(509,100),10:F(1)}
N=10;n=11

def sigma_bound(M):
    M=F(M);assert M**N>=n
    nu=next(j for j in range(N+1) if M**j*M0**(N-j)>=n)
    S=F(N-nu)/M0**2+F(nu-1)/M**2+(M**(nu-1)*M0**(N-nu)/n)**2
    return nu,S

def largest_lambda(S,a0,a1,den=100000):
    lo,hi=0,den
    while lo<hi:
        mid=(lo+hi+1)//2;lam=F(mid,den)
        # S a^2 - N lam a + N-S >=0
        if min(univ_bern([N-S,-N*lam,S],a0,a1,2))>=0:lo=mid
        else:hi=mid-1
    return F(lo,den)

def sqrt_upper(q,den=100000):
    lo,hi=0,den*2
    while lo<hi:
        mid=(lo+hi)//2
        if F(mid,den)**2>=q:hi=mid
        else:lo=mid+1
    return F(lo,den)

def q_poly(S,unit_second=False):
    # q(v)=1 - 2(N-S+Sa^2)/N v + a^2(1-y^2)v^2
    q={0:{(0,0):F(1)},1:{(0,0):-F(2)*(N-S)/N,(2,0):-F(2)*S/N}}
    if unit_second:q[2]={(2,0):F(1)}
    else:q[2]={(2,0):F(1),(2,2):F(-1)}
    return q

def qpower_by_v(S,ell,unit_second=False):
    q=q_poly(S,unit_second)
    D={0:{(0,0):F(1)}}
    for _ in range(ell):
        ND={}
        for rv,P in D.items():
            for qv,Q in q.items():ND[rv+qv]=add(ND.get(rv+qv,{}),mul(P,Q))
        D=ND
    return D

def integrated_interval(m,ell,S,lo,hi,unit_second=False):
    lo=F(lo);hi=F(hi);D=qpower_by_v(S,ell,unit_second)
    R={}
    for rv,P in D.items():
        R=add(R,scale(P,(hi**(m+rv+1)-lo**(m+rv+1))/F(m+rv+1)))
    return R

def principal(S,lam):
    P={(0,0):F(1,n),(1,0):-F(1,n),(0,2):F(1,2*n)}
    c=F(2)*S/N-1
    h={(0,0):c,(2,0):-c,(2,2):F(-1)}
    return add(P,scale(power(h,n//2),-F(1,n)/lam))

def full_cert(S,lam):
    P=principal(S,lam)
    for m in range(2,N+1):
        V=integrated_interval(m,(N-m)//2,S,0,1)
        P=add(P,scale(mul(V,monomial(m+1,m,C[m])),-1))
    return P

def split_cert(S,lam,tau):
    tau=F(tau);P=principal(S,lam)
    # termwise early part
    for m in range(2,N+1):
        V=integrated_interval(m,(N-m)//2,S,0,tau)
        P=add(P,scale(mul(V,monomial(m+1,m,C[m])),-1))
    # tail a * int_tau^1 (q0^5+q1^5)dv
    V0=integrated_interval(0,5,S,tau,1,False)
    V1=integrated_interval(0,5,S,tau,1,True)
    tail=mul(add(V0,V1),monomial(1,0))
    P=add(P,scale(tail,-1))
    return P

def boundary_sub(P):
    # a=1-x^2,y=xY, divide x^2
    R=defaultdict(F)
    for (i,j),c in P.items():
        for k in range(i+1):R[(2*k+j-2,j)]+=c*comb(i,k)*(-1)**k
    assert not {k:v for k,v in R.items() if k[0]<0 and v}
    return {k:v for k,v in R.items() if v}

def try_box(P,a0,a1,y0,y1):
    R=affine_rectangle(P,a0,a1,y0,y1)
    B=bernstein(R)
    k,v=min(B.items(),key=lambda kv:kv[1])
    return v,k

# exact prelim checks
x0=F(571,2000)
pi_lower=F(281476,89625)  # Machin + alternating arctan bounds
assert pi_lower > 11*x0
assert 2*(x0-x0**3/F(6))>M0
assert F(127,100)**10<11
assert C[7]**2>=F(10**10,7**7*3**3)
assert C[9]**2>=F(10**10,9**9)
# local range to .37
nu0,S0=sigma_bound(F(137,100))
assert min(univ_bern([N-S0,-N,S0],F(27,100),F(37,100),2))>0
print('prelim pass',nu0,float(S0))

# Exact interior boxes.  The split parameter is selected from a fixed rational menu;
# every successful box is then certified solely by its Bernstein coefficients.
TAU_MENU=[F(1),F(19,20),F(9,10),F(17,20),F(4,5),F(3,4),F(7,10),F(13,20),F(3,5),F(11,20),F(1,2)]
# preferred order by vertical slice (small eta prefers the full termwise estimate)
PREF=[
 [F(1),F(19,20),F(9,10)],
 [F(1),F(19,20),F(9,10)],
 [F(1),F(19,20),F(9,10)],
 [F(1),F(19,20),F(9,10)],
 [F(1),F(19,20),F(9,10),F(17,20)],
 [F(1),F(17,20),F(4,5),F(3,4)],
 [F(1),F(4,5),F(3,4),F(7,10)],
 [F(3,4),F(7,10),F(13,20),F(3,5),F(1)],
 [F(13,20),F(3,5),F(11,20),F(7,10),F(1)],
 [F(3,5),F(11,20),F(1,2),F(13,20),F(1)],
]
fail=[];global_min=None;where=None;cert_count=0
for i in range(37,90):
    a0,a1=F(i,100),F(i+1,100)
    nu,S=sigma_bound(1+a1)
    lam=largest_lambda(S,a0,a1)
    Y=sqrt_upper(1-lam**2)
    assert 2*lam>=a1
    hc=F(2)*S/N-1
    assert hc>=0 and hc*(1-a0*a0)<=1
    cache={F(1):full_cert(S,lam)}
    for tau in TAU_MENU[1:]:
        cache[tau]=split_cert(S,lam,tau)
    for j in range(10):
        y0=Y*F(j,10);y1=Y*F(j+1,10)
        tried=[];best=None
        order=[]
        for t in PREF[j]+TAU_MENU:
            if t not in order:order.append(t)
        for tau in order:
            v,k=try_box(cache[tau],a0,a1,y0,y1)
            tried.append((v,tau,k))
            if best is None or v>best[0]:best=(v,tau,k)
            if v>0:break
        if best[0]<=0:
            fail.append((a0,a1,y0,y1,nu,S,lam,Y,best))
        else:
            cert_count+=1
            if global_min is None or best[0]<global_min:
                global_min=best[0];where=(a0,a1,j,best)
    print(i,'fail total',len(fail),'min',float(global_min) if global_min else None,flush=True)

print('boxes',cert_count,'fails',len(fail),'global',global_min,where)
for f in fail[:20]:print('FAIL',tuple(map(str,f[:4])),f[-1][0],f[-1][1:])

# boundary .9-1 full termwise
nub,Sb=sigma_bound(F(2))
lamb=F(17,20)
# verify L>=lambda on [.9,1]
assert min(univ_bern([N-Sb,-N*lamb,Sb],F(9,10),F(1),2))>=0
Pb=boundary_sub(full_cert(Sb,lamb))
X=F(8,25);Yb=F(17,10)
Cdelta=(Sb*(1+F(9,10))-N)/(N*F(9,10))
assert X**2 >= F(1,10)
assert Yb**2 >= 2*Cdelta
vb,kb=try_box(Pb,F(0),X,F(0),Yb)
print('boundary',float(vb),kb,vb)
