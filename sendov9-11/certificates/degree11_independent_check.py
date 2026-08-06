#!/usr/bin/env python3
"""Independent SymPy reconstruction of the degree-11 Sendov certificates.

This implementation does not import the primary verifier.  It symbolically
reconstructs both the termwise and split integral polynomials, maps each
rational rectangle to the unit square, and checks exact tensor-Bernstein
positivity.  Optional command-line arguments START END restrict the a-box
indices to START,...,END-1; this is convenient for parallel/chunked checking.
"""
import sys
from math import comb
import sympy as sp

Q=sp.Rational
a,y,v,u,w,x,Yv=sp.symbols('a y v u w x Y')
N=10; n=11
M0=Q(563,1000)
C={2:Q(5),3:Q(10),4:Q(1447,50),5:Q(32),6:Q(3125,108),
   7:Q(2121,100),8:Q(3125,256),9:Q(509,100),10:Q(1)}

# Discovery table only chooses which exact polynomial to try first.  The
# conclusion comes solely from the reconstructed rational Bernstein coefficients.
TAU_INDEX={37:[40,40,40,40,40,40,40,40,40,40],38:[40,40,40,40,40,40,40,40,40,40],39:[40,40,40,40,40,40,40,40,40,40],40:[40,40,40,40,40,40,40,40,40,40],41:[40,40,40,40,40,40,40,40,40,40],42:[40,40,40,40,40,40,40,40,40,40],43:[40,40,40,40,40,40,40,40,40,40],44:[40,40,40,40,40,40,40,40,40,40],45:[40,40,40,40,40,40,40,40,40,40],46:[40,40,40,40,40,40,40,40,40,39],47:[40,40,40,40,40,40,40,40,40,37],48:[40,40,40,40,40,40,40,40,40,36],49:[40,40,40,40,40,40,40,40,38,35],50:[40,40,40,40,40,40,40,40,37,34],51:[40,40,40,40,40,40,40,40,36,33],52:[40,40,40,40,40,40,40,39,35,32],53:[40,40,40,40,40,40,40,38,35,31],54:[40,40,40,40,40,40,40,38,34,31],55:[40,40,40,40,40,40,40,37,33,30],56:[40,40,40,40,40,40,40,36,32,29],57:[40,40,40,40,40,40,40,36,32,29],58:[40,40,40,40,40,40,40,35,31,28],59:[40,40,40,40,40,40,39,34,31,28],60:[40,40,40,40,40,40,39,34,30,28],61:[40,40,40,40,40,40,38,33,30,27],62:[40,40,40,40,40,40,37,33,29,27],63:[40,40,40,40,40,40,37,32,29,26],64:[40,40,40,40,40,40,36,32,29,26],65:[40,40,40,40,40,40,36,31,28,26],66:[40,40,40,40,40,40,35,31,28,25],67:[40,40,40,40,40,40,35,31,27,25],68:[40,40,40,40,40,40,34,30,27,25],69:[40,40,40,40,40,39,34,30,27,24],70:[40,40,40,40,40,39,33,29,26,24],71:[40,40,40,40,40,38,33,29,26,24],72:[40,40,40,40,40,38,32,29,26,24],73:[40,40,40,40,40,37,32,28,25,23],74:[40,40,40,40,40,36,31,28,25,23],75:[40,40,40,40,40,36,31,27,25,23],76:[40,40,40,40,40,35,31,27,25,22],77:[40,40,40,40,40,35,30,27,24,22],78:[40,40,40,40,40,35,30,27,24,22],79:[40,40,40,40,40,34,29,26,24,22],80:[40,40,40,40,40,34,29,26,23,22],81:[40,40,40,40,40,33,29,26,23,21],82:[40,40,40,40,40,33,29,26,23,21],83:[40,40,40,40,39,32,28,25,23,21],84:[40,40,40,40,38,32,28,25,23,21],85:[40,40,40,40,38,32,28,25,23,21],86:[40,40,40,40,37,31,28,25,23,21],87:[40,40,40,40,36,31,28,25,23,21],88:[40,40,40,40,36,31,27,25,23,21],89:[40,40,40,40,35,31,27,25,23,21]}


def sigma_bound(M):
    M=Q(M)
    nu=next(j for j in range(N+1) if M**j*M0**(N-j)>=n)
    S=(N-nu)/M0**2+(nu-1)/M**2+(M**(nu-1)*M0**(N-nu)/n)**2
    return nu,sp.factor(S)


def bern_univ(poly,z,z0,z1,degree):
    expr=sp.Poly(sp.expand(poly.subs(z,z0+(z1-z0)*u)),u)
    cc=[expr.nth(k) for k in range(degree+1)]
    return [sp.factor(sum(cc[k]*Q(comb(i,k),comb(degree,k)) for k in range(i+1))) for i in range(degree+1)]


def largest_lambda(S,a0,a1,D=100000):
    lo,hi=0,D
    while lo<hi:
        mid=(lo+hi+1)//2;lam=Q(mid,D)
        if min(bern_univ(S*a*a-N*lam*a+N-S,a,a0,a1,2))>=0:lo=mid
        else:hi=mid-1
    return Q(lo,D)


def sqrt_upper(q,D=100000):
    lo,hi=0,2*D
    while lo<hi:
        mid=(lo+hi)//2
        if Q(mid,D)**2>=q:hi=mid
        else:lo=mid+1
    return Q(lo,D)


def q0(S):
    return 1-Q(2,N)*(N-S+S*a*a)*v+a*a*(1-y*y)*v*v

def q1(S):
    return 1-Q(2,N)*(N-S+S*a*a)*v+a*a*v*v


def principal(S,lam):
    h=(Q(2)*S/N-1)*(1-a*a)-a*a*y*y
    return (1-a)/n+y*y/(2*n)-h**(n//2)/(n*lam)


def Ppoly(S,lam,tau_index):
    tau=Q(tau_index,40)
    q=q0(S)
    P=principal(S,lam)
    for m in range(2,N+1):
        ell=(N-m)//2
        P-=C[m]*a**(m+1)*y**m*sp.integrate(v**m*q**ell,(v,0,tau))
    if tau_index<40:
        P-=a*sp.integrate(q**5+q1(S)**5,(v,tau,1))
    return sp.Poly(sp.expand(P),a,y)


def tensor_bern(poly,z1,z2,z10,z11,z20,z21):
    expr=sp.expand(poly.as_expr().subs({z1:z10+(z11-z10)*u,z2:z20+(z21-z20)*w}))
    p=sp.Poly(expr,u,w);nx,ny=p.degree(u),p.degree(w)
    coeff={(i,j):p.coeff_monomial(u**i*w**j) for i in range(nx+1) for j in range(ny+1)}
    B={}
    for i in range(nx+1):
        for j in range(ny+1):
            B[i,j]=sp.factor(sum(coeff[k,l]*Q(comb(i,k),comb(nx,k))*Q(comb(j,l),comb(ny,l))
                                       for k in range(i+1) for l in range(j+1)))
    return B


def candidate_order(k):
    # Exact fallback menu around the discovery value, then a coarse global menu.
    seq=[k]
    for d in (1,-1,2,-2,3,-3):
        if 4<=k+d<=40:seq.append(k+d)
    seq += [40,38,36,34,32,30,28,26,24,22,20]
    out=[]
    for t in seq:
        if t not in out:out.append(t)
    return out


def check_range(start,end):
    global_min=None;where=None;count=0
    for i in range(start,end):
        a0,a1=Q(i,100),Q(i+1,100)
        _,S=sigma_bound(1+a1)
        lam=largest_lambda(S,a0,a1);Yu=sqrt_upper(1-lam**2)
        assert 2*lam>=a1
        cache={}
        for j in range(10):
            y0,y1=Yu*Q(j,10),Yu*Q(j+1,10)
            ok=None
            for ti in candidate_order(TAU_INDEX[i][j]):
                if ti not in cache: cache[ti]=Ppoly(S,lam,ti)
                B=tensor_bern(cache[ti],a,y,a0,a1,y0,y1)
                key=min(B,key=B.get);val=B[key]
                if val>0:
                    ok=(val,ti,key);break
            assert ok is not None,(i,j)
            count+=1
            if global_min is None or ok[0]<global_min:
                global_min,where=ok[0],(i,j,ok[1],ok[2])
        print('row',i,'passed')
    print('INDEPENDENT INTERIOR CHECK PASSED',start,end,count)
    print('minimum',where,global_min)


def check_boundary():
    _,S=sigma_bound(2);lam=Q(17,20)
    assert min(bern_univ(S*a*a-N*lam*a+N-S,a,Q(9,10),1,2))>=0
    P=Ppoly(S,lam,40).as_expr()
    expr=sp.cancel(sp.expand(P.subs({a:1-x*x,y:x*Yv}))/x**2)
    assert sp.denom(expr)==1
    Pb=sp.Poly(sp.expand(expr),x,Yv)
    B=tensor_bern(Pb,x,Yv,0,Q(8,25),0,Q(17,10))
    key=min(B,key=B.get);val=B[key]
    assert val>0
    Cdelta=(S*(1+Q(9,10))-N)/(N*Q(9,10))
    assert Q(17,10)**2>=2*Cdelta
    print('INDEPENDENT BOUNDARY CHECK PASSED',key,val)


def prelim():
    x0=Q(571,2000)
    pi_lower=Q(281476,89625)
    assert pi_lower > 11*x0
    assert 2*(x0-x0**3/6)>M0
    assert Q(127,100)**10<11
    _,S=sigma_bound(Q(137,100))
    assert min(bern_univ(S*a*a-N*a+N-S,a,Q(27,100),Q(37,100),2))>0
    assert C[7]**2>=Q(10**10,7**7*3**3)
    assert C[9]**2>=Q(10**10,9**9)

if __name__=='__main__':
    prelim()
    if len(sys.argv)==3:
        check_range(int(sys.argv[1]),int(sys.argv[2]))
    else:
        check_range(37,90)
        check_boundary()
