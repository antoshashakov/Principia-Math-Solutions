#!/usr/bin/env python3
"""Regenerate the 531 degree-11 Sendov box certificates with the Cauchy
constant c4 = 1447/50 (replacing Schoenberg's 70/3).

Construction is line-for-line the arithmetic of
`certificates/degree11_verify.py` (the ground-truth verifier); the only change
is the c-table entry c4.  Integer scaling follows the shipped box files
exactly (validated by reproducing Sendov911Box11_37_0 / _56_9 / Boundary
byte-identically from the old constant):

  * pull the certificate back to the unit square over the box rectangle,
  * D  = lcm of the denominators of the pulled-back monomial coefficients,
  * A  = coefficient * D (integer monomial table),
  * L  = lcm_{k,l} C(nx,k)*C(ny,l),  Q k l = L / (C(nx,k)*C(ny,l)),
  * cnum = min_{i,j} intTable i j  (exact; intTable = Bernstein numerator).

Per-box split parameters tau come from `boxes11v2-tau.csv` (column `tau_cau`,
the c4-experiment's best-margin tau; 37 boxes differ from the old files).
The emitter asserts, per box, that min intTable / (D*L) equals the
experiment's recorded exact margin `margin_cau_exact`.

Exact rational arithmetic only (Python fractions).  NO floats appear in any
emitted data.

Usage:
  python emit_boxes11v2.py --box 37 0      # one interior box
  python emit_boxes11v2.py --boundary      # the boundary box
  python emit_boxes11v2.py --all           # all 530 interior + boundary
"""
import argparse, csv, os, sys, time
from collections import defaultdict
from fractions import Fraction as F
from math import comb, lcm

HERE = os.path.dirname(os.path.abspath(__file__))
OUTDIR_DEFAULT = os.path.join(HERE, 'boxes11v2')
TAU_CSV = os.path.join(HERE, 'boxes11v2-tau.csv')

# ---------- arithmetic: verbatim from certificates/degree11_verify.py ----------
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
N=10;n=11

# ---------- the c-table: c4 is the CAUCHY constant ----------
C4=F(1447,50)
# exact validity of the Cauchy bound at m=4, N=10:  c^2 * 4^4 * 6^6 >= 10^10
assert C4**2 * 4**4 * 6**6 >= 10**10
C={2:F(5),3:F(10),4:C4,5:F(32),6:F(3125,108),7:F(2121,100),
   8:F(3125,256),9:F(509,100),10:F(1)}

def sigma_bound(M):
    M=F(M);assert M**N>=n
    nu=next(j for j in range(N+1) if M**j*M0**(N-j)>=n)
    S=F(N-nu)/M0**2+F(nu-1)/M**2+(M**(nu-1)*M0**(N-nu)/n)**2
    return nu,S

def largest_lambda(S,a0,a1,den=100000):
    lo,hi=0,den
    while lo<hi:
        mid=(lo+hi+1)//2;lam=F(mid,den)
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
    for m in range(2,N+1):
        V=integrated_interval(m,(N-m)//2,S,0,tau)
        P=add(P,scale(mul(V,monomial(m+1,m,C[m])),-1))
    V0=integrated_interval(0,5,S,tau,1,False)
    V1=integrated_interval(0,5,S,tau,1,True)
    tail=mul(add(V0,V1),monomial(1,0))
    P=add(P,scale(tail,-1))
    return P

def boundary_sub(P):
    R=defaultdict(F)
    for (i,j),c in P.items():
        for k in range(i+1):R[(2*k+j-2,j)]+=c*comb(i,k)*(-1)**k
    assert not {k:v for k,v in R.items() if k[0]<0 and v}
    return {k:v for k,v in R.items() if v}

# ---------- integer scaling (shipped box-file conventions) ----------
def to_int_table(R,nx,ny):
    D=1
    for v in R.values():D=lcm(D,v.denominator)
    A=[[int(R.get((k,l),F(0))*D) for l in range(ny+1)] for k in range(nx+1)]
    return D,A

def cofactors(nx,ny):
    L=1
    for k in range(nx+1):
        for l in range(ny+1):L=lcm(L,comb(nx,k)*comb(ny,l))
    Q=[[L//(comb(nx,k)*comb(ny,l)) for l in range(ny+1)] for k in range(nx+1)]
    return L,Q

def int_table_min(A,Q,nx,ny):
    best=None
    for i in range(nx+1):
        for j in range(ny+1):
            s=0
            for k in range(i+1):
                for l in range(j+1):
                    a=A[k][l]
                    if a:s+=a*comb(i,k)*comb(j,l)*Q[k][l]
            if best is None or s<best:best=s
    return best

# ---------- Lean emission ----------
def fmt_table(A):
    rows=[ '[' + ', '.join(str(v) for v in row) + ']' for row in A ]
    return '  [' + ',\n   '.join(rows) + ']'

INTERIOR_TEMPLATE = """/-
Machine-checked certificate for a degree-11 interior box of
`papers/sendov-9-11.tex`: `a ∈ [{a0}, {a1}]`, `eta ∈ [{e0}, {e1}]`,
split parameter `tau = {tau}`, bidegree (11,10).

Data re-derived from the paper's construction with the Cauchy constant
`c4 = 1447/50` in place of Schoenberg's `70/3`, and checked in the kernel by
`decide` on integer arithmetic.  No floating point, no `native_decide`.
-/
import Sendov911Bern

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace Sendov911Box11_{i}_{j}

open Finset Sendov911Bern

def tab (T : List (List ℤ)) (k l : ℕ) : ℤ := (T.getD k []).getD l 0

def Adata : List (List ℤ) :=
{Adata}

def Qdata : List (List ℤ) :=
{Qdata}

def Dscale : ℤ := {D}
def Lscale : ℤ := {L}
def cnum : ℤ := {cnum}

theorem hQ : ∀ k ∈ range 12, ∀ l ∈ range 11,
    (((11 : ℕ).choose k : ℤ) * ((10 : ℕ).choose l : ℤ)) * tab Qdata k l = Lscale := by
  decide

theorem hint : ∀ i ∈ range 12, ∀ j ∈ range 11,
    cnum ≤ intTable 11 10 (tab Adata) (tab Qdata) i j := by
  decide

/-- The paper's degree-11 certificate polynomial for this box, pulled back to the
unit square and scaled by `D`, is strictly positive there. -/
theorem box_positive {{U V : ℝ}} (hU0 : 0 ≤ U) (hU1 : U ≤ 1) (hV0 : 0 ≤ V) (hV1 : V ≤ 1) :
    0 < ∑ k ∈ range 12, ∑ l ∈ range 11,
          ((tab Adata k l : ℝ) / (Dscale : ℝ)) * U ^ k * V ^ l := by
  refine cert_of_intTable (tab Adata) (tab Qdata) (D := (Dscale : ℝ)) (L := (Lscale : ℝ))
    (Lz := Lscale) (cnum := cnum) ?_ rfl ?_ hQ ?_ hint hU0 hU1 hV0 hV1
  · norm_num [Dscale]
  · norm_num [Lscale]
  · norm_num [cnum]

end Sendov911Box11_{i}_{j}

#print axioms Sendov911Box11_{i}_{j}.box_positive
"""

BOUNDARY_TEMPLATE = """/-
Machine-checked **boundary** certificate for degree 11 of `papers/sendov-9-11.tex`:
`a ∈ [9/10, 1]` via `a = 1 - x²`, `y = x·Y`, divided by `x²`;
rectangle `x ∈ [0, 8/25]`, `Y ∈ [0, 17/10]`, bidegree (30,10).

Data re-derived from the paper's construction (`boundary_sub ∘ full_cert`) with
the Cauchy constant `c4 = 1447/50` in place of Schoenberg's `70/3`, and
cross-checked entry by entry against the verifier's rational Bernstein table.
Checked in the kernel by `decide` on integer arithmetic.  No floating point,
no `native_decide`.
-/
import Sendov911Bern

set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

namespace Sendov911Box11Boundary

open Finset Sendov911Bern

def tab (T : List (List ℤ)) (k l : ℕ) : ℤ := (T.getD k []).getD l 0

def Adata : List (List ℤ) :=
{Adata}

def Qdata : List (List ℤ) :=
{Qdata}

def Dscale : ℤ := {D}
def Lscale : ℤ := {L}
def cnum : ℤ := {cnum}

theorem hQ : ∀ k ∈ range 31, ∀ l ∈ range 11,
    (((30 : ℕ).choose k : ℤ) * ((10 : ℕ).choose l : ℤ)) * tab Qdata k l = Lscale := by
  decide

theorem hint : ∀ i ∈ range 31, ∀ j ∈ range 11,
    cnum ≤ intTable 30 10 (tab Adata) (tab Qdata) i j := by
  decide

/-- The degree-11 boundary certificate polynomial, pulled back to the unit
square and scaled by `D`, is strictly positive there. -/
theorem box_positive {{U V : ℝ}} (hU0 : 0 ≤ U) (hU1 : U ≤ 1) (hV0 : 0 ≤ V) (hV1 : V ≤ 1) :
    0 < ∑ k ∈ range 31, ∑ l ∈ range 11,
          ((tab Adata k l : ℝ) / (Dscale : ℝ)) * U ^ k * V ^ l := by
  refine cert_of_intTable (tab Adata) (tab Qdata) (D := (Dscale : ℝ)) (L := (Lscale : ℝ))
    (Lz := Lscale) (cnum := cnum) ?_ rfl ?_ hQ ?_ hint hU0 hU1 hV0 hV1
  · norm_num [Dscale]
  · norm_num [Lscale]
  · norm_num [cnum]

end Sendov911Box11Boundary

#print axioms Sendov911Box11Boundary.box_positive
"""

def write_lean(path,text):
    # shipped box files are UTF-8, no BOM, CRLF
    with open(path,'w',encoding='utf-8',newline='\r\n') as f:
        f.write(text)

# ---------- per-box work ----------
def load_tau():
    """(i,j) -> (tau Fraction, margin_cau_exact Fraction)."""
    taus={}
    with open(TAU_CSV,newline='') as f:
        for row in csv.DictReader(f):
            taus[(int(row['i']),int(row['j']))]=(F(row['tau_cau']),F(row['margin_cau_exact']))
    assert len(taus)==530,len(taus)
    return taus

class RowCache:
    """Certificates for one a-row, keyed by tau (row constants are c4-free)."""
    def __init__(self,i):
        self.i=i
        a0,a1=F(i,100),F(i+1,100)
        nu,S=sigma_bound(1+a1)
        lam=largest_lambda(S,a0,a1)
        Y=sqrt_upper(1-lam**2)
        assert 2*lam>=a1
        hc=F(2)*S/N-1
        assert hc>=0 and hc*(1-a0*a0)<=1
        self.a0,self.a1,self.S,self.lam,self.Y=a0,a1,S,lam,Y
        self.certs={}
    def cert(self,tau):
        if tau not in self.certs:
            self.certs[tau]=full_cert(self.S,self.lam) if tau==F(1) \
                            else split_cert(self.S,self.lam,tau)
        return self.certs[tau]

def emit_interior(row,j,tau,margin_ref,outdir):
    i=row.i
    y0=row.Y*F(j,10);y1=row.Y*F(j+1,10)
    R=affine_rectangle(row.cert(tau),row.a0,row.a1,y0,y1)
    D,A=to_int_table(R,11,10)
    L,Q=cofactors(11,10)
    cnum=int_table_min(A,Q,11,10)
    assert cnum>0,(i,j)
    margin=F(cnum,D*L)
    assert margin==margin_ref,('margin mismatch vs c4_boxes.csv',i,j,margin,margin_ref)
    text=INTERIOR_TEMPLATE.format(
        a0=row.a0,a1=row.a1,e0=y0,e1=y1,tau=tau,i=i,j=j,
        Adata=fmt_table(A),Qdata=fmt_table(Q),D=D,L=L,cnum=cnum)
    write_lean(os.path.join(outdir,f'Sendov911Box11_{i}_{j}.lean'),text)
    return margin

BOUNDARY_MARGIN_REF=F(
    58783677556526534894130458023382054597437967641316736415627899292265103487584055329979704400730870346517117975645536873614611721987,
    912101053412329291206924773004784115369169494407806670805684437303796151062630230259438944562244699909570044837892055511474609375000)

def emit_boundary(outdir):
    nub,Sb=sigma_bound(F(2))
    lamb=F(17,20)
    assert min(univ_bern([N-Sb,-N*lamb,Sb],F(9,10),F(1),2))>=0
    X=F(8,25);Yb=F(17,10)
    Cdelta=(Sb*(1+F(9,10))-N)/(N*F(9,10))
    assert X**2>=F(1,10) and Yb**2>=2*Cdelta
    Pb=boundary_sub(full_cert(Sb,lamb))
    R=affine_rectangle(Pb,F(0),X,F(0),Yb)
    D,A=to_int_table(R,30,10)
    L,Q=cofactors(30,10)
    cnum=int_table_min(A,Q,30,10)
    assert cnum>0
    margin=F(cnum,D*L)
    assert margin==BOUNDARY_MARGIN_REF,('boundary margin mismatch',margin)
    text=BOUNDARY_TEMPLATE.format(Adata=fmt_table(A),Qdata=fmt_table(Q),D=D,L=L,cnum=cnum)
    write_lean(os.path.join(outdir,'Sendov911Box11Boundary.lean'),text)
    return margin

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--box',nargs=2,type=int,metavar=('I','J'))
    ap.add_argument('--boundary',action='store_true')
    ap.add_argument('--all',action='store_true')
    ap.add_argument('--outdir',default=OUTDIR_DEFAULT)
    args=ap.parse_args()
    os.makedirs(args.outdir,exist_ok=True)
    t0=time.time()
    if args.box:
        taus=load_tau()
        i,j=args.box
        tau,mref=taus[(i,j)]
        row=RowCache(i)
        m=emit_interior(row,j,tau,mref,args.outdir)
        print(f'box {i}_{j} tau={tau} margin={float(m):.6e} (exact match vs csv)  '
              f't={time.time()-t0:.0f}s')
    elif args.boundary:
        m=emit_boundary(args.outdir)
        print(f'boundary margin={float(m):.6e} (exact match vs experiment)  '
              f't={time.time()-t0:.0f}s')
    elif args.all:
        taus=load_tau()
        count=0;gmin=None;gwhere=None
        for i in range(37,90):
            row=RowCache(i)
            for j in range(10):
                tau,mref=taus[(i,j)]
                m=emit_interior(row,j,tau,mref,args.outdir)
                count+=1
                if gmin is None or m<gmin:gmin=m;gwhere=(i,j)
            print(f'row {i} done  t={time.time()-t0:.0f}s',flush=True)
        mb=emit_boundary(args.outdir)
        print(f'emitted {count} interior + 1 boundary  '
              f'global min interior margin {float(gmin):.6e} at {gwhere}  '
              f'boundary margin {float(mb):.6e}  t={time.time()-t0:.0f}s')
    else:
        ap.error('choose --box I J, --boundary, or --all')

if __name__=='__main__':
    main()
