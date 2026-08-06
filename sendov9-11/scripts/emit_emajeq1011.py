#!/usr/bin/env python3
"""EmajEq folding emitter (part of D10-6/D11-6 prep):

  * SendovNEmajEq.lean —
      Emaj10_eq   : MidChainN.Emaj 9 CTab10.c10 S a eta   = <explicit bracket poly>
      EmajTau11_eq: Split11.EmajTau CTab11.c11 S a eta tau = <explicit bracket poly>
    folded through SendovN.EInt.int_m_l (both-limits-free closed forms).

  * SendovNBoxEq10_40.lean — the ONE prototype hEq box identity (plan D10-6 perf
    probe): the degree-10 closed form P(S₄₀, λ₄₀) under the affine pullback of
    box 40 equals the shipped monomial table `Adata/Dscale` of
    Sendov911Box10_40.  Before emission this script REGENERATES the entire
    Adata table from the verifier's own `certificate_polynomial` arithmetic and
    asserts it matches the shipped file integer-for-integer, so the emitted
    identity is known-true before Lean sees it.

Every identity is sanity-checked at random rational points via two independent
computation routes (repeated polynomial multiplication vs the multinomial
bracket formula).  Exact rational arithmetic only.
"""
import os, random, re
from collections import defaultdict
from fractions import Fraction as F
from math import comb, factorial, lcm

from emit_rows1011 import D10

HERE = os.path.dirname(os.path.abspath(__file__))

C10 = {2: F(9, 2), 3: F(9), 4: F(2201, 100), 5: F(2201, 100), 6: F(877, 50),
       7: F(217, 20), 8: F(481, 100), 9: F(1)}
C11 = {2: F(5), 3: F(10), 4: F(1447, 50), 5: F(32), 6: F(3125, 108),
       7: F(2121, 100), 8: F(3125, 256), 9: F(509, 100), 10: F(1)}

PAIRS10 = [(m, (9 - m) // 2) for m in range(2, 10)]
PAIRS11 = [(m, (10 - m) // 2) for m in range(2, 11)]


def trinomial_coeffs(l):
    out = {}
    for p in range(l + 1):
        for q in range(l - p + 1):
            out[(p, q)] = factorial(l) // (factorial(p) * factorial(q) * factorial(l - p - q))
    return out


def rat(fr):
    fr = F(fr)
    if fr.denominator == 1:
        return f"({fr.numerator} : ℝ)"
    return f"({fr.numerator}/{fr.denominator} : ℝ)"


# ---------------- RHS text generation ----------------
def pow_txt(base, e):
    if e == 1:
        return base
    return f"{base} ^ {e}"


def bracket_terms(m, l, q1t, q2t, tail_mode=None):
    """List of term strings for  int v^m (1+Q1 v+Q2 v^2)^l dv  with
    tail_mode None -> limits (0,1): factor 1 (omitted);
    tail_mode 'head' -> limits (0,tau): factor tau^d;
    tail_mode 'tail' -> limits (tau,1): factor (1 - tau^d)."""
    tri = trinomial_coeffs(l)
    terms = []
    for (p, q), c in sorted(tri.items()):
        d = m + p + 2 * q + 1
        fs = [rat(F(c, d))]
        if p:
            fs.append(pow_txt(q1t, p))
        if q:
            fs.append(pow_txt(q2t, q))
        if tail_mode == 'head':
            fs.append(f"tau ^ {d}")
        elif tail_mode == 'tail':
            fs.append(f"(1 - tau ^ {d})")
        terms.append(" * ".join(fs))
    return terms


Q1_10 = "(-(2 * (9 - S + S * a ^ 2) / 9))"
Q1_11 = "(-(2 * (10 - S + S * a ^ 2) / 10))"
Q2T = "(a ^ 2 * (1 - eta ^ 2))"
Q2U = "(a ^ 2)"          # the q1-tail second coefficient


def rhs10():
    parts = []
    for m, l in PAIRS10:
        br = "\n          + ".join(bracket_terms(m, l, Q1_10, Q2T))
        parts.append(f"{rat(C10[m])} * eta ^ {m} * a ^ {m + 1} *\n"
                     f"        ({br})")
    return "\n      + ".join(parts)


def rhs11():
    parts = []
    for m, l in PAIRS11:
        br = "\n          + ".join(bracket_terms(m, l, Q1_11, Q2T, 'head'))
        parts.append(f"{rat(C11[m])} * eta ^ {m} * a ^ {m + 1} *\n"
                     f"        ({br})")
    t0 = "\n          + ".join(bracket_terms(0, 5, Q1_11, Q2T, 'tail'))
    t1 = "\n          + ".join(bracket_terms(0, 5, Q1_11, Q2U, 'tail'))
    parts.append(f"a *\n        (({t0})\n        + ({t1}))")
    return "\n      + ".join(parts)


# ---------------- independent-route sanity ----------------
def poly_pow_int(q1c, q2c, l, m, lo, hi):
    """int_lo^hi v^m (1+q1c v+q2c v^2)^l dv by repeated poly multiplication."""
    P = [F(1)]
    for _ in range(l):
        Q = [F(0)] * (len(P) + 2)
        for i, c in enumerate(P):
            Q[i] += c
            Q[i + 1] += c * q1c
            Q[i + 2] += c * q2c
        P = Q
    return sum(c * (F(hi) ** (m + i + 1) - F(lo) ** (m + i + 1)) / (m + i + 1)
               for i, c in enumerate(P))


def bracket_eval(m, l, q1c, q2c, lo, hi):
    tri = trinomial_coeffs(l)
    return sum(F(c, m + p + 2 * q + 1) * q1c ** p * q2c ** q
               * (F(hi) ** (m + p + 2 * q + 1) - F(lo) ** (m + p + 2 * q + 1))
               for (p, q), c in tri.items())


def sanity():
    rng = random.Random(20260806)
    for _ in range(25):
        S = F(rng.randint(1, 99), rng.randint(1, 9))
        a = F(rng.randint(1, 9), rng.randint(1, 9))
        eta = F(rng.randint(0, 9), rng.randint(1, 9))
        tau = F(rng.randint(0, 9), rng.randint(1, 9))
        q1_10 = -2 * (9 - S + S * a ** 2) / 9
        q1_11 = -2 * (10 - S + S * a ** 2) / 10
        q2t = a ** 2 * (1 - eta ** 2)
        # deg 10: Emaj over (0,1)
        lhs = sum(C10[m] * eta ** m * a ** (m + 1) * poly_pow_int(q1_10, q2t, l, m, 0, 1)
                  for m, l in PAIRS10)
        rhs = sum(C10[m] * eta ** m * a ** (m + 1) * bracket_eval(m, l, q1_10, q2t, 0, 1)
                  for m, l in PAIRS10)
        assert lhs == rhs, ("deg10", S, a, eta)
        # deg 11: EmajTau = head(0,tau) + a*(tail q0^5 + tail q1^5) over (tau,1)
        lhs = sum(C11[m] * eta ** m * a ** (m + 1) * poly_pow_int(q1_11, q2t, l, m, 0, tau)
                  for m, l in PAIRS11)
        lhs += a * (poly_pow_int(q1_11, q2t, 5, 0, tau, 1)
                    + poly_pow_int(q1_11, a ** 2, 5, 0, tau, 1))
        rhs = sum(C11[m] * eta ** m * a ** (m + 1) * bracket_eval(m, l, q1_11, q2t, 0, tau)
                  for m, l in PAIRS11)
        rhs += a * (bracket_eval(0, 5, q1_11, q2t, tau, 1)
                    + bracket_eval(0, 5, q1_11, a ** 2, tau, 1))
        assert lhs == rhs, ("deg11", S, a, eta, tau)
    print("sanity: 25 random rational points, both degrees, two routes agree")


# ---------------- SendovNEmajEq.lean ----------------
EMAJEQ_TEMPLATE = """import Mathlib
import SendovNMidChain
import SendovNSplit11
import SendovNEInt
import SendovNEsp10
import SendovNEsp11

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

/-!
# EmajEq folding for degrees 10 and 11 (generated)

Generated by `emit_emajeq1011.py`; do not hand-edit.  Rewrites the integral
majorants through the both-limits-free closed forms of `SendovN.EInt`
(`emit_eint1011.py`):

* `Emaj10_eq` : `MidChainN.Emaj 9 CTab10.c10 S a η` as an explicit polynomial
  in `(S, a, η)` — the degree-10 certificates' `E` term, with
  `Q1 = −2(9−S+Sa²)/9`, `Q2 = a²(1−η²)` spelled inline;
* `EmajTau11_eq` : `Split11.EmajTau CTab11.c11 S a η τ` as an explicit
  polynomial in `(S, a, η, τ)` — head integrals `(0,τ)`, τ-split tails `(τ,1)`
  (`q₀⁵` with `Q2 = a²(1−η²)`, `q₁⁵` with `Q2 = a²`).

Identities verified at 25 random rational points by two independent
computation routes before emission.  With these, each box `hEq` is a `rw`
followed by `ring`.
-/

namespace SendovN.EmajEq

open Finset intervalIntegral

/-- **`E_S(a,η)` at degree 10, evaluated** (the certificates' `E` term). -/
theorem Emaj10_eq (S a eta : ℝ) :
    MidChainN.Emaj 9 CTab10.c10 S a eta
      = {RHS10} := by
  unfold MidChainN.Emaj
  have hIcc : (Finset.Icc 2 9 : Finset ℕ) = {{2, 3, 4, 5, 6, 7, 8, 9}} := by decide
  rw [hIcc, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
{CVALS10}
{LVALS10}
  rw [{CREWRITES10}]
  have hq : ∀ v : ℝ, MidChainN.q0 9 S a eta v
      = 1 + {Q1_10} * v + {Q2T} * v ^ 2 := by
    intro v
    unfold MidChainN.q0
    push_cast
    ring
  simp only [hq]
  rw [EInt.int_2_3, EInt.int_3_3, EInt.int_4_2, EInt.int_5_2, EInt.int_6_1,
    EInt.int_7_1, EInt.int_8_0, EInt.int_9_0]
  norm_num
  ring

/-- **`E^{{(τ)}}_S(a,η)` at degree 11, evaluated** (the τ-split certificates'
`E` term; `τ = 1` degenerates to the unsplit form). -/
theorem EmajTau11_eq (S a eta tau : ℝ) :
    Split11.EmajTau CTab11.c11 S a eta tau
      = {RHS11} := by
  unfold Split11.EmajTau
  have hIcc : (Finset.Icc 2 10 : Finset ℕ) = {{2, 3, 4, 5, 6, 7, 8, 9, 10}} := by
    decide
  rw [hIcc, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
{CVALS11}
{LVALS11}
  rw [{CREWRITES11}]
  have hq0 : ∀ v : ℝ, MidChainN.q0 10 S a eta v
      = 1 + {Q1_11} * v + {Q2T} * v ^ 2 := by
    intro v
    unfold MidChainN.q0
    push_cast
    ring
  have hq1 : ∀ v : ℝ, Split11.q1 S a v
      = 1 + {Q1_11} * v + {Q2U} * v ^ 2 := by
    intro v
    unfold Split11.q1
    ring
  simp only [hq0, hq1]
  rw [EInt.int_2_4, EInt.int_3_3, EInt.int_4_3, EInt.int_5_2, EInt.int_6_2,
    EInt.int_7_1, EInt.int_8_1, EInt.int_9_0, EInt.int_10_0]
  have hi0 : IntervalIntegrable
      (fun v : ℝ => (1 + {Q1_11} * v + {Q2T} * v ^ 2) ^ 5)
      MeasureTheory.volume tau 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi1 : IntervalIntegrable
      (fun v : ℝ => (1 + {Q1_11} * v + {Q2U} * v ^ 2) ^ 5)
      MeasureTheory.volume tau 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h0 := EInt.int_0_5 tau 1 {Q1_11} {Q2T}
  have h1 := EInt.int_0_5 tau 1 {Q1_11} {Q2U}
  simp only [pow_zero, one_mul] at h0 h1
  rw [intervalIntegral.integral_add hi0 hi1, h0, h1]
  norm_num
  ring

end SendovN.EmajEq

#print axioms SendovN.EmajEq.Emaj10_eq
#print axioms SendovN.EmajEq.EmajTau11_eq
"""


def cval_block(cname, table, ell_n):
    cvals, lvals, rw = [], [], []
    for m in sorted(table):
        cvals.append(f"  have c{m} : CTab{ell_n + 1}.c{ell_n + 1} {m} = {rat(table[m])} := by"
                     f" norm_num [CTab{ell_n + 1}.c{ell_n + 1}]")
        lvals.append(f"  have l{m} : MidChainN.ell {ell_n} {m} = {(ell_n - m) // 2} := by"
                     f" norm_num [MidChainN.ell]")
        rw += [f"c{m}", f"l{m}"]
    return "\n".join(cvals), "\n".join(lvals), ", ".join(rw)


def emit_emajeq():
    cv10, lv10, rw10 = cval_block("c10", C10, 9)
    cv11, lv11, rw11 = cval_block("c11", C11, 10)
    src = EMAJEQ_TEMPLATE.format(
        RHS10=rhs10(), RHS11=rhs11(),
        CVALS10=cv10, LVALS10=lv10, CREWRITES10=rw10,
        CVALS11=cv11, LVALS11=lv11, CREWRITES11=rw11,
        Q1_10=Q1_10, Q1_11=Q1_11, Q2T=Q2T, Q2U=Q2U)
    out = os.path.join(HERE, "SendovNEmajEq.lean")
    with open(out, "w", encoding="utf-8", newline="\n") as f:
        f.write(src)
    print("wrote SendovNEmajEq.lean", len(src), "chars")


# ---------------- the box-40 hEq prototype ----------------
def poly_add(P, Q):
    R = defaultdict(F)
    for k, v in P.items():
        R[k] += v
    for k, v in Q.items():
        R[k] += v
    return {k: v for k, v in R.items() if v}


def poly_scale(P, c):
    c = F(c)
    return {k: v * c for k, v in P.items() if v * c}


def poly_mul(P, Q):
    R = defaultdict(F)
    for (i, j), c in P.items():
        for (k, l), d in Q.items():
            R[(i + k, j + l)] += c * d
    return {k: v for k, v in R.items() if v}


def poly_pow(P, n):
    R = {(0, 0): F(1)}
    B = P
    while n:
        if n & 1:
            R = poly_mul(R, B)
        B = poly_mul(B, B)
        n //= 2
    return R


def integrated_v_m_q_power10(m, ell, S):
    q = {0: {(0, 0): F(1)},
         1: {(0, 0): -F(2) * (9 - S) / 9, (2, 0): -F(2) * S / 9},
         2: {(2, 0): F(1), (2, 2): F(-1)}}
    D = {0: {(0, 0): F(1)}}
    for _ in range(ell):
        ND = {}
        for rv, P in D.items():
            for qv, Q in q.items():
                ND[rv + qv] = poly_add(ND.get(rv + qv, {}), poly_mul(P, Q))
        D = ND
    R = {}
    for rv, P in D.items():
        R = poly_add(R, poly_scale(P, F(1, m + rv + 1)))
    return R


def certificate_polynomial10(S, lam):
    P = {(0, 0): F(1, 10), (1, 0): F(-1, 10), (0, 2): F(1, 20)}
    c = F(2) * S / 9 - 1
    h = {(0, 0): c, (2, 0): -c, (2, 2): F(-1)}
    P = poly_add(P, poly_scale(poly_pow(h, 5), -F(1, 10) / lam))
    for m in range(2, 10):
        ell = (9 - m) // 2
        V = integrated_v_m_q_power10(m, ell, S)
        P = poly_add(P, poly_scale(poly_mul(V, {(m + 1, m): C10[m]}), -1))
    return P


def affine_rectangle(P, x0, x1, y0, y1):
    x0, x1, y0, y1 = map(F, (x0, x1, y0, y1))
    dx, dy = x1 - x0, y1 - y0
    R = defaultdict(F)
    for (i, j), c in P.items():
        for k in range(i + 1):
            cx = F(comb(i, k)) * x0 ** (i - k) * dx ** k
            for l in range(j + 1):
                R[(k, l)] += c * cx * F(comb(j, l)) * y0 ** (j - l) * dy ** l
    return {k: v for k, v in R.items() if v}


def parse_box40():
    path = os.path.join(HERE, "Sendov911Box10_40.lean")
    with open(path, encoding="utf-8") as f:
        text = f.read()
    m = re.search(r"def Adata : List \(List ℤ\) :=\n(.*?)\n\n", text, re.S)
    rows = re.findall(r"\[([-0-9, ]+)\]", m.group(1))
    A = [[int(x) for x in row.split(",")] for row in rows]
    d = re.search(r"def Dscale : ℤ := (\d+)", text)
    return A, int(d.group(1))


def check_and_emit_box40():
    # row-40 constants from the verifier's own arithmetic
    a0, a1 = F(40, 100), F(41, 100)
    nu, S = D10.sigma_bound(1 + a1)
    lam = D10.largest_lambda(S, a0, a1)
    Y = D10.sqrt_upper(1 - lam ** 2)
    assert (lam, Y) == (F(1227, 1250), F(3819, 20000)), (lam, Y)
    P = certificate_polynomial10(S, lam)
    R = affine_rectangle(P, a0, a1, 0, Y)
    D = 1
    for v in R.values():
        D = lcm(D, v.denominator)
    A = [[int(R.get((k, l), F(0)) * D) for l in range(11)] for k in range(11)]
    Afile, Dfile = parse_box40()
    assert D == Dfile, ("Dscale mismatch", D, Dfile)
    assert A == Afile, "Adata mismatch"
    print("box 40 pre-check: regenerated Adata/Dscale match the shipped file "
          "integer-for-integer")

    src = f"""import Mathlib
import SendovNEmajEq
import Sendov911Box10_40

set_option maxHeartbeats 4000000000
set_option maxRecDepth 100000

/-!
# D10-6 PROTOTYPE: the box-40 `hEq` identity (generated; perf probe)

Generated by `emit_emajeq1011.py`; do not hand-edit.  The degree-10 certificate
closed form `P(S₄₀, λ₄₀)(a, η)` — exactly the quantity `row_nonpos` proves
nonpositive — under the affine pullback `a = 2/5 + U/100`, `η = (3819/20000)V`
of box 40, equals the shipped monomial table `Adata/Dscale` of
`Sendov911Box10_40` (whose Bernstein positivity is kernel-checked).

The full Adata table was REGENERATED from `certificate_polynomial(S₄₀, λ₄₀)`
by the emitter and matched the shipped file integer-for-integer before this
file was written, so the identity below is known-true; the only question this
file answers is elaboration cost (`ring` at bidegree (10,10) with ~200-digit
rationals).

Row-40 constants (verifier arithmetic):
`S₄₀ = {S}`, `λ₄₀ = {lam}`, `Y₄₀ = {Y}`.
-/

namespace SendovN.BoxEq10

theorem box10_40_eq (U V : ℝ) :
    (1 - (2/5 + (1/100) * U)) / 10 + ((3819/20000) * V) ^ 2 / 20
      - MidChainN.hh 9 {rat(S)} (2/5 + (1/100) * U) ((3819/20000) * V) ^ 5
          / (10 * {rat(lam)})
      - MidChainN.Emaj 9 CTab10.c10 {rat(S)} (2/5 + (1/100) * U)
          ((3819/20000) * V)
    = ∑ k ∈ Finset.range 11, ∑ l ∈ Finset.range 11,
        ((Sendov911Box10_40.tab Sendov911Box10_40.Adata k l : ℝ)
          / (Sendov911Box10_40.Dscale : ℝ)) * U ^ k * V ^ l := by
  rw [EmajEq.Emaj10_eq]
  unfold MidChainN.hh
  push_cast
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Sendov911Box10_40.tab, Sendov911Box10_40.Adata, Sendov911Box10_40.Dscale,
    List.getD_cons_zero, List.getD_cons_succ, zero_add]
  norm_num
  ring

end SendovN.BoxEq10

#print axioms SendovN.BoxEq10.box10_40_eq
"""
    out = os.path.join(HERE, "SendovNBoxEq10_40.lean")
    with open(out, "w", encoding="utf-8", newline="\n") as f:
        f.write(src)
    print("wrote SendovNBoxEq10_40.lean", len(src), "chars")


if __name__ == "__main__":
    sanity()
    emit_emajeq()
    check_and_emit_box40()
