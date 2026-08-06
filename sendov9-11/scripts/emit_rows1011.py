#!/usr/bin/env python3
"""D10-4/5 and D11-4/5 emitter: SendovNRows10.lean / SendovNRows11.lean.

Per interior row i, emits
  * sigma_row_i : the Lemma-2.2 instance  sum 1/r_k^2 <= S_i  (SigmaGen.sigma_le_of),
  * L_row_i    : the L-quadratic  0 <= S_i a^2 - N lam_i a + N - S_i  on [a_i, a_{i+1}],
  * Y_row_i    : 1 - lam_i^2 <= Y_i^2,
  * lam_row_i  : beta_i <= 2 lam_i,
plus the boundary sigma instance / L-quadratic / prep facts.

EVERY constant (nu_i, S_i, lam_i, Y_i, S_b) is computed by the verifiers' own
arithmetic (`sigma_bound`, `largest_lambda`/`largest_grid_lambda`,
`sqrt_upper`/`smallest_grid_sqrt_upper`, transcribed verbatim from
certificates/degree10_verify.py and degree11_verify.py / emit_boxes11v2.py),
and cross-checked against the shipped box-file headers before anything is
written.  The emitter also re-checks, per row, the exact assertions the
verifiers make (L-quadratic Bernstein coefficients >= 0, Y^2 >= 1-lam^2,
2 lam >= beta), so the emitted nlinarith certificates are guaranteed to exist.

Exact rational arithmetic only.
"""
import os, re, sys
from collections import defaultdict
from fractions import Fraction as F
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))


def univ_bern(coeffs, x0, x1, degree=None):
    coeffs = list(map(F, coeffs)); x0 = F(x0); x1 = F(x1); d = x1 - x0
    if degree is None:
        degree = len(coeffs) - 1
    mono = defaultdict(F)
    for k, c in enumerate(coeffs):
        for j in range(k + 1):
            mono[j] += c * comb(k, j) * x0 ** (k - j) * d ** j
    out = []
    for i in range(degree + 1):
        s = F(0)
        for k, c in mono.items():
            if k <= i:
                s += c * F(comb(i, k), comb(degree, k))
        out.append(s)
    return out


class Deg:
    """Degree-specific data: N, n=C, M0, and verifier-verbatim helpers."""
    def __init__(self, N, C, M0):
        self.N, self.C, self.M0 = N, C, F(M0)

    def sigma_bound(self, M):
        M = F(M); N, C, M0 = self.N, self.C, self.M0
        assert M ** N >= C
        nu = next(j for j in range(N + 1) if M ** j * M0 ** (N - j) >= C)
        S = F(N - nu) / M0 ** 2 + F(nu - 1) / M ** 2 + (M ** (nu - 1) * M0 ** (N - nu) / C) ** 2
        return nu, S

    def largest_lambda(self, S, a0, a1, den=100000):
        N = self.N
        lo, hi = 0, den
        while lo < hi:
            mid = (lo + hi + 1) // 2; lam = F(mid, den)
            if min(univ_bern([N - S, -N * lam, S], a0, a1, 2)) >= 0:
                lo = mid
            else:
                hi = mid - 1
        return F(lo, den)

    def sqrt_upper(self, q, den=100000, double_hi=False):
        lo, hi = 0, (den * 2 if double_hi else den)
        while lo < hi:
            mid = (lo + hi) // 2
            if F(mid, den) ** 2 >= q:
                hi = mid
            else:
                lo = mid + 1
        return F(lo, den)


D10 = Deg(9, 10, F(309, 500))
D11 = Deg(10, 11, F(563, 1000))


def rat(fr):
    fr = F(fr)
    if fr.denominator == 1:
        return f"({fr.numerator} : ℝ)"
    return f"({fr.numerator}/{fr.denominator} : ℝ)"


# ---------------- box-header cross-checks ----------------
def crosscheck10():
    pat = re.compile(r"`a ∈ \[([^,]+), ([^\]]+)\]`, `y ∈ \[0, ([^\]]+)\]`")
    out = {}
    for i in range(40, 90):
        path = os.path.join(HERE, f"Sendov911Box10_{i}.lean")
        with open(path, encoding="utf-8") as f:
            head = f.read(600)
        m = pat.search(head)
        assert m, (i, head[:200])
        out[i] = (F(m.group(1)), F(m.group(2)), F(m.group(3)))
    return out


def crosscheck11():
    pat = re.compile(r"`a ∈ \[([^,]+), ([^\]]+)\]`, `eta ∈ \[([^,]+), ([^\]]+)\]`")
    out = {}
    for i in range(37, 90):
        for j in range(10):
            path = os.path.join(HERE, "boxes11v2", f"Sendov911Box11_{i}_{j}.lean")
            with open(path, encoding="utf-8") as f:
                head = f.read(700)
            m = pat.search(head)
            assert m, (i, j, head[:250])
            out[(i, j)] = tuple(F(m.group(k)) for k in range(1, 5))
    return out


# ---------------- row computation + emission ----------------
def row_constants(deg, i):
    a0, a1 = F(i, 100), F(i + 1, 100)
    M = 1 + a1
    nu, S = deg.sigma_bound(M)
    lam = deg.largest_lambda(S, a0, a1)
    Y = deg.sqrt_upper(1 - lam ** 2, double_hi=(deg.N == 10))
    # the verifiers' own per-row assertions
    b = univ_bern([deg.N - S, -deg.N * lam, S], a0, a1, 2)
    assert min(b) >= 0, (i, b)
    assert Y ** 2 >= 1 - lam ** 2
    assert 2 * lam >= a1
    hc = 2 * S / deg.N - 1
    assert hc >= 0 and hc * (1 - a0 * a0) <= 1
    return a0, a1, M, nu, S, lam, Y


def emit_sigma(name, N, m0, M, C, nu, S, indent=""):
    return f"""theorem {name} (r : Fin {N} → ℝ) (hlo : ∀ k, {rat(m0)} ≤ r k)
    (hhi : ∀ k, r k ≤ {rat(M)}) (hprod : ({C}:ℝ) ≤ ∏ k, r k) :
    ∑ k, 1 / r k ^ 2 ≤ {rat(S)} := by
  refine SigmaGen.sigma_le_of (m := {rat(m0)}) (M := {rat(M)}) (C := {C}) (nu := {nu})
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_ (by norm_num) r hlo hhi hprod
  intro j hj
  interval_cases j <;> norm_num
"""


def emit_L(name, N, S, lam, a0, a1):
    return f"""theorem {name} {{a : ℝ}} (h0 : {rat(a0)} ≤ a) (h1 : a ≤ {rat(a1)}) :
    0 ≤ {rat(S)} * a ^ 2 - {N} * {rat(lam)} * a + {N} - {rat(S)} := by
  nlinarith [sq_nonneg (a - {rat(a0)}), sq_nonneg ({rat(a1)} - a),
    mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
"""


def emit_degree(deg, lo, hi, m0_str, out_name, ns, boundary_lam, boundary_X, boundary_Y):
    N, C = deg.N, deg.C
    heads10 = crosscheck10() if N == 9 else None
    heads11 = crosscheck11() if N == 10 else None
    parts = [f"""import Mathlib
import SendovNSigma

set_option maxHeartbeats 4000000

/-!
# D{C}-4/5: the degree-{C} σ-rows, `L`-quadratics and side facts (generated)

Generated by `emit_rows1011.py`; do not hand-edit.  Every constant
(νᵢ, Sᵢ, λᵢ, Yᵢ, S_b) is computed by the verifiers' own `sigma_bound` /
`largest_lambda` / `sqrt_upper` arithmetic (degree{C}_verify.py) and
cross-checked against the shipped box-file headers before emission.

Per interior row `i` (`a ∈ [i/100, (i+1)/100]`):
* `sigma_row_i` : Lemma 2.2 instance `∑ 1/rₖ² ≤ Sᵢ` (`SigmaGen.sigma_le_of`);
* `L_row_i` : `0 ≤ Sᵢa² − {N}λᵢa + {N} − Sᵢ` on the interval (Bernstein
  certificate turned into an `nlinarith` cone combination);
* `Y_row_i` / `lam_row_i` : `1 − λᵢ² ≤ Yᵢ²` and `βᵢ ≤ 2λᵢ`.

Plus the boundary instance (`M = 2`, `λ_b = {boundary_lam}`) and its prep facts.
-/

namespace {ns}

open Finset

"""]
    names = []
    consts = []
    for i in range(lo, hi):
        a0, a1, M, nu, S, lam, Y = row_constants(deg, i)
        # cross-check against box headers
        if N == 9:
            ha0, ha1, hY = heads10[i]
            assert (ha0, ha1, hY) == (a0, a1, Y), (i, ha0, ha1, hY, a0, a1, Y)
        else:
            for j in range(10):
                e = heads11[(i, j)]
                assert e == (a0, a1, Y * F(j, 10), Y * F(j + 1, 10)), (i, j, e)
        consts.append((i, a0, a1, M, nu, S, lam, Y))
        parts.append(f"/-! ### Row {i}: `a ∈ [{a0}, {a1}]`, M = {M}, ν = {nu}, "
                     f"S = {S}, λ = {lam}, Y = {Y} -/\n\n")
        parts.append(emit_sigma(f"sigma_row_{i}", N, m0_str, M, C, nu, S))
        parts.append("\n")
        parts.append(emit_L(f"L_row_{i}", N, S, lam, a0, a1))
        parts.append(f"""
theorem Y_row_{i} : 1 - {rat(lam)} ^ 2 ≤ {rat(Y)} ^ 2 := by norm_num

theorem lam_row_{i} : {rat(a1)} ≤ 2 * {rat(lam)} := by norm_num

""")
        names += [f"sigma_row_{i}", f"L_row_{i}", f"Y_row_{i}", f"lam_row_{i}"]

    # ---- boundary ----
    nub, Sb = deg.sigma_bound(2)
    lamb = F(boundary_lam)
    assert min(univ_bern([N - Sb, -N * lamb, Sb], F(9, 10), F(1), 2)) >= 0
    Cd = (Sb * (1 + F(9, 10)) - N) / (N * F(9, 10))
    X, Yb = F(boundary_X), F(boundary_Y)
    assert X ** 2 >= F(1, 10) and Yb ** 2 >= 2 * Cd
    hcb = 2 * Sb / N - 1
    assert hcb >= 0 and hcb * (1 - F(81, 100)) <= 1
    assert 2 * lamb >= 1
    parts.append(f"/-! ### Boundary: `a ∈ [9/10, 1]`, M = 2, ν = {nub}, "
                 f"S_b = {Sb}, λ_b = {lamb}, X = {X}, Y_b = {Yb} -/\n\n")
    parts.append(emit_sigma("sigma_boundary", N, m0_str, 2, C, nub, Sb))
    parts.append("\n")
    parts.append(emit_L("L_boundary", N, Sb, lamb, F(9, 10), F(1)))
    parts.append(f"""
theorem lam_boundary : (1:ℝ) ≤ 2 * {rat(lamb)} := by norm_num

/-- `X² ≥ 1/10`: the boundary `x`-range fits in `[0, {X}]`. -/
theorem X_boundary : (1/10 : ℝ) ≤ {rat(X)} ^ 2 := by norm_num

/-- `Y_b² ≥ 2C_b`, `C_b = (S_b·(19/10) − {N})/({N}·(9/10))`. -/
theorem Yb_boundary :
    2 * (({rat(Sb)}) * (19/10) - {N}) / ({N} * (9/10)) ≤ {rat(Yb)} ^ 2 := by
  norm_num

""")
    names += ["sigma_boundary", "L_boundary", "lam_boundary", "X_boundary", "Yb_boundary"]
    parts.append(f"end {ns}\n\n")
    for nm in names:
        parts.append(f"#print axioms {ns}.{nm}\n")
    src = "".join(parts)
    with open(os.path.join(HERE, out_name), "w", encoding="utf-8", newline="\n") as f:
        f.write(src)
    print(f"wrote {out_name}: rows {lo}..{hi-1}, boundary nu={nub}, "
          f"Sb={Sb}, {len(src)} chars")
    return consts


if __name__ == "__main__":
    c10 = emit_degree(D10, 40, 90, F(309, 500), "SendovNRows10.lean",
                      "SendovN.Rows10", F(22, 25), F(8, 25), F(31, 20))
    c11 = emit_degree(D11, 37, 90, F(563, 1000), "SendovNRows11.lean",
                      "SendovN.Rows11", F(17, 20), F(8, 25), F(17, 10))
    # summary for the log
    print("deg10 nu range:", sorted({r[4] for r in c10}))
    print("deg11 nu range:", sorted({r[4] for r in c11}))
