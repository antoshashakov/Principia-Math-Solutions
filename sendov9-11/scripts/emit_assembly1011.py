#!/usr/bin/env python3
"""Final-assembly emitter for the Sendov 10/11 port (tasks a/b/c of the plan):

  --bdry      SendovNBdryEq10.lean / SendovNBdryEq11.lean : the TWO boundary
              hEq identities (bidegree (28,10) resp. (30,10)) — plan D10-6/D11-6
              boundary shapes, the only untimed rings.
  --chunk10 L SendovNRed10<L>.lean (L in A..E; 10 rows each): per row the Box
              value, the hEq identity, and the row reduction red_i.
  --row11 I   SendovNRed11_<I>.lean: 10 strip boxes + hEqs + rowPos + red_I.
  --bdryred   SendovNRed10Bdry.lean / SendovNRed11Bdry.lean.
  --covering  SendovNCovering10.lean / SendovNCovering11.lean.
  --reduction SendovNReduction10.lean / SendovNReduction11.lean.
  --all       everything.

TRUTH SAFEGUARD (as in the box-40 prototype): before emitting any hEq, the
entire integer monomial table Adata/Dscale is REGENERATED from the verifiers'
own arithmetic (certificate_polynomial / full_cert / split_cert / boundary_sub
+ affine_rectangle + lcm scaling) and matched against the shipped box file
integer-for-integer.  Exact rational arithmetic only.
"""
import argparse, os, re
from fractions import Fraction as F
from math import lcm

from emit_rows1011 import D10, D11, row_constants
from emit_emajeq1011 import certificate_polynomial10, affine_rectangle, rat
import emit_boxes11v2 as B11

HERE = os.path.dirname(os.path.abspath(__file__))


def write_file(name, src):
    with open(os.path.join(HERE, name), "w", encoding="utf-8", newline="\n") as f:
        f.write(src)
    print(f"wrote {name} ({len(src)} chars)")


# ---------------- shipped-table parsing + matching ----------------
def parse_box(path):
    with open(os.path.join(HERE, path), encoding="utf-8") as f:
        text = f.read()
    m = re.search(r"def Adata : List \(List ℤ\) :=\r?\n(.*?)\r?\n\r?\n", text, re.S)
    rows = re.findall(r"\[([-0-9, ]+)\]", m.group(1))
    A = [[int(x) for x in row.split(",")] for row in rows]
    d = re.search(r"def Dscale : ℤ := (\d+)", text)
    return A, int(d.group(1))


def int_table(R, nx, ny):
    D = 1
    for v in R.values():
        D = lcm(D, v.denominator)
    A = [[int(R.get((k, l), F(0)) * D) for l in range(ny + 1)] for k in range(nx + 1)]
    return A, D


def assert_match(R, nx, ny, path, tag):
    A, D = int_table(R, nx, ny)
    Af, Df = parse_box(path)
    assert D == Df, (tag, "Dscale mismatch")
    assert A == Af, (tag, "Adata mismatch")


# ---------------- degree-10 verifier constants ----------------
def deg10_row(i):
    a0, a1, M, nu, S, lam, Y = row_constants(D10, i)
    P = certificate_polynomial10(S, lam)
    R = affine_rectangle(P, a0, a1, 0, Y)
    assert_match(R, 10, 10, f"Sendov911Box10_{i}.lean", f"box10_{i}")
    return a0, a1, S, lam, Y


def deg10_boundary():
    nub, Sb = D10.sigma_bound(2)
    lamb = F(22, 25)
    X, Yb = F(8, 25), F(31, 20)
    P = certificate_polynomial10(Sb, lamb)
    Pb = B11.boundary_sub(P)
    R = affine_rectangle(Pb, 0, X, 0, Yb)
    assert_match(R, 28, 10, "Sendov911Box10Boundary.lean", "bdry10")
    # facts backing the reduction's nlinarith certificates
    assert Sb > 9
    c1 = 9 * Yb ** 2 - 2 * Sb
    g0 = F(81, 10) * Yb ** 2 - F(19, 5) * Sb + 18
    assert c1 > 0 and g0 > 0, (c1, g0)
    assert X ** 2 >= F(1, 10)
    return Sb, lamb, X, Yb


def deg11_boundary():
    nub, Sb = B11.sigma_bound(2)
    lamb = F(17, 20)
    X, Yb = F(8, 25), F(17, 10)
    Pb = B11.boundary_sub(B11.full_cert(Sb, lamb))
    R = affine_rectangle(Pb, 0, X, 0, Yb)
    assert_match(R, 30, 10, os.path.join("boxes11v2", "Sendov911Box11Boundary.lean"),
                 "bdry11")
    assert Sb > 10
    c1 = 10 * Yb ** 2 - 2 * Sb
    g0 = 9 * Yb ** 2 - F(19, 5) * Sb + 20
    assert c1 > 0 and g0 > 0, (c1, g0)
    assert X ** 2 >= F(1, 10)
    return Sb, lamb, X, Yb


# ---------------- Lean text helpers ----------------
CAST10 = "(((9:ℕ):ℝ) + 1)"


def lhs10(S, A, E, lam):
    return (f"(1 - {A}) / {CAST10} + {E} ^ 2 / (2 * {CAST10})\n"
            f"      - MidChainN.hh 9 {rat(S)} {A} {E} ^ 5 / ({CAST10} * {rat(lam)})\n"
            f"      - MidChainN.Emaj 9 CTab10.c10 {rat(S)} {A} {E}")


def lhs11(S, A, E, lam, tau):
    return (f"(1 - {A}) / 11 + {E} ^ 2 / 22\n"
            f"      - MidChainN.hh 10 {rat(S)} {A} {E} ^ 5 / (11 * {rat(lam)})\n"
            f"      - Split11.EmajTau CTab11.c11 {rat(S)} {A} {E} {rat(tau)}")


def rhs_sum(ns, nx, U="U", V="V"):
    return (f"∑ k ∈ Finset.range {nx + 1}, ∑ l ∈ Finset.range 11,\n"
            f"        (({ns}.tab {ns}.Adata k l : ℝ)\n"
            f"          / ({ns}.Dscale : ℝ)) * {U} ^ k * {V} ^ l")


EQ_PROOF10 = """  rw [EmajEq.Emaj10_eq]
  unfold MidChainN.hh
  push_cast
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    {ns}.tab, {ns}.Adata, {ns}.Dscale,
    List.getD_cons_zero, List.getD_cons_succ, zero_add]
  norm_num
  ring"""

EQ_PROOF11_S2 = """  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    {ns}.tab, {ns}.Adata, {ns}.Dscale,
    List.getD_cons_zero, List.getD_cons_succ, zero_add]
  norm_num
  ring"""

EQ_PROOF11 = """  rw [EmajEq.EmajTau11_eq]
  unfold MidChainN.hh
  push_cast
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    {ns}.tab, {ns}.Adata, {ns}.Dscale,
    List.getD_cons_zero, List.getD_cons_succ, zero_add]
  norm_num
  ring"""


def box_def(name, ns, nx):
    return f"""noncomputable def {name} : Box where
  nx := {nx}
  ny := 10
  A := {ns}.tab {ns}.Adata
  D := ({ns}.Dscale : ℝ)
  hD := by norm_num [{ns}.Dscale]
"""


# ---------------- (a) the two boundary hEq prototypes ----------------
def emit_bdry_eqs():
    Sb, lamb, X, Yb = deg10_boundary()
    A = "(1 - ((8/25 : ℝ) * U) ^ 2)"
    E = "(((8/25 : ℝ) * U) * ((31/20 : ℝ) * V))"
    src = f"""import Mathlib
import SendovNEmajEq
import Sendov911Box10Boundary

set_option maxHeartbeats 4000000000
set_option maxRecDepth 1000000

/-!
# D10-6 boundary hEq (generated by emit_assembly1011.py; do not hand-edit)

The degree-10 certificate closed form at `S_b, λ_b = 22/25` under the boundary
substitution `a = 1 − x²`, `η = x·Y` and the pullback `x = (8/25)U`,
`Y = (31/20)V`, equals `x²` times the shipped bidegree-(28,10) boundary table.
Adata/Dscale regenerated from `boundary_sub ∘ certificate_polynomial` and
matched integer-for-integer before emission.
-/

namespace SendovN.BdryEq10

theorem bdry10_eq (U V : ℝ) :
    {lhs10(Sb, A, E, lamb)}
    = ((8/25 : ℝ) * U) ^ 2 * ({rhs_sum('Sendov911Box10Boundary', 28)}) := by
{EQ_PROOF10.format(ns='Sendov911Box10Boundary')}

end SendovN.BdryEq10

#print axioms SendovN.BdryEq10.bdry10_eq
"""
    write_file("SendovNBdryEq10.lean", src)

    Sb, lamb, X, Yb = deg11_boundary()
    A = "(1 - ((8/25 : ℝ) * U) ^ 2)"
    E = "(((8/25 : ℝ) * U) * ((17/10 : ℝ) * V))"
    src = f"""import Mathlib
import SendovNEmajEq
import Sendov911Box11Boundary

set_option maxHeartbeats 4000000000
set_option maxRecDepth 1000000

/-!
# D11-6 boundary hEq (generated by emit_assembly1011.py; do not hand-edit)

The degree-11 τ-split certificate closed form at `τ = 1` (which degenerates to
the unsplit form used by `boundary_sub ∘ full_cert`), at `S_b, λ_b = 17/20`,
under `a = 1 − x²`, `η = x·Y`, `x = (8/25)U`, `Y = (17/10)V`, equals `x²` times
the shipped bidegree-(30,10) boundary table (c₄ = 1447/50 Cauchy data,
kernel-checked in `boxes11v2/`).  Adata/Dscale matched integer-for-integer
before emission.
-/

namespace SendovN.BdryEq11

theorem bdry11_eq (U V : ℝ) :
    {lhs11(Sb, A, E, lamb, F(1))}
    = ((8/25 : ℝ) * U) ^ 2 * ({rhs_sum('Sendov911Box11Boundary', 30)}) := by
{EQ_PROOF11.format(ns='Sendov911Box11Boundary')}

end SendovN.BdryEq11

#print axioms SendovN.BdryEq11.bdry11_eq
"""
    write_file("SendovNBdryEq11.lean", src)


# ---------------- (b/c) degree-10 chunk files ----------------
RED10_TEMPLATE = """theorem red_{i} (mu : ℂ) (Df : Fin 9 → ℂ) (rr : Fin 9 → ℝ) (a eta sig : ℝ)
    (h0 : {a0r} ≤ a) (h1 : a ≤ {a1r})
    (heta0 : 0 ≤ eta) (hnormSq : Complex.normSq mu = 1 - eta ^ 2)
    (hloc : (9:ℝ) ≤ 9 * a * mu.re + (1 - a ^ 2) * sig)
    (hsigeq : sig = ∑ k, 1 / rr k ^ 2)
    (hrlo : ∀ k, (309/500 : ℝ) ≤ rr k) (hrhi : ∀ k, rr k ≤ a + 1)
    (hprod : (10:ℝ) ≤ ∏ k, rr k)
    (hz : ∑ j, Df j = 0)
    (hD2 : ∑ j, ‖Df j‖ ^ 2 ≤ 9 * eta ^ 2)
    (hI : ‖∫ t in (0:ℝ)..a, ∏ j, ((1:ℂ) - (t:ℂ) * (mu + Df j))‖ < a / 10) :
    ∃ U V : ℝ, 0 ≤ U ∧ U ≤ 1 ∧ 0 ≤ V ∧ V ≤ 1 ∧
      Sendov911Capstone.Box.poly box_{i} U V ≤ 0 := by
  have ha0 : (0:ℝ) < a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hsig : sig ≤ {Sr} := by
    rw [hsigeq]
    exact Rows10.sigma_row_{i} rr hrlo (fun k => le_trans (hrhi k) (by linarith)) hprod
  have hL := Rows10.L_row_{i} h0 h1
  have hloc' : ((9:ℕ):ℝ) ≤ ((9:ℕ):ℝ) * a * mu.re + (1 - a ^ 2) * sig := by
    push_cast
    exact hloc
  have hkey := MidChainN.key_of_loc ha1 ha0.le hloc' hsig
  have hL' : 0 ≤ {Sr} * a ^ 2 - ((9:ℕ):ℝ) * {lamr} * a + ((9:ℕ):ℝ) - {Sr} := by
    push_cast
    exact hL
  have hlamu := MidChainN.lam_le_u (by norm_num) ha0 hkey hL'
  have hmunorm := MidChainN.lam_le_norm mu hlamu
  have hmu0 : mu ≠ 0 := by
    intro hcon
    rw [hcon] at hmunorm
    simp only [norm_zero] at hmunorm
    norm_num at hmunorm
  have hetale := MidChainN.eta_sq_le mu (by norm_num) hnormSq hmunorm
  have hetaY : eta ≤ {Yr} :=
    MidChainN.eta_le_Y (by norm_num) heta0 hetale Rows10.Y_row_{i}
  have hP := MidChainN.row_nonpos (N := 9) (alpha := {a0r}) (beta := {a1r})
    (S := {Sr}) (lam := {lamr}) (sigma := sig) (by norm_num)
    CTab10.c10 (fun m _ => CTab10.c10_nonneg m) mu Df a eta
    (by norm_num) (by norm_num) (by norm_num) Rows10.lam_row_{i} h0 h1
    heta0 hnormSq hloc' hsig hL' hz
    (CTab10.cTable10 Df eta heta0 hz hD2)
    (by push_cast; norm_num; exact JBoundN.J_closed_form_deg10 hmu0 a)
    (by push_cast; norm_num; exact hI)
  refine ⟨100 * (a - {a0r}), eta / {Yr}, by linarith, by linarith,
    div_nonneg heta0 (by norm_num), (div_le_one (by norm_num)).mpr hetaY, ?_⟩
  have heq := eq_{i} (100 * (a - {a0r})) (eta / {Yr})
  rw [show {a0r} + (1/100) * (100 * (a - {a0r})) = a by ring] at heq
  rw [show {Yr} * (eta / {Yr}) = eta by field_simp <;> ring] at heq
  exact le_of_eq_of_le heq.symm hP
"""


def emit_chunk10(letter):
    lo = 40 + 10 * "ABCDE".index(letter)
    rows = range(lo, lo + 10)
    imports = "\n".join(f"import Sendov911Box10_{i}" for i in rows)
    parts = [f"""import Mathlib
import SendovNEmajEq
import SendovNRows10
import SendovNCoverGrid
{imports}

set_option maxHeartbeats 4000000000
set_option maxRecDepth 100000

/-!
# D10-6/7 assembly chunk {letter} (rows {lo}–{lo + 9}; generated by
emit_assembly1011.py, do not hand-edit)

Per row: the `Box` value, the hEq identity against the shipped monomial table
(regenerated from the verifier arithmetic and matched integer-for-integer
before emission), and the row reduction `red_i` (`row_nonpos` → pullback).
-/

namespace SendovN.Red10{letter}

open Finset Sendov911Capstone

"""]
    names = []
    for i in rows:
        a0, a1, S, lam, Y = deg10_row(i)
        ns = f"Sendov911Box10_{i}"
        A = f"({rat(a0)} + (1/100) * U)"
        E = f"({rat(Y)} * V)"
        parts.append(f"/-! ### Row {i}: `a ∈ [{a0}, {a1}]`, S = {S}, λ = {lam}, "
                     f"Y = {Y} -/\n\n")
        parts.append(box_def(f"box_{i}", ns, 10) + "\n")
        parts.append(f"""theorem eq_{i} (U V : ℝ) :
    {lhs10(S, A, E, lam)}
    = {rhs_sum(ns, 10)} := by
{EQ_PROOF10.format(ns=ns)}

""")
        parts.append(RED10_TEMPLATE.format(
            i=i, a0r=rat(a0), a1r=rat(a1), Sr=rat(S), lamr=rat(lam), Yr=rat(Y)))
        parts.append("\n")
        names += [f"eq_{i}", f"red_{i}"]

    boxlist = ", ".join(f"box_{i}" for i in rows)
    parts.append(f"""noncomputable def chunk : List Box :=
  [{boxlist}]

theorem chunkPos : CoveringPositive chunk := by
  unfold chunk
""")
    tail = "  refine "
    for i in rows:
        tail += (f"coveringPositive_cons (fun _ _ h1 h2 h3 h4 => "
                 f"Sendov911Box10_{i}.box_positive h1 h2 h3 h4)\n    (")
    tail += "coveringPositive_nil" + ")" * 10 + "\n"
    parts.append(tail)
    names.append("chunkPos")
    parts.append(f"\nend SendovN.Red10{letter}\n\n")
    for nm in names:
        parts.append(f"#print axioms SendovN.Red10{letter}.{nm}\n")
    write_file(f"SendovNRed10{letter}.lean", "".join(parts))


# ---------------- (b/c) degree-11 row files ----------------
RED11_BRANCH = """  · -- strip j = {j}, τ = {tau}
    push_cast at hja hjb
    have hP := Split11.split_row_nonpos (alpha := {a0r}) (beta := {a1r})
      (S := {Sr}) (lam := {lamr}) (sigma := sig) (tau := {taur}) CTab11.c11
      (fun m _ => CTab11.c11_nonneg m) mu Df a eta
      (by norm_num) (by norm_num) (by norm_num) Rows11.lam_row_{i}
      (by norm_num) (by norm_num) h0 h1 heta0 hnormSq hloc hsig hL hz hY1 hc hI
    refine ⟨box_{i}_{j}, mem_{i}_{j}, 100 * (a - {a0r}), (eta - {y0r}) / {stepr},
      by linarith, by linarith, div_nonneg (by linarith) (by norm_num),
      (div_le_one (by norm_num)).mpr (by linarith), ?_⟩
    have heq := eq_{i}_{j} (100 * (a - {a0r})) ((eta - {y0r}) / {stepr})
    rw [show {a0r} + (1/100) * (100 * (a - {a0r})) = a by ring] at heq
    rw [show {y0r} + {stepr} * ((eta - {y0r}) / {stepr}) = eta by field_simp <;> ring] at heq
    exact le_of_eq_of_le heq.symm hP
"""

RED11_HEAD = """theorem red_{i} (mu : ℂ) (Df : Fin 10 → ℂ) (rr : Fin 10 → ℝ) (a eta sig : ℝ)
    (h0 : {a0r} ≤ a) (h1 : a ≤ {a1r})
    (heta0 : 0 ≤ eta) (hnormSq : Complex.normSq mu = 1 - eta ^ 2)
    (hloc : (10:ℝ) ≤ 10 * a * mu.re + (1 - a ^ 2) * sig)
    (hsigeq : sig = ∑ k, 1 / rr k ^ 2)
    (hrlo : ∀ k, (563/1000 : ℝ) ≤ rr k) (hrhi : ∀ k, rr k ≤ a + 1)
    (hprod : (11:ℝ) ≤ ∏ k, rr k)
    (hz : ∑ j, Df j = 0) (hY1 : ∀ j, ‖mu + Df j‖ ≤ 1)
    (hD2 : ∑ j, ‖Df j‖ ^ 2 ≤ 10 * eta ^ 2)
    (hI : ‖∫ t in (0:ℝ)..a, ∏ j, ((1:ℂ) - (t:ℂ) * (mu + Df j))‖ < a / 11) :
    ∃ b ∈ row_{i}, ∃ U V : ℝ, 0 ≤ U ∧ U ≤ 1 ∧ 0 ≤ V ∧ V ≤ 1 ∧
      Sendov911Capstone.Box.poly b U V ≤ 0 := by
  have ha0 : (0:ℝ) < a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hsig : sig ≤ {Sr} := by
    rw [hsigeq]
    exact Rows11.sigma_row_{i} rr hrlo (fun k => le_trans (hrhi k) (by linarith)) hprod
  have hL := Rows11.L_row_{i} h0 h1
  have hc := CTab11.cTable11 Df eta heta0 hz hD2
  have hloc' : ((10:ℕ):ℝ) ≤ ((10:ℕ):ℝ) * a * mu.re + (1 - a ^ 2) * sig := by
    push_cast
    exact hloc
  have hkey := MidChainN.key_of_loc ha1 ha0.le hloc' hsig
  have hL' : 0 ≤ {Sr} * a ^ 2 - ((10:ℕ):ℝ) * {lamr} * a + ((10:ℕ):ℝ) - {Sr} := by
    push_cast
    exact hL
  have hlamu := MidChainN.lam_le_u (by norm_num) ha0 hkey hL'
  have hmunorm := MidChainN.lam_le_norm mu hlamu
  have hetale := MidChainN.eta_sq_le mu (by norm_num) hnormSq hmunorm
  have hetaY : eta ≤ {Yr} :=
    MidChainN.eta_le_Y (by norm_num) heta0 hetale Rows11.Y_row_{i}
  obtain ⟨j, hj, hja, hjb⟩ := Cover.cover_grid (by norm_num : (0:ℝ) < {stepr}) 0 10
    (by norm_num) eta heta0 (by push_cast; linarith)
  interval_cases j
"""


def poly_txt(P, va="a", ve="eta"):
    terms = []
    for (ia, je) in sorted(P):
        c = P[(ia, je)]
        fs = [rat(c)]
        if ia:
            fs.append(f"{va} ^ {ia}" if ia > 1 else va)
        if je:
            fs.append(f"{ve} ^ {je}" if je > 1 else ve)
        terms.append(" * ".join(fs))
    return "\n      + ".join(terms)


def emit_row11(i, taus):
    row = B11.RowCache(i)
    a0, a1, S, lam, Y = row.a0, row.a1, row.S, row.lam, row.Y
    step = Y / 10
    imports = "\n".join(f"import Sendov911Box11_{i}_{j}" for j in range(10))
    parts = [f"""import Mathlib
import SendovNEmajEq
import SendovNRows11
import SendovNCoverGrid
{imports}

set_option maxHeartbeats 4000000000
set_option maxRecDepth 100000

/-!
# D11-6/7 assembly for row {i} (generated by emit_assembly1011.py; do not
hand-edit)

`a ∈ [{a0}, {a1}]`, S = {S}, λ = {lam}, Y = {Y}.  Per η-strip j: the `Box`
value, the hEq identity against the shipped `boxes11v2` table (regenerated
from the verifier arithmetic — `split_cert` at the box's recorded τ — and
matched integer-for-integer before emission), the strip membership, and the
row reduction `red_{i}` (strip cover → `split_row_nonpos` → pullback).
-/

namespace SendovN.Red11_{i}

open Finset Sendov911Capstone

"""]
    names = []
    branchparts = []
    # stage 1: one "certificate polynomial, evaluated" lemma per distinct τ
    taulist = sorted({taus[(i, j)][0] for j in range(10)})
    tidx = {t: k for k, t in enumerate(taulist)}
    for t in taulist:
        Ppoly = row.cert(t)
        parts.append(f"""/-- Stage 1: the τ = {t} certificate closed form, evaluated
(coefficients from the verifier's own `split_cert` arithmetic). -/
theorem Peq_{i}_t{tidx[t]} (a eta : ℝ) :
    {lhs11(S, 'a', 'eta', lam, t)}
    = {poly_txt(Ppoly)} := by
  rw [EmajEq.EmajTau11_eq]
  unfold MidChainN.hh
  push_cast
  norm_num
  ring

""")
        names.append(f"Peq_{i}_t{tidx[t]}")
    for j in range(10):
        tau, _mref = taus[(i, j)]
        y0, y1 = Y * F(j, 10), Y * F(j + 1, 10)
        R = affine_rectangle(row.cert(tau), a0, a1, y0, y1)
        assert_match(R, 11, 10,
                     os.path.join("boxes11v2", f"Sendov911Box11_{i}_{j}.lean"),
                     f"box11_{i}_{j}")
        ns = f"Sendov911Box11_{i}_{j}"
        A = f"({rat(a0)} + (1/100) * U)"
        E = f"({rat(y0)} + {rat(step)} * V)"
        parts.append(f"/-! ### Strip {j}: `η ∈ [{y0}, {y1}]`, τ = {tau} -/\n\n")
        parts.append(box_def(f"box_{i}_{j}", ns, 11) + "\n")
        parts.append(f"""theorem eq_{i}_{j} (U V : ℝ) :
    {lhs11(S, A, E, lam, tau)}
    = {rhs_sum(ns, 11)} := by
  rw [Peq_{i}_t{tidx[tau]}]
{EQ_PROOF11_S2.format(ns=ns)}

""")
        names.append(f"eq_{i}_{j}")
        branchparts.append(RED11_BRANCH.format(
            i=i, j=j, tau=tau, a0r=rat(a0), a1r=rat(a1), Sr=rat(S),
            lamr=rat(lam), taur=rat(tau), y0r=rat(y0), stepr=rat(step)))

    boxlist = ", ".join(f"box_{i}_{j}" for j in range(10))
    parts.append(f"""noncomputable def row_{i} : List Box :=
  [{boxlist}]

""")
    for j in range(10):
        memterm = "List.Mem.head _"
        for _ in range(j):
            memterm = f"List.Mem.tail _ ({memterm})"
        parts.append(f"theorem mem_{i}_{j} : box_{i}_{j} ∈ row_{i} :=\n"
                     f"  {memterm}\n\n")
    parts.append(f"theorem rowPos_{i} : CoveringPositive row_{i} := by\n"
                 f"  unfold row_{i}\n")
    tail = "  refine "
    for j in range(10):
        tail += (f"coveringPositive_cons (fun _ _ h1 h2 h3 h4 => "
                 f"Sendov911Box11_{i}_{j}.box_positive h1 h2 h3 h4)\n    (")
    tail += "coveringPositive_nil" + ")" * 10 + "\n\n"
    parts.append(tail)
    parts.append(RED11_HEAD.format(
        i=i, a0r=rat(a0), a1r=rat(a1), Sr=rat(S), lamr=rat(lam), Yr=rat(Y),
        stepr=rat(step)))
    parts.extend(branchparts)
    names += [f"rowPos_{i}", f"red_{i}"]
    parts.append(f"\nend SendovN.Red11_{i}\n\n")
    for nm in names:
        parts.append(f"#print axioms SendovN.Red11_{i}.{nm}\n")
    write_file(f"SendovNRed11_{i}.lean", "".join(parts))


# ---------------- boundary reduction files ----------------
def bdryred_src(n, Sb, lamb, Yb, eqmod, eqns, eqname, boxns, nx, Lbdry, lambdry,
                cast, vfac, extra_hyps, split_call):
    N = n - 1
    Ybr = rat(Yb)
    Sbr = rat(Sb)
    return f"""import Mathlib
import {eqmod}
import SendovNRows{n}
import Sendov911Capstone

set_option maxHeartbeats 4000000

/-!
# D{n}-8: the boundary reduction (generated by emit_assembly1011.py)

`9/10 ≤ a < 1` is driven into the boundary box: σ ≤ S_b (`sigma_boundary`),
the localization key gives `{N}a(1−u) ≤ (1−a)(S_b(1+a)−{N})`, hence
`η² ≤ Y_b²(1−a)`; substituting `x = √(1−a)`, `Y = η/x` and pulling back
`U = (25/8)x`, `V = {vfac}·Y`, the boundary hEq turns the nonpositive
certificate value into `x²·(box polynomial) ≤ 0`, and `x² > 0` finishes.
-/

namespace SendovN.Red{n}Bdry

open Finset Sendov911Capstone

{box_def(f'boxB{n}', boxns, nx)}
theorem posB{n} : ∀ U V : ℝ, 0 ≤ U → U ≤ 1 → 0 ≤ V → V ≤ 1 →
    0 < Box.poly boxB{n} U V :=
  fun _ _ h1 h2 h3 h4 => {boxns}.box_positive h1 h2 h3 h4

theorem red_bdry (mu : ℂ) (Df : Fin {N} → ℂ) (rr : Fin {N} → ℝ) (a eta sig : ℝ)
    (h0 : (9/10 : ℝ) ≤ a) (h1 : a < 1)
    (heta0 : 0 ≤ eta) (hnormSq : Complex.normSq mu = 1 - eta ^ 2)
    (hetau : eta ^ 2 ≤ 1 - mu.re ^ 2) (hmu1 : ‖mu‖ < 1)
    (hloc : ({N}:ℝ) ≤ {N} * a * mu.re + (1 - a ^ 2) * sig)
    (hsigeq : sig = ∑ k, 1 / rr k ^ 2)
    (hrlo : ∀ k, {rat(D10.M0) if n == 10 else rat(D11.M0)} ≤ rr k)
    (hrhi : ∀ k, rr k ≤ a + 1)
    (hprod : ({n}:ℝ) ≤ ∏ k, rr k)
    (hz : ∑ j, Df j = 0){extra_hyps}
    (hD2 : ∑ j, ‖Df j‖ ^ 2 ≤ {N} * eta ^ 2)
    (hI : ‖∫ t in (0:ℝ)..a, ∏ j, ((1:ℂ) - (t:ℂ) * (mu + Df j))‖ < a / {n}) :
    ∃ U V : ℝ, 0 ≤ U ∧ U ≤ 1 ∧ 0 ≤ V ∧ V ≤ 1 ∧
      Sendov911Capstone.Box.poly boxB{n} U V ≤ 0 := by
  have ha0 : (0:ℝ) < a := by linarith
  have ha1 : a ≤ 1 := h1.le
  have hsig : sig ≤ {Sbr} := by
    rw [hsigeq]
    exact Rows{n}.sigma_boundary rr hrlo (fun k => le_trans (hrhi k) (by linarith)) hprod
  have hL := Rows{n}.L_boundary h0 ha1
  have hloc' : (({N}:ℕ):ℝ) ≤ (({N}:ℕ):ℝ) * a * mu.re + (1 - a ^ 2) * sig := by
    push_cast
    exact hloc
  have hkey := MidChainN.key_of_loc ha1 ha0.le hloc' hsig
  have hL' : 0 ≤ {Sbr} * a ^ 2 - (({N}:ℕ):ℝ) * {rat(lambdry)} * a + (({N}:ℕ):ℝ) - {Sbr} := by
    push_cast
    exact hL
  have hlamu := MidChainN.lam_le_u (by norm_num) ha0 hkey hL'
  have hmunorm := MidChainN.lam_le_norm mu hlamu
  have hmu0 : mu ≠ 0 := by
    intro hcon
    rw [hcon] at hmunorm
    simp only [norm_zero] at hmunorm
    norm_num at hmunorm
{split_call}
  -- η² ≤ Y_b²(1−a)
  have hkeyP : ({N}:ℝ) - {Sbr} + {Sbr} * a ^ 2 ≤ {N} * a * mu.re := by
    push_cast at hkey
    linarith [hkey]
  have hu1 : mu.re < 1 := lt_of_le_of_lt (Complex.re_le_norm mu) hmu1
  have h9a : {N} * a * (1 - mu.re) ≤ (1 - a) * ({Sbr} * (1 + a) - {N}) := by
    nlinarith [hkeyP]
  have hA : {N} * a * eta ^ 2 ≤ 2 * ((1 - a) * ({Sbr} * (1 + a) - {N})) := by
    nlinarith [h9a,
      mul_le_mul_of_nonneg_left hetau (by linarith : (0:ℝ) ≤ {N} * a),
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ {N} * a)
        (by linarith : (0:ℝ) ≤ 1 - mu.re)) (by linarith : (0:ℝ) ≤ 1 - mu.re),
      hlamu]
  have hxx : {N} * a * eta ^ 2 ≤ {N} * a * ({Ybr} ^ 2 * (1 - a)) := by
    nlinarith [hA, mul_nonneg (sub_nonneg.mpr h0) (by linarith : (0:ℝ) ≤ 1 - a)]
  have heta2 : eta ^ 2 ≤ {Ybr} ^ 2 * (1 - a) :=
    le_of_mul_le_mul_left (by linarith [hxx]) (by linarith : (0:ℝ) < {N} * a)
  -- the substitution x = √(1−a), Y = η/x
  set x := Real.sqrt (1 - a) with hxdef
  have hx2 : x ^ 2 = 1 - a := Real.sq_sqrt (by linarith)
  have hx0 : (0:ℝ) < x := Real.sqrt_pos.mpr (by linarith)
  have hxle : x ≤ 8/25 := by
    nlinarith [hx2, sq_nonneg (x - 8/25), h0]
  have hYle : eta / x ≤ {Ybr} := by
    rw [div_le_iff₀ hx0]
    nlinarith [heta2, hx2, heta0,
      mul_nonneg (by norm_num : (0:ℝ) ≤ {Ybr}) hx0.le]
  refine ⟨25/8 * x, {vfac} * (eta / x), by linarith, by linarith,
    mul_nonneg (by norm_num) (div_nonneg heta0 hx0.le), ?_, ?_⟩
  · nlinarith [hYle, div_nonneg heta0 hx0.le]
  have heq := {eqns}.{eqname} (25/8 * x) ({vfac} * (eta / x))
  rw [show (8/25 : ℝ) * (25/8 * x) = x by ring] at heq
  rw [show ({rat(Yb)}) * ({vfac} * (eta / x)) = eta / x by ring] at heq
  rw [show (1:ℝ) - x ^ 2 = a by linarith [hx2]] at heq
  rw [show x * (eta / x) = eta by field_simp [hx0.ne']] at heq
  have heqq : Box.poly boxB{n} (25/8 * x) ({vfac} * (eta / x))
      = {rhs_sum(boxns, nx, U='(25/8 * x)', V=f'({vfac} * (eta / x))')} := rfl
  have hs : x ^ 2 * Box.poly boxB{n} (25/8 * x) ({vfac} * (eta / x)) ≤ 0 := by
    rw [heqq]
    exact le_of_eq_of_le heq.symm hP
  have hx2pos : (0:ℝ) < x ^ 2 := pow_pos hx0 2
  nlinarith [hs, hx2pos]

end SendovN.Red{n}Bdry

#print axioms SendovN.Red{n}Bdry.posB{n}
#print axioms SendovN.Red{n}Bdry.red_bdry
"""


def emit_bdryred():
    Sb, lamb, X, Yb = deg10_boundary()
    split10 = f"""  have hP := MidChainN.row_nonpos (N := 9) (alpha := (9/10 : ℝ)) (beta := (1:ℝ))
    (S := {rat(Sb)}) (lam := {rat(lamb)}) (sigma := sig) (by norm_num)
    CTab10.c10 (fun m _ => CTab10.c10_nonneg m) mu Df a eta
    (by norm_num) le_rfl (by norm_num) Rows10.lam_boundary h0 ha1
    heta0 hnormSq hloc' hsig hL' hz
    (CTab10.cTable10 Df eta heta0 hz hD2)
    (by push_cast; norm_num; exact JBoundN.J_closed_form_deg10 hmu0 a)
    (by push_cast; norm_num; exact hI)"""
    src = bdryred_src(10, Sb, lamb, Yb, "SendovNBdryEq10", "BdryEq10",
                      "bdry10_eq", "Sendov911Box10Boundary", 28,
                      "L_boundary", lamb, CAST10, "(20/31 : ℝ)", "", split10)
    write_file("SendovNRed10Bdry.lean", src)

    Sb, lamb, X, Yb = deg11_boundary()
    extra = "\n    (hY1 : ∀ j, ‖mu + Df j‖ ≤ 1)"
    split11 = f"""  have hc := CTab11.cTable11 Df eta heta0 hz hD2
  have hP := Split11.split_row_nonpos (alpha := (9/10 : ℝ)) (beta := (1:ℝ))
    (S := {rat(Sb)}) (lam := {rat(lamb)}) (sigma := sig) (tau := 1) CTab11.c11
    (fun m _ => CTab11.c11_nonneg m) mu Df a eta
    (by norm_num) le_rfl (by norm_num) Rows11.lam_boundary
    (by norm_num) (by norm_num) h0 ha1 heta0 hnormSq hloc hsig hL hz hY1 hc hI"""
    src = bdryred_src(11, Sb, lamb, Yb, "SendovNBdryEq11", "BdryEq11",
                      "bdry11_eq", "Sendov911Box11Boundary", 30,
                      "L_boundary", lamb, "11", "(10/17 : ℝ)", extra, split11)
    write_file("SendovNRed11Bdry.lean", src)


# ---------------- covering files ----------------
def emit_covering10():
    chunks = [f"Red10{L}" for L in "ABCDE"]
    imports = "\n".join(f"import SendovN{c}" for c in chunks)
    parts = [f"""import Mathlib
{imports}
import SendovNRed10Bdry
import SendovNCoverGrid

set_option maxHeartbeats 4000000

/-!
# D10-9: `CoveringPositive boxes10` (generated by emit_assembly1011.py)

The 51-box family (50 interior rows + boundary) assembled from the per-chunk
`CoveringPositive` proofs via `coveringPositive_append`, plus the membership
lemmas the reduction needs.
-/

namespace SendovN.Covering10

open Sendov911Capstone

noncomputable def boxes10 : List Box :=
  Red10A.chunk ++ (Red10B.chunk ++ (Red10C.chunk ++ (Red10D.chunk
    ++ (Red10E.chunk ++ [Red10Bdry.boxB10]))))

theorem covering10 : CoveringPositive boxes10 :=
  Cover.coveringPositive_append Red10A.chunkPos
    (Cover.coveringPositive_append Red10B.chunkPos
      (Cover.coveringPositive_append Red10C.chunkPos
        (Cover.coveringPositive_append Red10D.chunkPos
          (Cover.coveringPositive_append Red10E.chunkPos
            (coveringPositive_cons Red10Bdry.posB10 coveringPositive_nil)))))

"""]
    names = ["covering10"]
    for i in range(40, 90):
        c = (i - 40) // 10
        j = i % 10
        inner = "List.Mem.head _"
        for _ in range(j):
            inner = f"List.Mem.tail _ ({inner})"
        term = f"List.mem_append_left _ ({inner})"
        for _ in range(c):
            term = f"List.mem_append_right _ ({term})"
        parts.append(f"theorem mem_{i} : Red10{'ABCDE'[c]}.box_{i} ∈ boxes10 :=\n"
                     f"  {term}\n\n")
        names.append(f"mem_{i}")
    term = "List.Mem.head _"
    for _ in range(5):
        term = f"List.mem_append_right _ ({term})"
    parts.append(f"theorem mem_bdry : Red10Bdry.boxB10 ∈ boxes10 :=\n  {term}\n\n")
    names.append("mem_bdry")
    parts.append("end SendovN.Covering10\n\n")
    for nm in names:
        parts.append(f"#print axioms SendovN.Covering10.{nm}\n")
    write_file("SendovNCovering10.lean", "".join(parts))


def emit_covering11():
    rows = list(range(37, 90))
    imports = "\n".join(f"import SendovNRed11_{i}" for i in rows)
    listbody = " ++ (".join([f"Red11_{i}.row_{i}" for i in rows] + ["[Red11Bdry.boxB11]"])
    listbody += ")" * len(rows)
    posbody = "\n    (".join(
        [f"Cover.coveringPositive_append Red11_{i}.rowPos_{i}" for i in rows]
        + ["coveringPositive_cons Red11Bdry.posB11 coveringPositive_nil"])
    posbody += ")" * len(rows)
    parts = [f"""import Mathlib
{imports}
import SendovNRed11Bdry
import SendovNCoverGrid

set_option maxHeartbeats 16000000

/-!
# D11-9: `CoveringPositive boxes11` (generated by emit_assembly1011.py)

The 531-box family (53 rows × 10 η-strips + boundary), assembled from the
per-row `CoveringPositive` proofs via `coveringPositive_append`, plus the
per-row membership lifts the reduction needs.
-/

namespace SendovN.Covering11

open Sendov911Capstone

noncomputable def boxes11 : List Box :=
  {listbody}

theorem covering11 : CoveringPositive boxes11 :=
  {posbody}

"""]
    names = ["covering11"]
    for idx, i in enumerate(rows):
        term = "List.mem_append_left _ hb"
        for _ in range(idx):
            term = f"List.mem_append_right _ ({term})"
        parts.append(f"theorem lift_{i} {{b : Box}} (hb : b ∈ Red11_{i}.row_{i}) :"
                     f" b ∈ boxes11 :=\n  {term}\n\n")
        names.append(f"lift_{i}")
    term = "List.Mem.head _"
    for _ in range(len(rows)):
        term = f"List.mem_append_right _ ({term})"
    parts.append(f"theorem mem_bdry : Red11Bdry.boxB11 ∈ boxes11 :=\n  {term}\n\n")
    names.append("mem_bdry")
    parts.append("end SendovN.Covering11\n\n")
    for nm in names:
        parts.append(f"#print axioms SendovN.Covering11.{nm}\n")
    write_file("SendovNCovering11.lean", "".join(parts))


# ---------------- reduction files ----------------
def emit_reduction10():
    branches = []
    for i in range(40, 90):
        c = "ABCDE"[(i - 40) // 10]
        branches.append(f"""    · push_cast at hia hib
      obtain ⟨U, V, hu1, hu2, hv1, hv2, hle⟩ := Red10{c}.red_{i} D.mu D.dev D.r
        D.a D.eta D.sigma (by linarith) (by linarith) heta0 hnormSq hloc9 D.sigma_eq
        hsep D.r_le hprod10 hz hD2 hI
      exact ⟨Red10{c}.box_{i}, Covering10.mem_{i}, U, V, hu1, hu2, hv1, hv2, hle⟩""")
    branchtext = "\n".join(branches)
    src = f"""import Mathlib
import SendovNCovering10
import SendovNSmall10
import SendovNSep10
import SendovNRotData
import Sendov9.GWS

set_option maxHeartbeats 16000000

/-!
# D10-10: `CertificateReduction 10 boxes10` (generated by emit_assembly1011.py)

A counterexample to Sendov in degree 10 yields (rotation) a `DataN 10`;
separation (GWS + tenth-roots algebra) gives `rₖ > 309/500`; the three ranges
`a ≤ 2/5` (small, excluded outright), `2/5 ≤ a ≤ 9/10` (50-interval cover →
per-row reduction) and `9/10 ≤ a ≤ 1` (boundary; `a = 1` excluded directly)
each land in a box of `boxes10` at a nonpositive point.
-/

namespace SendovN.Reduction10

open Finset Polynomial Sendov911Capstone

/-- **Lemma 2.1 at degree 10** — every other zero is farther than `309/500`. -/
theorem separation10 (D : DataN 10) (k : Fin (10 - 1)) :
    (309/500 : ℝ) < ‖(D.a : ℂ) - D.z k‖ := by
  obtain ⟨w, hw, heq⟩ := Sendov9.GWS.graceWalshSzegoPos (10 - 1)
    (SegmentN.uFam D k) ‖(D.a : ℂ) - D.z k‖ (by norm_num)
    (fun j => SegmentN.norm_u_lt D k j)
  rw [SegmentN.integral_uFam_zero D k] at heq
  exact lt_trans (RootUnity10.norm_gt_of_integral_zero10 heq.symm) hw

theorem certificateReduction10 : CertificateReduction 10 Covering10.boxes10 := by
  intro hbad
  unfold Sendov at hbad
  push_neg at hbad
  obtain ⟨p, hm, hdeg, hroots, a0, ha0mem, hno⟩ := hbad
  obtain ⟨D⟩ := RotDataN.exists_data (by norm_num) hm hdeg hroots ha0mem
    (fun z hz => hno z (isRoot_of_mem_roots hz))
  -- shared facts
  have hsep : ∀ k, (309/500 : ℝ) ≤ D.r k := fun k => (separation10 D k).le
  have hprodgt : (10:ℝ) < ∏ k, D.r k := by
    have h := D.prod_r_gt_n
    norm_num at h
    exact h
  have hprod10 : (10:ℝ) ≤ ∏ k, D.r k := hprodgt.le
  have heta0 : 0 ≤ D.eta := D.eta_nonneg
  have hnormSq : Complex.normSq D.mu = 1 - D.eta ^ 2 := by
    have := D.eta_sq
    linarith
  have hloc9 : (9:ℝ) ≤ 9 * D.a * D.mu.re + (1 - D.a ^ 2) * D.sigma := by
    have h := D.localization
    simp only [DataN.u] at h
    norm_num at h
    exact h
  have hz : ∑ j, D.dev j = 0 := D.sum_dev_zero
  have hD2 : ∑ j, ‖D.dev j‖ ^ 2 ≤ 9 * D.eta ^ 2 := by
    have h := D.sum_normSq_dev_le
    norm_num at h
    exact h
  have hu1 : D.mu.re < 1 := lt_of_le_of_lt (Complex.re_le_norm D.mu) D.mu_norm_lt_one
  have hYd : ∀ j, D.mu + D.dev j = ((D.a : ℂ) - D.zeta j)⁻¹ := by
    intro j
    unfold DataN.dev DataN.Y
    ring
  rcases le_or_gt D.a (2/5) with hsm | hmid0
  · -- small range: excluded outright
    exfalso
    rcases le_or_gt D.a (29/100) with hpp | hqq
    · exact Small10.product_excluded D.ha0 hpp (fun k => (D.r_pos k).le)
        (fun k => by have := D.r_le k; linarith) hprodgt
    · have hsig' : D.sigma ≤ 63/10 := by
        rw [D.sigma_eq]
        exact Small10.sigma_small D.r hsep
          (fun k => by have := D.r_le k; linarith) hprod10
      exact Small10.quad_excluded hqq.le hsm hsig' hloc9 hu1
  -- `0 < a` from here on: `|I| < a/10`
  have ha0 : 0 < D.a := by linarith
  have hI0 := D.norm_I_lt ha0
  have hI : ‖∫ t in (0:ℝ)..D.a, ∏ j, ((1:ℂ) - (t:ℂ) * (D.mu + D.dev j))‖
      < D.a / 10 := by
    simp only [hYd]
    push_cast at hI0
    exact hI0
  rcases le_or_gt D.a (9/10) with hmid | htop
  · -- interior: 50-interval cover
    obtain ⟨i, hi, hia, hib⟩ := Cover.cover_grid (by norm_num : (0:ℝ) < 1/100)
      (2/5) 50 (by norm_num) D.a (by linarith) (by push_cast; linarith)
    interval_cases i
{branchtext}
  · -- boundary
    rcases lt_or_eq_of_le D.ha1 with hlt1 | hone
    · have hetau : D.eta ^ 2 ≤ 1 - D.mu.re ^ 2 := by
        have h := D.eta_sq_le_one_sub_u_sq
        simpa [DataN.u] using h
      obtain ⟨U, V, hu1', hu2, hv1, hv2, hle⟩ := Red10Bdry.red_bdry D.mu D.dev D.r
        D.a D.eta D.sigma htop.le hlt1 heta0 hnormSq hetau D.mu_norm_lt_one hloc9
        D.sigma_eq hsep D.r_le hprod10 hz hD2 hI
      exact ⟨Red10Bdry.boxB10, Covering10.mem_bdry, U, V, hu1', hu2, hv1, hv2, hle⟩
    · exact (D.one_excluded hone).elim

end SendovN.Reduction10

#print axioms SendovN.Reduction10.separation10
#print axioms SendovN.Reduction10.certificateReduction10
"""
    write_file("SendovNReduction10.lean", src)


def emit_reduction11():
    branches = []
    for i in range(37, 90):
        branches.append(f"""    · push_cast at hia hib
      obtain ⟨b, hb, U, V, hu1', hu2, hv1, hv2, hle⟩ := Red11_{i}.red_{i} D.mu D.dev
        D.r D.a D.eta D.sigma (by linarith) (by linarith) heta0 hnormSq hloc10
        D.sigma_eq hsep D.r_le hprod11 hz hY1 hD2 hI
      exact ⟨b, Covering11.lift_{i} hb, U, V, hu1', hu2, hv1, hv2, hle⟩""")
    branchtext = "\n".join(branches)
    src = f"""import Mathlib
import SendovNCovering11
import SendovNSmall11
import SendovNSep11
import SendovNRotData
import Sendov9.GWS

set_option maxHeartbeats 16000000

/-!
# D11-10: `CertificateReduction 11 boxes11` (generated by emit_assembly1011.py)

As at degree 10, with the 53-interval cover, the per-row η-strip covers (inside
each `red_i`), and the τ-split row machinery.
-/

namespace SendovN.Reduction11

open Finset Polynomial Sendov911Capstone

/-- **Lemma 2.1 at degree 11** — every other zero is farther than `563/1000`. -/
theorem separation11 (D : DataN 11) (k : Fin (11 - 1)) :
    (563/1000 : ℝ) < ‖(D.a : ℂ) - D.z k‖ := by
  obtain ⟨w, hw, heq⟩ := Sendov9.GWS.graceWalshSzegoPos (11 - 1)
    (SegmentN.uFam D k) ‖(D.a : ℂ) - D.z k‖ (by norm_num)
    (fun j => SegmentN.norm_u_lt D k j)
  rw [SegmentN.integral_uFam_zero D k] at heq
  exact lt_trans (RootUnity11.norm_gt_of_integral_zero11 heq.symm) hw

theorem certificateReduction11 : CertificateReduction 11 Covering11.boxes11 := by
  intro hbad
  unfold Sendov at hbad
  push_neg at hbad
  obtain ⟨p, hm, hdeg, hroots, a0, ha0mem, hno⟩ := hbad
  obtain ⟨D⟩ := RotDataN.exists_data (by norm_num) hm hdeg hroots ha0mem
    (fun z hz => hno z (isRoot_of_mem_roots hz))
  have hsep : ∀ k, (563/1000 : ℝ) ≤ D.r k := fun k => (separation11 D k).le
  have hprodgt : (11:ℝ) < ∏ k, D.r k := by
    have h := D.prod_r_gt_n
    norm_num at h
    exact h
  have hprod11 : (11:ℝ) ≤ ∏ k, D.r k := hprodgt.le
  have heta0 : 0 ≤ D.eta := D.eta_nonneg
  have hnormSq : Complex.normSq D.mu = 1 - D.eta ^ 2 := by
    have := D.eta_sq
    linarith
  have hloc10 : (10:ℝ) ≤ 10 * D.a * D.mu.re + (1 - D.a ^ 2) * D.sigma := by
    have h := D.localization
    simp only [DataN.u] at h
    norm_num at h
    exact h
  have hz : ∑ j, D.dev j = 0 := D.sum_dev_zero
  have hD2 : ∑ j, ‖D.dev j‖ ^ 2 ≤ 10 * D.eta ^ 2 := by
    have h := D.sum_normSq_dev_le
    norm_num at h
    exact h
  have hu1 : D.mu.re < 1 := lt_of_le_of_lt (Complex.re_le_norm D.mu) D.mu_norm_lt_one
  have hYd : ∀ j, D.mu + D.dev j = ((D.a : ℂ) - D.zeta j)⁻¹ := by
    intro j
    unfold DataN.dev DataN.Y
    ring
  have hY1 : ∀ j, ‖D.mu + D.dev j‖ ≤ 1 := by
    intro j
    rw [hYd j]
    exact (D.norm_Y_lt_one j).le
  rcases le_or_gt D.a (37/100) with hsm | hmid0
  · exfalso
    rcases le_or_gt D.a (27/100) with hpp | hqq
    · exact Small11.product_excluded D.ha0 hpp (fun k => (D.r_pos k).le)
        (fun k => by have := D.r_le k; linarith) hprodgt
    · have hsig' : D.sigma ≤ 36/5 := by
        rw [D.sigma_eq]
        exact Small11.sigma_small D.r hsep
          (fun k => by have := D.r_le k; linarith) hprod11
      exact Small11.quad_excluded hqq.le hsm hsig' hloc10 hu1
  have ha0 : 0 < D.a := by linarith
  have hI0 := D.norm_I_lt ha0
  have hI : ‖∫ t in (0:ℝ)..D.a, ∏ j, ((1:ℂ) - (t:ℂ) * (D.mu + D.dev j))‖
      < D.a / 11 := by
    simp only [hYd]
    push_cast at hI0
    exact hI0
  rcases le_or_gt D.a (9/10) with hmid | htop
  · obtain ⟨i, hi, hia, hib⟩ := Cover.cover_grid (by norm_num : (0:ℝ) < 1/100)
      (37/100) 53 (by norm_num) D.a (by linarith) (by push_cast; linarith)
    interval_cases i
{branchtext}
  · rcases lt_or_eq_of_le D.ha1 with hlt1 | hone
    · have hetau : D.eta ^ 2 ≤ 1 - D.mu.re ^ 2 := by
        have h := D.eta_sq_le_one_sub_u_sq
        simpa [DataN.u] using h
      obtain ⟨U, V, hu1', hu2, hv1, hv2, hle⟩ := Red11Bdry.red_bdry D.mu D.dev D.r
        D.a D.eta D.sigma htop.le hlt1 heta0 hnormSq hetau D.mu_norm_lt_one hloc10
        D.sigma_eq hsep D.r_le hprod11 hz hY1 hD2 hI
      exact ⟨Red11Bdry.boxB11, Covering11.mem_bdry, U, V, hu1', hu2, hv1, hv2, hle⟩
    · exact (D.one_excluded hone).elim

end SendovN.Reduction11

#print axioms SendovN.Reduction11.separation11
#print axioms SendovN.Reduction11.certificateReduction11
"""
    write_file("SendovNReduction11.lean", src)


# ---------------- final files ----------------
def emit_finals():
    for n in (10, 11):
        src = f"""import Mathlib
import SendovNReduction{n}

/-!
# Sendov's conjecture, degree {n} — final theorem

`CertificateReduction {n} boxes{n}` (the analytic reduction, proved) +
`CoveringPositive boxes{n}` (the kernel-checked finite half) through
`Sendov911Capstone.sendov_of_reduction`.

Acceptance gate: `#print axioms` must show exactly
`[propext, Classical.choice, Quot.sound]`.
-/

namespace SendovN.Final{n}

/-- **Sendov's conjecture in degree {n}.** -/
theorem sendov{n} : Sendov911Capstone.Sendov {n} :=
  Sendov911Capstone.sendov_of_reduction Reduction{n}.certificateReduction{n}
    Covering{n}.covering{n}

end SendovN.Final{n}

#print axioms SendovN.Final{n}.sendov{n}
"""
        write_file(f"Sendov{n}Final.lean", src)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bdry", action="store_true")
    ap.add_argument("--chunk10", type=str)
    ap.add_argument("--row11", type=int)
    ap.add_argument("--bdryred", action="store_true")
    ap.add_argument("--covering", action="store_true")
    ap.add_argument("--reduction", action="store_true")
    ap.add_argument("--finals", action="store_true")
    ap.add_argument("--all-rows11", action="store_true")
    ap.add_argument("--all-chunks10", action="store_true")
    args = ap.parse_args()
    if args.bdry:
        emit_bdry_eqs()
    if args.chunk10:
        emit_chunk10(args.chunk10)
    if args.all_chunks10:
        for L in "ABCDE":
            emit_chunk10(L)
    if args.row11 is not None:
        emit_row11(args.row11, B11.load_tau())
    if args.all_rows11:
        taus = B11.load_tau()
        for i in range(37, 90):
            emit_row11(i, taus)
    if args.bdryred:
        emit_bdryred()
    if args.covering:
        emit_covering10()
        emit_covering11()
    if args.reduction:
        emit_reduction10()
        emit_reduction11()
    if args.finals:
        emit_finals()


if __name__ == "__main__":
    main()
