import Mathlib
import Sendov9.MidRow

set_option maxHeartbeats 4000000

namespace Sendov9.EmajEq

open Finset

/-!
# `E_S(a,η)` in the certificates' own form

`MidRow.row_excluded` consumes the majorant as `MidRow.Emaj`, a sum over `Icc 2 8` of
integrals.  The Bernstein certificates in `CertData.lean` are stated against the same
quantity with those integrals already evaluated, in terms of

    Q1 = -(8 - S + Sa²)/4,     Q2 = a²(1 - η²).

This file is that identity, once.  It is all that stands between the eighteen rows and
being pure boilerplate: with `Emaj_eq` in hand, each row's `hPdef` is a `rw` followed by
`ring`.

Two steps: expand `Icc 2 8` termwise (`Finset.sum_Icc_succ_top`, six peels), and rewrite
each `∫₀¹ vᵐ q^ℓ` with `EIntegrals` after `MidMaj.q_eq` puts `q_S` into the
`1 + Q1v + Q2v²` shape those lemmas speak about.

The `(cₘ)` and `(ℓₘ)` tables are `MidPt.cc` and `MidPt.ell`; the bracket expressions on
the right were transcribed verbatim from `Sendov9Complete` by the generator, which is
exactly why this closes by `ring` rather than by hand-matching coefficients.

Sendov's conjecture in degree nine remains unproven.
-/

open MidMaj (Q1 Q2)

/-- **`E_S(a,η)`, evaluated.**  The right-hand side is the certificates' `E` term. -/
theorem Emaj_eq (S a eta : ℝ) :
    MidRow.Emaj S a eta
      = (4 : ℝ) * a ^ 3 * eta ^ 2 * ((1/3 : ℝ) + (3/5 : ℝ) * Q2 a eta
          + (3/7 : ℝ) * Q2 a eta ^ 2 + (1/9 : ℝ) * Q2 a eta ^ 3 + (3/4 : ℝ) * Q1 S a
          + (1 : ℝ) * Q1 S a * Q2 a eta + (3/8 : ℝ) * Q1 S a * Q2 a eta ^ 2
          + (3/5 : ℝ) * Q1 S a ^ 2 + (3/7 : ℝ) * Q1 S a ^ 2 * Q2 a eta
          + (1/6 : ℝ) * Q1 S a ^ 3)
        + (264/35 : ℝ) * a ^ 4 * eta ^ 3 * ((1/4 : ℝ) + (1/3 : ℝ) * Q2 a eta
          + (1/8 : ℝ) * Q2 a eta ^ 2 + (2/5 : ℝ) * Q1 S a
          + (2/7 : ℝ) * Q1 S a * Q2 a eta + (1/6 : ℝ) * Q1 S a ^ 2)
        + (24 : ℝ) * a ^ 5 * eta ^ 4 * ((1/5 : ℝ) + (2/7 : ℝ) * Q2 a eta
          + (1/9 : ℝ) * Q2 a eta ^ 2 + (1/3 : ℝ) * Q1 S a
          + (1/4 : ℝ) * Q1 S a * Q2 a eta + (1/7 : ℝ) * Q1 S a ^ 2)
        + (56 : ℝ) * a ^ 6 * eta ^ 5 * ((1/6 : ℝ) + (1/8 : ℝ) * Q2 a eta
          + (1/7 : ℝ) * Q1 S a)
        + (28 : ℝ) * a ^ 7 * eta ^ 6 * ((1/7 : ℝ) + (1/9 : ℝ) * Q2 a eta
          + (1/8 : ℝ) * Q1 S a)
        + (8 : ℝ) * a ^ 8 * eta ^ 7 * ((1/8 : ℝ))
        + (1 : ℝ) * a ^ 9 * eta ^ 8 * ((1/9 : ℝ)) := by
  rw [MidRow.Emaj]
  -- expand `Icc 2 8` as an explicit finset.  Peeling with `sum_Icc_succ_top` instead
  -- needs `rw [show (8:ℕ) = 7+1 ..]`, which rewrites numerals elsewhere in the goal and
  -- dies with "motive is not type correct".
  have hIcc : (Finset.Icc 2 8 : Finset ℕ) = {2, 3, 4, 5, 6, 7, 8} := by decide
  rw [hIcc, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  -- the tables, and `q_S` in the `1 + Q1 v + Q2 v²` shape `EIntegrals` speaks about
  -- Reduce `cc`/`ell` by rewriting their VALUES, one closed numeral at a time.
  -- `norm_num` on the whole goal also turns `x ^ 1` into `x` and `x ^ 0` into `1`, after
  -- which `EInt.int_5_1`/`int_7_0`/`int_8_0` stop matching; and `simp only` on the whole
  -- goal reassociates the integrand's `1 + Q1 v + Q2 v²`, which breaks the rest.
  have c2 : MidPt.cc 2 = 4 := by norm_num [MidPt.cc]
  have c3 : MidPt.cc 3 = 264 / 35 := by norm_num [MidPt.cc]
  have c4 : MidPt.cc 4 = 24 := by norm_num [MidPt.cc]
  have c5 : MidPt.cc 5 = 56 := by norm_num [MidPt.cc]
  have c6 : MidPt.cc 6 = 28 := by norm_num [MidPt.cc]
  have c7 : MidPt.cc 7 = 8 := by norm_num [MidPt.cc]
  have c8 : MidPt.cc 8 = 1 := by norm_num [MidPt.cc]
  have l2 : MidPt.ell 2 = 3 := by norm_num [MidPt.ell]
  have l3 : MidPt.ell 3 = 2 := by norm_num [MidPt.ell]
  have l4 : MidPt.ell 4 = 2 := by norm_num [MidPt.ell]
  have l5 : MidPt.ell 5 = 1 := by norm_num [MidPt.ell]
  have l6 : MidPt.ell 6 = 1 := by norm_num [MidPt.ell]
  have l7 : MidPt.ell 7 = 0 := by norm_num [MidPt.ell]
  have l8 : MidPt.ell 8 = 0 := by norm_num [MidPt.ell]
  rw [c2, c3, c4, c5, c6, c7, c8, l2, l3, l4, l5, l6, l7, l8]
  simp only [MidMaj.q_eq]
  rw [EInt.int_2_3, EInt.int_3_2, EInt.int_4_2, EInt.int_5_1, EInt.int_6_1,
    EInt.int_7_0, EInt.int_8_0]
  ring

end Sendov9.EmajEq

#print axioms Sendov9.EmajEq.Emaj_eq
