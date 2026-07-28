import Mathlib
import Sendov9.TopPointwise

set_option maxHeartbeats 4000000

namespace Sendov9.TopEq

open Finset

/-!
# `ℰ(x,y)` in the boundary certificate's own form

`TopPt.norm_I_sub_J_le_E` produces the majorant as `∑ₘ cₘ ηᵐ ∫₀^W tᵐ q^{ℓₘ} dt`;
`Cert.bdry_pos` is stated against `δ·ℰ(x,y)` with `ℰ = ∑ₘ cₘ x^{m-2} yᵐ · bracketₘ` and
the integrals already evaluated.

The two differ by exactly the factored `δ`: with `η = xy` and `δ = x²`,

    ηᵐ = xᵐ yᵐ = x² · x^{m-2} yᵐ = δ · x^{m-2} yᵐ      (valid since m ≥ 2),

so this file's `Emaj_eqW` is the middle range's `EmajEq.Emaj_eq` with a `W`-dependent
bracket and an `x²` pulled out front.

Sendov's conjecture in degree nine remains unproven.
-/

/-- The certificate's `W = 1 - x²` — the upper limit of every boundary integral. -/
noncomputable def W (x : ℝ) : ℝ := 1 - x ^ 2

/-- The certificate's `Q1 = -2 + (19/10)x²`. -/
noncomputable def Q1 (x : ℝ) : ℝ := -2 + (19/10 : ℝ) * x ^ 2

/-- The certificate's `Q2 = 1 - x²y²`. -/
noncomputable def Q2 (x y : ℝ) : ℝ := 1 - x ^ 2 * y ^ 2

/-- `qb` is literally `1 + Q1 t + Q2 t²`. -/
theorem qb_eq (x y t : ℝ) : TopAn.qb x y t = 1 + Q1 x * t + Q2 x y * t ^ 2 := by
  unfold TopAn.qb Q1 Q2
  ring

/-- **`ℰ(x,y)`, evaluated**, with `δ = x²` factored out exactly as `Cert.bdry_pos` has it. -/
theorem Emaj_eqW (x y : ℝ) :
    (∑ m ∈ Finset.Icc 2 8, MidPt.cc m * (x * y) ^ m
        * ∫ t in (0:ℝ)..(1 - x ^ 2), t ^ m * TopAn.qb x y t ^ MidPt.ell m)
      = x ^ 2 * (
        (4 : ℝ) * x ^ 0 * y ^ 2 * ((1/3 : ℝ) * W x ^ 3 + (3/5 : ℝ) * Q2 x y * W x ^ 5
          + (3/7 : ℝ) * Q2 x y ^ 2 * W x ^ 7 + (1/9 : ℝ) * Q2 x y ^ 3 * W x ^ 9
          + (3/4 : ℝ) * Q1 x * W x ^ 4 + (1 : ℝ) * Q1 x * Q2 x y * W x ^ 6
          + (3/8 : ℝ) * Q1 x * Q2 x y ^ 2 * W x ^ 8 + (3/5 : ℝ) * Q1 x ^ 2 * W x ^ 5
          + (3/7 : ℝ) * Q1 x ^ 2 * Q2 x y * W x ^ 7 + (1/6 : ℝ) * Q1 x ^ 3 * W x ^ 6)
        + (264/35 : ℝ) * x ^ 1 * y ^ 3 * ((1/4 : ℝ) * W x ^ 4
          + (1/3 : ℝ) * Q2 x y * W x ^ 6 + (1/8 : ℝ) * Q2 x y ^ 2 * W x ^ 8
          + (2/5 : ℝ) * Q1 x * W x ^ 5 + (2/7 : ℝ) * Q1 x * Q2 x y * W x ^ 7
          + (1/6 : ℝ) * Q1 x ^ 2 * W x ^ 6)
        + (24 : ℝ) * x ^ 2 * y ^ 4 * ((1/5 : ℝ) * W x ^ 5
          + (2/7 : ℝ) * Q2 x y * W x ^ 7 + (1/9 : ℝ) * Q2 x y ^ 2 * W x ^ 9
          + (1/3 : ℝ) * Q1 x * W x ^ 6 + (1/4 : ℝ) * Q1 x * Q2 x y * W x ^ 8
          + (1/7 : ℝ) * Q1 x ^ 2 * W x ^ 7)
        + (56 : ℝ) * x ^ 3 * y ^ 5 * ((1/6 : ℝ) * W x ^ 6
          + (1/8 : ℝ) * Q2 x y * W x ^ 8 + (1/7 : ℝ) * Q1 x * W x ^ 7)
        + (28 : ℝ) * x ^ 4 * y ^ 6 * ((1/7 : ℝ) * W x ^ 7
          + (1/9 : ℝ) * Q2 x y * W x ^ 9 + (1/8 : ℝ) * Q1 x * W x ^ 8)
        + (8 : ℝ) * x ^ 5 * y ^ 7 * ((1/8 : ℝ) * W x ^ 8)
        + (1 : ℝ) * x ^ 6 * y ^ 8 * ((1/9 : ℝ) * W x ^ 9)) := by
  have hIcc : (Finset.Icc 2 8 : Finset ℕ) = {2, 3, 4, 5, 6, 7, 8} := by decide
  rw [hIcc, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  -- the tables, as closed numerals (see `EmajEq` for why not `norm_num` on the whole goal)
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
  simp only [qb_eq]
  have hW : (1 : ℝ) - x ^ 2 = W x := rfl
  rw [hW]
  rw [EIntW.intW_2_3, EIntW.intW_3_2, EIntW.intW_4_2, EIntW.intW_5_1, EIntW.intW_6_1,
    EIntW.intW_7_0, EIntW.intW_8_0]
  ring

end Sendov9.TopEq

#print axioms Sendov9.TopEq.qb_eq
#print axioms Sendov9.TopEq.Emaj_eqW
