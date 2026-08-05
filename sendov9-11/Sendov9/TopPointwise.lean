import Mathlib
import Sendov9.TopAnalytic
import Sendov9.EIntegralsW
import Sendov9.MidPointwise

set_option maxHeartbeats 4000000

namespace Sendov9.TopPt

open Finset

/-!
# `|I - J| ≤ δ·ℰ(x,y)` — the boundary range's analytic half

This is `MidPointwise` again with two changes, and it is *simpler*:

* the majorant is `TopAn.qb` rather than `MidMaj.qt`;
* **no change of variables is needed.**  In the boundary range `a = 1 - δ = 1 - x² = W`,
  so the integral `∫₀ᵃ tᵐ q^{ℓ} dt` is already over `[0, W]` — exactly what
  `EIntegralsW` evaluates.  The middle range needed `t = av` to reach `[0,1]`; here the
  upper limit *is* the certificate's `W`.

The `(cₘ)` and `(ℓₘ)` tables are shared with the middle range (`MidPt.cc`, `MidPt.ell`),
as is the `eₘ` table `MidPt.em_table` — none of that depends on which range we are in.

The paper writes the bound as `|I - J| ≤ δ·ℰ(x,y)` with
`ℰ = ∑ cₘ x^{m-2} yᵐ ∫₀^W tᵐ q^{ℓₘ} dt`.  The `x^{m-2}` is just `δ = x²` factored out of
`ηᵐ = (xy)ᵐ`, so what is proved here is the un-factored form `∑ cₘ ηᵐ ∫₀^W …`; the two
agree by `ring` at the use site, and keeping `η` avoids carrying `x^{m-2}` through the
estimate.

Sendov's conjecture in degree nine remains unproven.
-/

/-- **The pointwise estimate**, boundary version.  For `0 ≤ t ≤ 1 - x²`. -/
theorem pointwise {x y eta u : ℝ} (mu : ℂ) (D : Fin 8 → ℂ)
    (hx0 : 0 ≤ x) (hx : x ≤ 8/25) (hy0 : 0 ≤ y) (hy : y ^ 2 ≤ 19/10)
    (heta : eta = x * y) (heta0 : 0 ≤ eta)
    (hu : mu.re = u) (hnsq : Complex.normSq mu = 1 - x ^ 2 * y ^ 2)
    (hone : 1 - u ≤ (19/20 : ℝ) * x ^ 2)
    (hz : ∑ j, D j = 0) (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2)
    (t : ℝ) (ht0 : 0 ≤ t) (htW : t ≤ 1 - x ^ 2) :
    ‖(∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j))) - ((1 : ℂ) - (t : ℂ) * mu) ^ 8‖
      ≤ ∑ m ∈ Finset.Icc 2 8, MidPt.cc m * eta ^ m * (t ^ m * TopAn.qb x y t ^ MidPt.ell m) := by
  have hfac : ∀ j : Fin 8, (1 : ℂ) - (t : ℂ) * (mu + D j)
      = ((1 : ℂ) - (t : ℂ) * mu) - (t : ℂ) * D j := by
    intro j; ring
  rw [Finset.prod_congr rfl (fun j _ => hfac j),
    prod_sub_eq_head_add_tail ((1 : ℂ) - (t : ℂ) * mu) (t : ℂ) D hz]
  simp only [add_sub_cancel_left]
  refine le_trans (norm_tail_le ((1 : ℂ) - (t : ℂ) * mu) (t : ℂ) D MidPt.cc eta
    (MidPt.em_table D eta heta0 hz hD)) ?_
  have hnt : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_of_nonneg ht0]
  have hq0 : 0 ≤ TopAn.qb x y t := TopAn.qb_nonneg mu ht0 hu hnsq hone
  have hq1 : TopAn.qb x y t ≤ 1 := TopAn.qb_le_one ht0 htW hx0 hx hy0 hy
  have hwsq : ‖(1 : ℂ) - (t : ℂ) * mu‖ ^ 2 ≤ TopAn.qb x y t := by
    have h := TopAn.normSq_le_qb (x := x) (y := y) (t := t) (u := u) mu ht0 hu hnsq hone
    rwa [Complex.normSq_eq_norm_sq] at h
  refine Finset.sum_le_sum fun m hm => ?_
  have hle : 2 * MidPt.ell m ≤ 8 - m := MidPt.ell_ok m hm
  have hpow : ‖(1 : ℂ) - (t : ℂ) * mu‖ ^ (8 - m) ≤ TopAn.qb x y t ^ MidPt.ell m :=
    IJ.pow_le_q_pow (norm_nonneg _) hwsq hq0 hq1 hle
  have hcc : 0 ≤ MidPt.cc m * eta ^ m := by
    have : 0 ≤ MidPt.cc m := by
      unfold MidPt.cc
      split_ifs <;> norm_num
    positivity
  rw [hnt]
  calc t ^ m * ‖(1 : ℂ) - (t : ℂ) * mu‖ ^ (8 - m) * (MidPt.cc m * eta ^ m)
      ≤ t ^ m * TopAn.qb x y t ^ MidPt.ell m * (MidPt.cc m * eta ^ m) := by
        refine mul_le_mul_of_nonneg_right ?_ hcc
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = MidPt.cc m * eta ^ m * (t ^ m * TopAn.qb x y t ^ MidPt.ell m) := by ring

/-- **`|I - J| ≤ ∑ₘ cₘ ηᵐ ∫₀^{1-x²} tᵐ q^{ℓₘ} dt`.**

The upper limit `a = 1 - x²` is already the certificate's `W`, so `EIntegralsW` evaluates
these integrals directly — no substitution step. -/
theorem norm_I_sub_J_le_E {x y eta u : ℝ} (mu : ℂ) (D : Fin 8 → ℂ)
    (hx0 : 0 ≤ x) (hx : x ≤ 8/25) (hy0 : 0 ≤ y) (hy : y ^ 2 ≤ 19/10)
    (heta : eta = x * y) (heta0 : 0 ≤ eta)
    (hu : mu.re = u) (hnsq : Complex.normSq mu = 1 - x ^ 2 * y ^ 2)
    (hone : 1 - u ≤ (19/20 : ℝ) * x ^ 2)
    (hz : ∑ j, D j = 0) (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2)
    (ha0 : 0 ≤ 1 - x ^ 2) :
    ‖(∫ t in (0:ℝ)..(1 - x ^ 2), ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j)))
        - (∫ t in (0:ℝ)..(1 - x ^ 2), ((1 : ℂ) - (t : ℂ) * mu) ^ 8)‖
      ≤ ∑ m ∈ Finset.Icc 2 8, MidPt.cc m * eta ^ m
          * ∫ t in (0:ℝ)..(1 - x ^ 2), t ^ m * TopAn.qb x y t ^ MidPt.ell m := by
  have hqcont : Continuous (TopAn.qb x y) := by
    unfold TopAn.qb
    fun_prop
  have hbcont : Continuous (fun t : ℝ =>
      ∑ m ∈ Finset.Icc 2 8, MidPt.cc m * eta ^ m
        * (t ^ m * TopAn.qb x y t ^ MidPt.ell m)) := by
    apply continuous_finset_sum
    intro m _
    exact ((continuous_pow m).mul (hqcont.pow (MidPt.ell m))).const_mul (MidPt.cc m * eta ^ m)
  have hFcont : Continuous (fun t : ℝ => ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j))) := by
    fun_prop
  have hGcont : Continuous (fun t : ℝ => ((1 : ℂ) - (t : ℂ) * mu) ^ 8) := by
    fun_prop
  have hbound := IJ.norm_I_sub_J_le ha0
    (fun t : ℝ => ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j)))
    (fun t : ℝ => ((1 : ℂ) - (t : ℂ) * mu) ^ 8)
    (fun t : ℝ => ∑ m ∈ Finset.Icc 2 8, MidPt.cc m * eta ^ m
      * (t ^ m * TopAn.qb x y t ^ MidPt.ell m))
    (hFcont.intervalIntegrable _ _) (hGcont.intervalIntegrable _ _)
    (hbcont.intervalIntegrable _ _)
    (fun t ht => pointwise mu D hx0 hx hy0 hy heta heta0 hu hnsq hone hz hD t ht.1 ht.2)
  refine le_trans hbound (le_of_eq ?_)
  exact IJ.integral_majorant (1 - x ^ 2) MidPt.cc eta (TopAn.qb x y) MidPt.ell hqcont

end Sendov9.TopPt

#print axioms Sendov9.TopPt.pointwise
#print axioms Sendov9.TopPt.norm_I_sub_J_le_E
