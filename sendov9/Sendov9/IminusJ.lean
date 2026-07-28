import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.IJ

open Finset intervalIntegral

/-!
# `|I - J| ≤ E_S` (equation 4.7)

`I = ∫₀ᵃ ∏ⱼ(1 - tYⱼ) dt` and `J = ∫₀ᵃ (1-tμ)⁸ dt`.  Writing `Yⱼ = μ + Dⱼ` and
`w = 1 - tμ`, the centred expansion (banked in `Sigma22.lean`) gives

    ∏ⱼ(1 - tYⱼ) - (1-tμ)⁸ = ∑_{m=2}^{8} (-t)^m w^{8-m} eₘ(D),

so `I - J` is the integral of that tail.  Bounding under the integral sign and using
`|eₘ| ≤ cₘ ηᵐ` and `|w|^{8-m} ≤ q^{ℓₘ}` at feasible points yields `E_S`.

The pieces here are the integral-level steps: pulling the difference inside one
integral, bounding by the integral of the norm, and monotonicity.  The pointwise
work is already done.
-/

/-- `I - J` is the integral of the pointwise difference. -/
theorem sub_eq_integral_sub (a : ℝ) (F G : ℝ → ℂ)
    (hF : IntervalIntegrable F MeasureTheory.volume 0 a)
    (hG : IntervalIntegrable G MeasureTheory.volume 0 a) :
    (∫ t in (0:ℝ)..a, F t) - (∫ t in (0:ℝ)..a, G t)
      = ∫ t in (0:ℝ)..a, (F t - G t) := (integral_sub hF hG).symm

/-- Bounding a ℂ-valued integral by the integral of a real majorant of its norm. -/
theorem norm_integral_le_of_norm_le {a : ℝ} (ha : 0 ≤ a) (H : ℝ → ℂ) (b : ℝ → ℝ)
    (hH : IntervalIntegrable H MeasureTheory.volume 0 a)
    (hb : IntervalIntegrable b MeasureTheory.volume 0 a)
    (hle : ∀ t ∈ Set.Icc (0:ℝ) a, ‖H t‖ ≤ b t) :
    ‖∫ t in (0:ℝ)..a, H t‖ ≤ ∫ t in (0:ℝ)..a, b t := by
  have h1 : ‖∫ t in (0:ℝ)..a, H t‖ ≤ ∫ t in (0:ℝ)..a, ‖H t‖ :=
    norm_integral_le_integral_norm ha
  have h2 : (∫ t in (0:ℝ)..a, ‖H t‖) ≤ ∫ t in (0:ℝ)..a, b t := by
    apply integral_mono_on ha hH.norm hb
    intro t ht
    exact hle t ht
  linarith

/-- The majorant `∑_{m=2}^{8} cₘ ηᵐ tᵐ q(t)^{ℓₘ}` integrates termwise. -/
theorem integral_majorant (a : ℝ) (c : ℕ → ℝ) (eta : ℝ) (q : ℝ → ℝ) (l : ℕ → ℕ)
    (hq : Continuous q) :
    (∫ t in (0:ℝ)..a, ∑ m ∈ Finset.Icc 2 8, c m * eta ^ m * (t ^ m * q t ^ (l m)))
      = ∑ m ∈ Finset.Icc 2 8, c m * eta ^ m * ∫ t in (0:ℝ)..a, (t ^ m * q t ^ (l m)) := by
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun m _ => by
      rw [← integral_const_mul]
  · intro m _
    apply Continuous.intervalIntegrable
    fun_prop

/-- **Equation (4.7), the integral half.**  Given the pointwise tail bound, the
difference of the integrals is bounded by the integrated majorant. -/
theorem norm_I_sub_J_le {a : ℝ} (ha : 0 ≤ a) (F G : ℝ → ℂ) (b : ℝ → ℝ)
    (hF : IntervalIntegrable F MeasureTheory.volume 0 a)
    (hG : IntervalIntegrable G MeasureTheory.volume 0 a)
    (hb : IntervalIntegrable b MeasureTheory.volume 0 a)
    (hle : ∀ t ∈ Set.Icc (0:ℝ) a, ‖F t - G t‖ ≤ b t) :
    ‖(∫ t in (0:ℝ)..a, F t) - (∫ t in (0:ℝ)..a, G t)‖ ≤ ∫ t in (0:ℝ)..a, b t := by
  rw [sub_eq_integral_sub a F G hF hG]
  exact norm_integral_le_of_norm_le ha (fun t => F t - G t) b (hF.sub hG) hb hle

/-- The pointwise majorant step: `‖w‖^e ≤ q^l` whenever `‖w‖² ≤ q ≤ 1` and `2l ≤ e`.

This is the paper's rounding-DOWN of half-integral powers (`q^{5/2} ≤ q²`,
`q^{3/2} ≤ q`, `q^{1/2} ≤ 1`), so the hypothesis is `2l ≤ e`, not `e ≤ 2l`:
with `e = 8-m` and `l = ℓₘ` the pairs are (6,3), (5,2), (4,2), (3,1), (2,1), (1,0), (0,0).

Note `‖w‖ ≤ 1` is forced by `‖w‖² ≤ q ≤ 1`, which is what lets the surplus
`e - 2l` factors be discarded. -/
theorem pow_le_q_pow {w q : ℝ} {e l : ℕ} (hw : 0 ≤ w) (hwq : w ^ 2 ≤ q)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hle : 2 * l ≤ e) :
    w ^ e ≤ q ^ l := by
  have hw1 : w ≤ 1 := by nlinarith
  calc w ^ e ≤ w ^ (2 * l) := pow_le_pow_of_le_one hw hw1 hle
    _ = (w ^ 2) ^ l := pow_mul w 2 l
    _ ≤ q ^ l := pow_le_pow_left₀ (by positivity) hwq l

/-- The `(e, l)` pairs the paper actually uses, `e = 8 - m` and `l = ℓₘ`. -/
theorem ell_pairs_ok : ∀ m ∈ Finset.Icc 2 8,
    2 * (if m = 2 then 3 else if m = 3 then 2 else if m = 4 then 2
         else if m = 5 then 1 else if m = 6 then 1 else 0) ≤ 8 - m := by
  decide

end Sendov9.IJ

#print axioms Sendov9.IJ.sub_eq_integral_sub
#print axioms Sendov9.IJ.norm_integral_le_of_norm_le
#print axioms Sendov9.IJ.integral_majorant
#print axioms Sendov9.IJ.norm_I_sub_J_le
#print axioms Sendov9.IJ.pow_le_q_pow
#print axioms Sendov9.IJ.ell_pairs_ok
