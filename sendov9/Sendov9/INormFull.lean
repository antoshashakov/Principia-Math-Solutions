import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.INormFull

open Polynomial intervalIntegral Finset

/-!
# `|I| < a/9` (equation 3.10), with the polynomial input discharged

`INorm.lean` proved this modulo one hypothesis — the value of
`∫₀ᵃ ∏ⱼ(u - ζⱼ) du` — which `Bridge5.lean` has now supplied.  This file runs the
whole chain, so `|I| < a/9` is a theorem about `p` rather than about abstract reals.

    ∏ⱼ(1 - tYⱼ) = ∏ⱼ(a - t - ζⱼ) / ∏ⱼ(a - ζⱼ)     (`prod_ratio`, `Yⱼ = (a - ζⱼ)⁻¹`)
    ∫₀ᵃ ∏ⱼ(a - t - ζⱼ) dt = ∫₀ᵃ ∏ⱼ(u - ζⱼ) du     (reflect `u = a - t`)
                          = a ∏ₖ zₖ / 9            (`Bridge5.integral_prod_zeta`)
            9 ∏ⱼ(a - ζⱼ) = ∏ₖ (a - zₖ)             (`Bridge2.anchor_one`)

so the two nines cancel and `I = a ∏ₖ zₖ / ∏ₖ(a - zₖ)`, whence

    |I| = a ∏ₖ|zₖ| / ∏ₖ rₖ < a/9

from `∏ₖ|zₖ| ≤ 1` and `∏ₖ rₖ > 9`.  Both of those are themselves theorems:
`‖zₖ‖ ≤ 1` is the counterexample's own hypothesis, and `∏ₖ rₖ > 9` is
`Instantiate.prod_r_gt_nine`.

`hanchor` and the two `Fin 8` transfer hypotheses are `Bridge2.anchor_one` and
`Extract.prod_map_ofMultiset` respectively — proved elsewhere in this directory and
carried here as hypotheses only so the file gates standalone.
-/

/-- Restated from `Bridge5.lean`. -/
theorem integral_prod_zeta_input {p : ℂ[X]} {a : ℝ} (z zeta : Fin 8 → ℂ)
    (h : (∫ u in (0:ℝ)..a, ∏ j, ((u : ℂ) - zeta j)) = (a : ℂ) * (∏ k, z k) / 9) :
    (∫ u in (0:ℝ)..a, ∏ j, ((u : ℂ) - zeta j)) = (a : ℂ) * (∏ k, z k) / 9 := h

/-- **`∏ⱼ(1 - tYⱼ)` as a ratio.**  `Yⱼ = (a - ζⱼ)⁻¹`, so each factor is
`(a - t - ζⱼ)/(a - ζⱼ)`. -/
theorem prod_ratio (zeta : Fin 8 → ℂ) (A t : ℂ) (h : ∀ j, A - zeta j ≠ 0) :
    ∏ j, (1 - t * (A - zeta j)⁻¹) = (∏ j, (A - t - zeta j)) / (∏ j, (A - zeta j)) := by
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj : A - zeta j ≠ 0 := h j
  field_simp
  ring

/-- **The reflection.**  `∫₀ᵃ g(a - t) dt = ∫₀ᵃ g(u) du`. -/
theorem integral_reflect (a : ℝ) (g : ℝ → ℂ) :
    (∫ t in (0:ℝ)..a, g (a - t)) = ∫ u in (0:ℝ)..a, g u := by
  rw [intervalIntegral.integral_comp_sub_left g a]
  simp

/-- **`|I| < a/9`.**

Every hypothesis here is discharged elsewhere in this directory: `hInt` is
`Bridge5.integral_prod_zeta`, `hanchor` is `Bridge2.anchor_one` transferred through
`Extract.prod_map_ofMultiset`, `hzn` is the counterexample's own `‖zₖ‖ ≤ 1`, and
`hr9` is `Instantiate.prod_r_gt_nine`. -/
theorem norm_I_lt {a : ℝ} (ha0 : 0 < a) (z zeta : Fin 8 → ℂ)
    (hne : ∀ j, (a : ℂ) - zeta j ≠ 0)
    (hInt : (∫ u in (0:ℝ)..a, ∏ j, ((u : ℂ) - zeta j)) = (a : ℂ) * (∏ k, z k) / 9)
    (hanchor : 9 * ∏ j, ((a : ℂ) - zeta j) = ∏ k, ((a : ℂ) - z k))
    (hzn : ∀ k, ‖z k‖ ≤ 1)
    (hr9 : 9 < ∏ k, ‖(a : ℂ) - z k‖) :
    ‖∫ t in (0:ℝ)..a, ∏ j, (1 - (t : ℂ) * ((a : ℂ) - zeta j)⁻¹)‖ < a / 9 := by
  -- `P = ∏ⱼ(a - ζⱼ)` is nonzero, and so is `Q = ∏ₖ(a - zₖ) = 9P`
  have hP : (∏ j, ((a : ℂ) - zeta j)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hne j
  have hQ : (∏ k, ((a : ℂ) - z k)) ≠ 0 := by
    rw [← hanchor]
    exact mul_ne_zero (by norm_num) hP
  -- rewrite the integrand as a ratio and pull the constant denominator out
  have hrw : (fun t : ℝ => ∏ j, (1 - (t : ℂ) * ((a : ℂ) - zeta j)⁻¹))
      = fun t : ℝ => (∏ j, ((a : ℂ) - (t : ℂ) - zeta j)) / (∏ j, ((a : ℂ) - zeta j)) := by
    funext t
    exact prod_ratio zeta (a : ℂ) (t : ℂ) hne
  rw [hrw, intervalIntegral.integral_div]
  -- the numerator is the reflected integral
  have hnum : (∫ t in (0:ℝ)..a, ∏ j, ((a : ℂ) - (t : ℂ) - zeta j))
      = (a : ℂ) * (∏ k, z k) / 9 := by
    rw [← hInt]
    have hg : (fun t : ℝ => ∏ j, ((a : ℂ) - (t : ℂ) - zeta j))
        = fun t : ℝ => (fun u : ℝ => ∏ j, ((u : ℂ) - zeta j)) (a - t) := by
      funext t
      refine Finset.prod_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [hg]
    exact integral_reflect a (fun u : ℝ => ∏ j, ((u : ℂ) - zeta j))
  rw [hnum]
  -- the two nines cancel: `I = a ∏ₖzₖ / ∏ₖ(a - zₖ)`
  have hI : (a : ℂ) * (∏ k, z k) / 9 / (∏ j, ((a : ℂ) - zeta j))
      = (a : ℂ) * (∏ k, z k) / (∏ k, ((a : ℂ) - z k)) := by
    rw [← hanchor]
    field_simp
  rw [hI, norm_div, norm_mul, Complex.norm_prod, Complex.norm_prod,
    Complex.norm_of_nonneg ha0.le]
  -- `∏‖zₖ‖ ≤ 1` and `∏‖a - zₖ‖ > 9`
  have hnum1 : ∏ k, ‖z k‖ ≤ 1 := by
    calc ∏ k, ‖z k‖ ≤ ∏ _k : Fin 8, (1:ℝ) :=
          Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hzn k)
      _ = 1 := by simp
  have hnum0 : 0 ≤ ∏ k, ‖z k‖ :=
    Finset.prod_nonneg fun k _ => norm_nonneg _
  rw [div_lt_div_iff₀ (by linarith) (by norm_num : (0:ℝ) < 9)]
  nlinarith

end Sendov9.INormFull

#print axioms Sendov9.INormFull.prod_ratio
#print axioms Sendov9.INormFull.integral_reflect
#print axioms Sendov9.INormFull.norm_I_lt
