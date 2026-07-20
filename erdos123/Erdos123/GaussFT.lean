/-
ERDŐS #123 — THE GAUSSIAN FOURIER TRANSFORM
===========================================
This file contains the Gaussian Fourier transform and its rescaled / tail corollaries,
and NOTHING else.  Specifically:

  `gaussian_ft_complex`       ∫ e^{-2π²u²} e(-yu) du = (1/√(2π)) e^{-y²/2}
  `gaussian_ft_real`          the real part of the above
  `gaussian_ft_scaled`        ∫ e^{-Au²} cos(yu) du = √(π/A) e^{-y²/(4A)}   (A > 0)
  `gaussian_integrable_scaled` integrability of that integrand
  `gauss_tail_Ioi`            ∫_{u>T} e^{-Au²} du ≤ e^{-AT²}/(AT)
  `gauss_osc_tail_Ioi`        the same bound for the oscillating integrand

No local CLT, no Taylor bound, no three-range split lives here; see `Erdos123.GLCLT`
for the (as yet unproved) assembly.
-/
import Erdos123.Band

set_option maxHeartbeats 4000000

open scoped Real
open MeasureTheory

namespace Erdos123Band

noncomputable section

/-! ## The Gaussian Fourier transform (Lemma gaussian-ft).

`∫_ℝ e^{-2π²u²} e^{-2πiyu} du = (1/√(2π)) e^{-y²/2}`.  We derive it from Mathlib's
`integral_cexp_quadratic` with `b = -2π²`, `c = -2πiy`, `d = 0`. -/

/-- `(1/(2π) : ℂ)^(1/2) = 1/√(2π)`: the complex square root of the positive real `1/(2π)`. -/
lemma cpow_half_inv_two_pi :
    ((Real.pi : ℂ) / (2 * (Real.pi : ℂ) ^ 2)) ^ (1 / 2 : ℂ)
      = (1 / Real.sqrt (2 * Real.pi) : ℝ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hval : (Real.pi : ℂ) / (2 * (Real.pi : ℂ) ^ 2) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [hval]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow (by positivity)]
  congr 1
  rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, ← one_div]

/-- **Gaussian Fourier transform (complex form), Lemma gaussian-ft.**
    `∫ e^{-2π²u²}·e(-y u) du = (1/√(2π))·e^{-y²/2}`, from Mathlib `fourierIntegral_gaussian`
    with `b = 2π²`, `t = -2πy`. -/
lemma gaussian_ft_complex (y : ℝ) :
    (∫ u : ℝ, Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) * e (-(y * u)))
      = (1 / Real.sqrt (2 * Real.pi) : ℝ) * Complex.exp (-((y : ℂ) ^ 2 / 2)) := by
  have hbre : (0 : ℝ) < (2 * (Real.pi : ℂ) ^ 2).re := by
    have : (2 * (Real.pi : ℂ) ^ 2) = ((2 * Real.pi ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]; positivity
  have hint : ∀ u : ℝ,
      Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) * e (-(y * u))
        = Complex.exp (Complex.I * ((-(2 * Real.pi * y) : ℝ) : ℂ) * u)
          * Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) := by
    intro u
    rw [mul_comm]
    congr 2
    rw [e]
    congr 1
    push_cast
    ring
  simp_rw [hint]
  rw [fourierIntegral_gaussian hbre ((-(2 * Real.pi * y) : ℝ) : ℂ)]
  rw [cpow_half_inv_two_pi]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  congr 2
  push_cast
  field_simp
  ring

/-- The Gaussian × character integrand is integrable (`integrable_cexp_quadratic`). -/
lemma gauss_integrable (y : ℝ) :
    Integrable (fun u : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) * e (-(y * u))) := by
  have hbre : (0 : ℝ) < (2 * (Real.pi : ℂ) ^ 2).re := by
    have : (2 * (Real.pi : ℂ) ^ 2) = ((2 * Real.pi ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]; positivity
  have hfun : (fun u : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) * e (-(y * u)))
      = (fun u : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * (u : ℂ) ^ 2
          + (-(2 * Real.pi * Complex.I * y)) * u + 0)) := by
    funext u
    rw [e, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfun]
  exact integrable_cexp_quadratic hbre _ 0

/-- **Gaussian Fourier transform (real form).**
    `∫ cos(2π y u)·e^{-2π²u²} du = (1/√(2π))·e^{-y²/2}` — the real part of `gaussian_ft_complex`. -/
lemma gaussian_ft_real (y : ℝ) :
    (∫ u : ℝ, Real.cos (2 * Real.pi * y * u) * Real.exp (-(2 * Real.pi ^ 2 * u ^ 2)))
      = (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(y ^ 2 / 2)) := by
  have hcpx := gaussian_ft_complex y
  have hintg := gauss_integrable y
  have hpt : ∀ u : ℝ,
      (Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) * e (-(y * u))).re
        = Real.cos (2 * Real.pi * y * u) * Real.exp (-(2 * Real.pi ^ 2 * u ^ 2)) := by
    intro u
    have hAreal : Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * (u : ℂ) ^ 2)
        = ((Real.exp (-(2 * Real.pi ^ 2 * u ^ 2)) : ℝ) : ℂ) := by
      rw [show -(2 * (Real.pi : ℂ) ^ 2) * (u : ℂ) ^ 2
            = ((-(2 * Real.pi ^ 2 * u ^ 2) : ℝ) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_exp]
    have here : (e (-(y * u))).re = Real.cos (2 * Real.pi * y * u) := by
      have hb : e (-(y * u)) = Complex.exp ((↑(2 * Real.pi * (-(y * u))) : ℂ) * Complex.I) := by
        rw [e]; congr 1; push_cast; ring
      rw [hb, Complex.exp_ofReal_mul_I_re]
      rw [show 2 * Real.pi * (-(y * u)) = -(2 * Real.pi * y * u) by ring, Real.cos_neg]
    rw [hAreal, Complex.re_ofReal_mul, here, mul_comm]
  have hlhs : (∫ u : ℝ, Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) * e (-(y * u))).re
      = ∫ u : ℝ, Real.cos (2 * Real.pi * y * u) * Real.exp (-(2 * Real.pi ^ 2 * u ^ 2)) := by
    have hre := _root_.integral_re (𝕜 := ℂ) hintg
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [← hlhs, hcpx, Complex.re_ofReal_mul,
    show -((y : ℂ) ^ 2 / 2) = ((-(y ^ 2 / 2) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
    Complex.ofReal_re]

/-! ## Rescaled and tail versions.

These are the forms actually consumed by the local-CLT principal-range estimate:
a general Gaussian width `A > 0` and a plain (non-normalised) frequency `y`. -/

/-- The rescaled Gaussian × cosine integrand is integrable. -/
theorem gaussian_integrable_scaled {A : ℝ} (hA : 0 < A) (y : ℝ) :
    MeasureTheory.Integrable (fun u : ℝ => Real.exp (-(A * u ^ 2)) * Real.cos (y * u)) := by
  have hg : Integrable (fun u : ℝ => Real.exp (-(A * u ^ 2))) := by
    have h := _root_.integrable_exp_neg_mul_sq hA
    simpa only [neg_mul] using h
  refine hg.mul_bdd (c := 1) ?_ ?_
  · fun_prop
  · refine Filter.Eventually.of_forall (fun u => ?_)
    simpa using Real.abs_cos_le_one (y * u)

/-- **Rescaled Gaussian Fourier transform.**
    `∫ e^{-A u²} cos(y u) du = √(π/A)·e^{-y²/(4A)}` for `A > 0`.
    At `y = 0` this is Mathlib's `integral_gaussian`. -/
theorem gaussian_ft_scaled {A : ℝ} (hA : 0 < A) (y : ℝ) :
    (∫ u : ℝ, Real.exp (-(A * u ^ 2)) * Real.cos (y * u))
      = Real.sqrt (Real.pi / A) * Real.exp (-(y ^ 2 / (4 * A))) := by
  have hbre : (0 : ℝ) < ((A : ℂ)).re := by simpa using hA
  have hFT := fourierIntegral_gaussian (b := (A : ℂ)) hbre ((y : ℝ) : ℂ)
  -- integrability of the complex integrand
  have hintg : Integrable
      (fun u : ℝ => Complex.exp (Complex.I * (y : ℂ) * u) * Complex.exp (-(A : ℂ) * (u : ℂ) ^ 2)) := by
    have hfun : (fun u : ℝ => Complex.exp (Complex.I * (y : ℂ) * u)
          * Complex.exp (-(A : ℂ) * (u : ℂ) ^ 2))
        = (fun u : ℝ => Complex.exp (-(A : ℂ) * (u : ℂ) ^ 2
            + (Complex.I * (y : ℂ)) * u + 0)) := by
      funext u
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [hfun]
    exact integrable_cexp_quadratic hbre _ 0
  have hpt : ∀ u : ℝ,
      (Complex.exp (Complex.I * (y : ℂ) * u) * Complex.exp (-(A : ℂ) * (u : ℂ) ^ 2)).re
        = Real.exp (-(A * u ^ 2)) * Real.cos (y * u) := by
    intro u
    have hAreal : Complex.exp (-(A : ℂ) * (u : ℂ) ^ 2)
        = ((Real.exp (-(A * u ^ 2)) : ℝ) : ℂ) := by
      rw [show -(A : ℂ) * (u : ℂ) ^ 2 = ((-(A * u ^ 2) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp]
    have here : (Complex.exp (Complex.I * (y : ℂ) * u)).re = Real.cos (y * u) := by
      rw [show Complex.I * (y : ℂ) * (u : ℂ) = ((y * u : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.exp_ofReal_mul_I_re _
    rw [hAreal, mul_comm, Complex.re_ofReal_mul, here]
  have hlhs : (∫ u : ℝ, Complex.exp (Complex.I * (y : ℂ) * u)
        * Complex.exp (-(A : ℂ) * (u : ℂ) ^ 2)).re
      = ∫ u : ℝ, Real.exp (-(A * u ^ 2)) * Real.cos (y * u) := by
    have hre := _root_.integral_re (𝕜 := ℂ) hintg
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hrhs : ((Real.pi : ℂ) / (A : ℂ)) ^ (1 / 2 : ℂ)
        * Complex.exp (-(y : ℂ) ^ 2 / (4 * (A : ℂ)))
      = ((Real.sqrt (Real.pi / A) * Real.exp (-(y ^ 2 / (4 * A))) : ℝ) : ℂ) := by
    have hA' : (A : ℂ) ≠ 0 := by
      simpa using hA.ne'
    have h1 : ((Real.pi : ℂ) / (A : ℂ)) = ((Real.pi / A : ℝ) : ℂ) := by push_cast; ring
    have h2 : (-(y : ℂ) ^ 2 / (4 * (A : ℂ))) = ((-(y ^ 2 / (4 * A)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h1, h2, ← Complex.ofReal_exp, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_mul, ← Real.sqrt_eq_rpow]
  rw [← hlhs, hFT, hrhs, Complex.ofReal_re]

/-- Sanity check on the constant in `gaussian_ft_scaled`: specialising to `y = 0`
reproduces exactly Mathlib's `integral_gaussian`. -/
theorem gaussian_ft_scaled_zero {A : ℝ} (hA : 0 < A) :
    (∫ u : ℝ, Real.exp (-A * u ^ 2)) = Real.sqrt (Real.pi / A) := by
  have h := gaussian_ft_scaled hA 0
  simp only [zero_mul, Real.cos_zero, mul_one] at h
  simp only [neg_mul]
  rw [h]
  norm_num

-- The two statements are literally the same proposition:
example {A : ℝ} (hA : 0 < A) : True := by
  have h1 : (∫ u : ℝ, Real.exp (-A * u ^ 2)) = Real.sqrt (Real.pi / A) :=
    gaussian_ft_scaled_zero hA
  have h2 : (∫ u : ℝ, Real.exp (-A * u ^ 2)) = Real.sqrt (Real.pi / A) :=
    _root_.integral_gaussian A
  trivial

/-- Gaussian tail on a half-line: `∫_{u > T} e^{-A u²} du ≤ e^{-A T²}/(A T)`. -/
theorem gauss_tail_Ioi {A T : ℝ} (hA : 0 < A) (hT : 0 < T) :
    (∫ u in Set.Ioi T, Real.exp (-(A * u ^ 2))) ≤ Real.exp (-(A * T ^ 2)) / (A * T) := by
  have hAT : -(A * T) < 0 := by nlinarith
  have hint1 : IntegrableOn (fun u : ℝ => Real.exp (-(A * u ^ 2))) (Set.Ioi T) := by
    have h := _root_.integrable_exp_neg_mul_sq hA
    have h' : Integrable (fun u : ℝ => Real.exp (-(A * u ^ 2))) := by
      simpa only [neg_mul] using h
    exact h'.integrableOn
  have hint2 : IntegrableOn (fun u : ℝ => Real.exp (-(A * T) * u)) (Set.Ioi T) :=
    integrableOn_exp_mul_Ioi hAT T
  have hmono : (∫ u in Set.Ioi T, Real.exp (-(A * u ^ 2)))
      ≤ ∫ u in Set.Ioi T, Real.exp (-(A * T) * u) := by
    refine MeasureTheory.setIntegral_mono_on hint1 hint2 measurableSet_Ioi ?_
    intro u hu
    have hu' : T < u := hu
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg (mul_nonneg hA.le (hT.trans hu').le) (sub_nonneg.mpr hu'.le)]
  rw [integral_exp_mul_Ioi hAT T] at hmono
  refine hmono.trans_eq ?_
  rw [show -(A * T) * T = -(A * T ^ 2) by ring, neg_div_neg_eq]

/-- Same tail bound, for the oscillating integrand. -/
theorem gauss_osc_tail_Ioi {A T : ℝ} (hA : 0 < A) (hT : 0 < T) (y : ℝ) :
    |∫ u in Set.Ioi T, Real.exp (-(A * u ^ 2)) * Real.cos (y * u)|
      ≤ Real.exp (-(A * T ^ 2)) / (A * T) := by
  have hint : IntegrableOn
      (fun u : ℝ => Real.exp (-(A * u ^ 2)) * Real.cos (y * u)) (Set.Ioi T) :=
    (gaussian_integrable_scaled hA y).integrableOn
  have hint1 : IntegrableOn (fun u : ℝ => Real.exp (-(A * u ^ 2))) (Set.Ioi T) := by
    have h := _root_.integrable_exp_neg_mul_sq hA
    have h' : Integrable (fun u : ℝ => Real.exp (-(A * u ^ 2))) := by
      simpa only [neg_mul] using h
    exact h'.integrableOn
  calc |∫ u in Set.Ioi T, Real.exp (-(A * u ^ 2)) * Real.cos (y * u)|
      ≤ ∫ u in Set.Ioi T, |Real.exp (-(A * u ^ 2)) * Real.cos (y * u)| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u in Set.Ioi T, Real.exp (-(A * u ^ 2)) := by
        refine MeasureTheory.setIntegral_mono_on hint.abs hint1 measurableSet_Ioi ?_
        intro u _
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        calc Real.exp (-(A * u ^ 2)) * |Real.cos (y * u)|
            ≤ Real.exp (-(A * u ^ 2)) * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
          _ = Real.exp (-(A * u ^ 2)) := mul_one _
    _ ≤ Real.exp (-(A * T ^ 2)) / (A * T) := gauss_tail_Ioi hA hT

end

end Erdos123Band
