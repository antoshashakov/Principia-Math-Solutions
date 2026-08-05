import Mathlib
import Sendov9.MidAnalytic
import Sendov9.EIntegrals

set_option maxHeartbeats 4000000

namespace Sendov9.MidMaj

open Finset intervalIntegral

/-!
# From the `t`-integral to the certificate's `v`-integral

`IminusJ.norm_I_sub_J_le` produces the majorant as an integral over `[0,a]` in `t`,

    ∫₀ᵃ tᵐ q(t)^{ℓ} dt,        q(t) = 1 - 2 L_S(a) t + (1-η²)t²,

while `E_S(a,η)` — and hence every certificate — is stated over `[0,1]` in `v`:

    E_S(a,η) = ∑_{m=2}^{8} c_m a^{m+1} η^m ∫₀¹ vᵐ q_S(a,η;v)^{ℓ_m} dv.

The two are related by `t = av`, and this file is that change of variables, together
with the two facts about `q(t)` that the pointwise estimate needs.

The substitution is the only place a scaling factor appears, and it is exactly the
`a^{m+1}` in `E_S`: `∫₀ᵃ tᵐ q(t)^ℓ dt = a^{m+1} ∫₀¹ vᵐ q_S(a,η;v)^ℓ dv`.

Composed with `EIntegrals`, this turns each row's analytic majorant into the closed
rational expression the Bernstein certificate is stated against.

Sendov's conjecture in degree nine remains unproven.
-/

/-- The majorant in `t`, i.e. `q_S(a,η;·)` before the substitution `t = av`.

Written with `(8 - S + Sa²)/(4a)` rather than `2 L_S(a)` so that `qt_at` is a `ring`
step; the two are equal since `L_S(a) = (8 - S + Sa²)/(8a)`. -/
noncomputable def qt (S a eta t : ℝ) : ℝ :=
  1 - ((8 - S + S * a ^ 2) / (4 * a)) * t + (1 - eta ^ 2) * t ^ 2

theorem continuous_qt (S a eta : ℝ) : Continuous (qt S a eta) := by
  unfold qt
  fun_prop

/-- **The substitution, pointwise.**  `qt(av) = q_S(a,η;v)`. -/
theorem qt_at (S a eta v : ℝ) (ha : a ≠ 0) : qt S a eta (a * v) = MidAn.q S a eta v := by
  unfold qt MidAn.q
  field_simp

/-- `∫₀ᵃ f = a ∫₀¹ f(a·)`. -/
theorem integral_scale (a : ℝ) (f : ℝ → ℝ) :
    (∫ t in (0:ℝ)..a, f t) = a * ∫ v in (0:ℝ)..1, f (a * v) := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := (1:ℝ)) (f := f) a
  simp only [smul_eq_mul, mul_zero, mul_one] at h
  exact h.symm

/-- **The change of variables that produces `E_S`'s `a^{m+1}`.** -/
theorem integral_term (S a eta : ℝ) (ha : 0 < a) (m l : ℕ) :
    (∫ t in (0:ℝ)..a, t ^ m * qt S a eta t ^ l)
      = a ^ (m + 1) * ∫ v in (0:ℝ)..1, v ^ m * MidAn.q S a eta v ^ l := by
  rw [integral_scale a (fun t => t ^ m * qt S a eta t ^ l)]
  have hcongr : ∀ v : ℝ, (a * v) ^ m * qt S a eta (a * v) ^ l
      = a ^ m * (v ^ m * MidAn.q S a eta v ^ l) := by
    intro v
    rw [qt_at S a eta v (ne_of_gt ha), mul_pow]
    ring
  simp only [hcongr]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- `‖1 - tμ‖² ≤ qt(t)` for `t ≥ 0` — the pointwise majorant, before substitution. -/
theorem normSq_le_qt {a eta S t : ℝ} (mu : ℂ) (ha : 0 < a) (ht0 : 0 ≤ t)
    (heta : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : 8 - S + S * a ^ 2 ≤ 8 * a * mu.re) :
    Complex.normSq (1 - (t : ℂ) * mu) ≤ qt S a eta t := by
  rw [MidAn.normSq_one_sub, heta]
  unfold qt
  have h4a : (0:ℝ) < 4 * a := by linarith
  have hdiv : (8 - S + S * a ^ 2) / (4 * a) ≤ 2 * mu.re := by
    rw [div_le_iff₀ h4a]
    linarith [hkey]
  nlinarith [hdiv, ht0]

/-- `qt(t) ≤ 1` on `[0,a]`, inherited from `q_S ≤ 1` on `[0,1]` through `t = a v`. -/
theorem qt_le_one {a eta S lam beta t : ℝ} (ha : 0 < a) (ht0 : 0 ≤ t) (hta : t ≤ a)
    (ha1 : 0 ≤ a) (hab : a ≤ beta) (hbeta : 0 ≤ beta)
    (hL : 8 * a * lam ≤ 8 - S + S * a ^ 2) (h2lb : beta ≤ 2 * lam) :
    qt S a eta t ≤ 1 := by
  have hv0 : 0 ≤ t / a := div_nonneg ht0 (le_of_lt ha)
  have hv1 : t / a ≤ 1 := by
    rw [div_le_one ha]
    exact hta
  have hback : a * (t / a) = t := by field_simp
  have h := MidAn.q_le_one (a := a) (eta := eta) (S := S) (lam := lam) (beta := beta)
    (v := t / a) ha1 hv0 hv1 hab hbeta hL h2lb
  rw [← qt_at S a eta (t / a) (ne_of_gt ha), hback] at h
  exact h

/-- `0 ≤ qt(t)` for `t ≥ 0`, since it dominates a square. -/
theorem qt_nonneg {a eta S t : ℝ} (mu : ℂ) (ha : 0 < a) (ht0 : 0 ≤ t)
    (heta : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : 8 - S + S * a ^ 2 ≤ 8 * a * mu.re) :
    0 ≤ qt S a eta t :=
  le_trans (Complex.normSq_nonneg _) (normSq_le_qt mu ha ht0 heta hkey)

/-! ### The seven terms, in closed form

Composing `integral_term` with `EIntegrals` turns each `∫₀ᵃ tᵐ qt(t)^{ℓₘ} dt` into
`a^{m+1}` times the exact rational expression the certificates are stated against.
`Q1` and `Q2` below are the certificate's own abbreviations. -/

/-- The certificate's `Q1 = -(8 - S + Sa²)/4`. -/
noncomputable def Q1 (S a : ℝ) : ℝ := -((8 - S + S * a ^ 2) / 4)

/-- The certificate's `Q2 = a²(1 - η²)`. -/
noncomputable def Q2 (a eta : ℝ) : ℝ := a ^ 2 * (1 - eta ^ 2)

/-- `q_S(a,η;v) = 1 + Q1·v + Q2·v²`, the shape `EIntegrals` speaks about. -/
theorem q_eq (S a eta v : ℝ) :
    MidAn.q S a eta v = 1 + Q1 S a * v + Q2 a eta * v ^ 2 := by
  unfold MidAn.q Q1 Q2
  ring

/-- `m = 2`, `ℓ = 3`: the first and largest term of `E_S`. -/
theorem term_2_3 (S a eta : ℝ) (ha : 0 < a) :
    (∫ t in (0:ℝ)..a, t ^ 2 * qt S a eta t ^ 3)
      = a ^ 3 * ((1/3 : ℝ) + (3/5 : ℝ) * Q2 a eta + (3/7 : ℝ) * Q2 a eta ^ 2
          + (1/9 : ℝ) * Q2 a eta ^ 3 + (3/4 : ℝ) * Q1 S a + (1 : ℝ) * Q1 S a * Q2 a eta
          + (3/8 : ℝ) * Q1 S a * Q2 a eta ^ 2 + (3/5 : ℝ) * Q1 S a ^ 2
          + (3/7 : ℝ) * Q1 S a ^ 2 * Q2 a eta + (1/6 : ℝ) * Q1 S a ^ 3) := by
  rw [integral_term S a eta ha 2 3]
  simp only [q_eq]
  rw [EInt.int_2_3]

theorem term_3_2 (S a eta : ℝ) (ha : 0 < a) :
    (∫ t in (0:ℝ)..a, t ^ 3 * qt S a eta t ^ 2)
      = a ^ 4 * ((1/4 : ℝ) + (1/3 : ℝ) * Q2 a eta + (1/8 : ℝ) * Q2 a eta ^ 2
          + (2/5 : ℝ) * Q1 S a + (2/7 : ℝ) * Q1 S a * Q2 a eta
          + (1/6 : ℝ) * Q1 S a ^ 2) := by
  rw [integral_term S a eta ha 3 2]
  simp only [q_eq]
  rw [EInt.int_3_2]

theorem term_4_2 (S a eta : ℝ) (ha : 0 < a) :
    (∫ t in (0:ℝ)..a, t ^ 4 * qt S a eta t ^ 2)
      = a ^ 5 * ((1/5 : ℝ) + (2/7 : ℝ) * Q2 a eta + (1/9 : ℝ) * Q2 a eta ^ 2
          + (1/3 : ℝ) * Q1 S a + (1/4 : ℝ) * Q1 S a * Q2 a eta
          + (1/7 : ℝ) * Q1 S a ^ 2) := by
  rw [integral_term S a eta ha 4 2]
  simp only [q_eq]
  rw [EInt.int_4_2]

theorem term_5_1 (S a eta : ℝ) (ha : 0 < a) :
    (∫ t in (0:ℝ)..a, t ^ 5 * qt S a eta t ^ 1)
      = a ^ 6 * ((1/6 : ℝ) + (1/8 : ℝ) * Q2 a eta + (1/7 : ℝ) * Q1 S a) := by
  rw [integral_term S a eta ha 5 1]
  simp only [q_eq]
  rw [EInt.int_5_1]

theorem term_6_1 (S a eta : ℝ) (ha : 0 < a) :
    (∫ t in (0:ℝ)..a, t ^ 6 * qt S a eta t ^ 1)
      = a ^ 7 * ((1/7 : ℝ) + (1/9 : ℝ) * Q2 a eta + (1/8 : ℝ) * Q1 S a) := by
  rw [integral_term S a eta ha 6 1]
  simp only [q_eq]
  rw [EInt.int_6_1]

theorem term_7_0 (S a eta : ℝ) (ha : 0 < a) :
    (∫ t in (0:ℝ)..a, t ^ 7 * qt S a eta t ^ 0) = a ^ 8 * (1/8 : ℝ) := by
  rw [integral_term S a eta ha 7 0]
  simp only [q_eq]
  rw [EInt.int_7_0]

theorem term_8_0 (S a eta : ℝ) (ha : 0 < a) :
    (∫ t in (0:ℝ)..a, t ^ 8 * qt S a eta t ^ 0) = a ^ 9 * (1/9 : ℝ) := by
  rw [integral_term S a eta ha 8 0]
  simp only [q_eq]
  rw [EInt.int_8_0]

end Sendov9.MidMaj

#print axioms Sendov9.MidMaj.continuous_qt
#print axioms Sendov9.MidMaj.qt_at
#print axioms Sendov9.MidMaj.integral_scale
#print axioms Sendov9.MidMaj.integral_term
#print axioms Sendov9.MidMaj.normSq_le_qt
#print axioms Sendov9.MidMaj.qt_le_one
#print axioms Sendov9.MidMaj.qt_nonneg
#print axioms Sendov9.MidMaj.q_eq
#print axioms Sendov9.MidMaj.term_2_3
#print axioms Sendov9.MidMaj.term_3_2
#print axioms Sendov9.MidMaj.term_4_2
#print axioms Sendov9.MidMaj.term_5_1
#print axioms Sendov9.MidMaj.term_6_1
#print axioms Sendov9.MidMaj.term_7_0
#print axioms Sendov9.MidMaj.term_8_0
