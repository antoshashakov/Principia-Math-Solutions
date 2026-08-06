import Mathlib
import SendovNBridge

set_option maxHeartbeats 4000000

/-!
# P5: `JBoundN` — the comparison integral `J = ∫₀ᵃ (1 − tμ)^N dt`

Port of the `J` material from `Sendov9/Sigma22.lean` (`integrand_expand`, `J_sum`,
`J_closed_form`, `inv_sqrt_ge`, `norm_J_ge`).

* `integrand_expand` / `J_sum` generalize symbolically to any `N` (binomial theorem).
* `J_closed_form` rests on `C(N,k)/(k+1) = C(N+1,k+1)/(N+1)`, closed by `ring` on
  explicit numerals — so it is instantiated at the two needed exponents
  (`N = 9 → n = 10` and `N = 10 → n = 11`), exactly as the plan prescribes.
* `norm_J_ge` **is** provable generically: the places degree 9 used the numeral `9`
  (`norm_num` on `‖(9:ℂ)‖`, `ring` on `(1/9)·9 = 1`) become `Complex.norm_natCast`
  and `field_simp` against `(n:ℝ) ≠ 0`.
-/

namespace SendovN.JBoundN

open Finset intervalIntegral

/-- Binomial expansion of the integrand, generic in `N`. -/
theorem integrand_expand (N : ℕ) (mu : ℂ) (t : ℝ) :
    (1 - (t : ℂ) * mu) ^ N
      = ∑ k ∈ Finset.range (N + 1),
          ((Nat.choose N k : ℂ) * (-mu) ^ k) * (t : ℂ) ^ k := by
  have h := add_pow (-((t : ℂ) * mu)) 1 N
  simp only [one_pow, mul_one] at h
  rw [show (1 : ℂ) - (t : ℂ) * mu = -((t : ℂ) * mu) + 1 from by ring, h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (-((t : ℂ) * mu)) = (t : ℂ) * (-mu) from by ring, mul_pow]
  ring

/-- `J` as an explicit finite sum, generic in `N`. -/
theorem J_sum (N : ℕ) (mu : ℂ) (a : ℝ) :
    (∫ t in (0:ℝ)..a, (1 - (t : ℂ) * mu) ^ N)
      = ∑ k ∈ Finset.range (N + 1),
          ((Nat.choose N k : ℂ) * (-mu) ^ k) * ((a ^ (k + 1) / (k + 1) : ℝ) : ℂ) := by
  simp only [integrand_expand N mu]
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl fun k _ => by
      rw [intervalIntegral.integral_const_mul, BridgeN.integral_cpow_ofReal]
  · intro k _
    apply Continuous.intervalIntegrable
    continuity

/-- **Closed form at `N = 9`** (degree 10): `J = (1 − (1−aμ)¹⁰)/(10μ)`. -/
theorem J_closed_form_deg10 {mu : ℂ} (hmu : mu ≠ 0) (a : ℝ) :
    (∫ t in (0:ℝ)..a, (1 - (t : ℂ) * mu) ^ 9)
      = (1 - (1 - (a : ℂ) * mu) ^ 10) / (10 * mu) := by
  rw [J_sum]
  have hne : (10 : ℂ) * mu ≠ 0 := by
    simp only [ne_eq, mul_eq_zero]
    push_neg
    exact ⟨by norm_num, hmu⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    show Nat.choose 9 0 = 1 from by decide, show Nat.choose 9 1 = 9 from by decide,
    show Nat.choose 9 2 = 36 from by decide, show Nat.choose 9 3 = 84 from by decide,
    show Nat.choose 9 4 = 126 from by decide, show Nat.choose 9 5 = 126 from by decide,
    show Nat.choose 9 6 = 84 from by decide, show Nat.choose 9 7 = 36 from by decide,
    show Nat.choose 9 8 = 9 from by decide, show Nat.choose 9 9 = 1 from by decide]
  push_cast
  rw [eq_div_iff hne]
  ring

/-- **Closed form at `N = 10`** (degree 11): `J = (1 − (1−aμ)¹¹)/(11μ)`. -/
theorem J_closed_form_deg11 {mu : ℂ} (hmu : mu ≠ 0) (a : ℝ) :
    (∫ t in (0:ℝ)..a, (1 - (t : ℂ) * mu) ^ 10)
      = (1 - (1 - (a : ℂ) * mu) ^ 11) / (11 * mu) := by
  rw [J_sum]
  have hne : (11 : ℂ) * mu ≠ 0 := by
    simp only [ne_eq, mul_eq_zero]
    push_neg
    exact ⟨by norm_num, hmu⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    show Nat.choose 10 0 = 1 from by decide, show Nat.choose 10 1 = 10 from by decide,
    show Nat.choose 10 2 = 45 from by decide, show Nat.choose 10 3 = 120 from by decide,
    show Nat.choose 10 4 = 210 from by decide, show Nat.choose 10 5 = 252 from by decide,
    show Nat.choose 10 6 = 210 from by decide, show Nat.choose 10 7 = 120 from by decide,
    show Nat.choose 10 8 = 45 from by decide, show Nat.choose 10 9 = 10 from by decide,
    show Nat.choose 10 10 = 1 from by decide]
  push_cast
  rw [eq_div_iff hne]
  ring

/-- `1/√(1−η²) ≥ 1 + η²/2` for `0 ≤ η² < 1` (paper eq. (scalar); degree-free). -/
theorem inv_sqrt_ge {e : ℝ} (h0 : 0 ≤ e) (h1 : e < 1) :
    1 + e / 2 ≤ 1 / Real.sqrt (1 - e) := by
  have hpos : 0 < 1 - e := by linarith
  have hs : 0 < Real.sqrt (1 - e) := Real.sqrt_pos.mpr hpos
  rw [le_div_iff₀ hs]
  have hsq : Real.sqrt (1 - e) ^ 2 = 1 - e := Real.sq_sqrt (le_of_lt hpos)
  nlinarith [Real.sqrt_nonneg (1 - e), hsq, sq_nonneg (Real.sqrt (1 - e) - 1), sq_nonneg e]

/-- **The `|J|` lower bound, generic in the exponent `n ≥ 1`.**
With `R = |1 − aμ|` and `|μ| = √(1−η²)`:
`1/n + η²/(2n) − Rⁿ/(n|μ|) ≤ |(1 − (1−aμ)ⁿ)/(nμ)|`. -/
theorem norm_J_ge {mu : ℂ} (hmu : mu ≠ 0) {n : ℕ} (hn : 0 < n) (a eta : ℝ)
    (heta : ‖mu‖ ^ 2 = 1 - eta ^ 2) (he0 : 0 ≤ eta) (he1 : eta < 1) :
    1 / n + eta ^ 2 / (2 * n) - ‖1 - (a : ℂ) * mu‖ ^ n / (n * ‖mu‖)
      ≤ ‖(1 - (1 - (a : ℂ) * mu) ^ n) / (n * mu)‖ := by
  have hmn : 0 < ‖mu‖ := norm_pos_iff.mpr hmu
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnR0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  set R := ‖1 - (a : ℂ) * mu‖ with hR
  have hnum : 1 - R ^ n ≤ ‖1 - (1 - (a : ℂ) * mu) ^ n‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((1 - (a : ℂ) * mu) ^ n)
    simpa [norm_pow, hR] using this
  have hden : ‖((n : ℕ) : ℂ) * mu‖ = (n : ℝ) * ‖mu‖ := by
    rw [norm_mul, Complex.norm_natCast]
  rw [norm_div, hden]
  have hnmupos : (0 : ℝ) < (n : ℝ) * ‖mu‖ := mul_pos hnR hmn
  have hstep : (1 - R ^ n) / ((n : ℝ) * ‖mu‖)
      ≤ ‖1 - (1 - (a : ℂ) * mu) ^ n‖ / ((n : ℝ) * ‖mu‖) :=
    div_le_div_of_nonneg_right hnum hnmupos.le
  refine le_trans ?_ hstep
  have hmnorm : ‖mu‖ = Real.sqrt (1 - eta ^ 2) := by
    rw [← heta, Real.sqrt_sq (norm_nonneg mu)]
  have hkey : 1 + eta ^ 2 / 2 ≤ 1 / ‖mu‖ := by
    rw [hmnorm]
    exact inv_sqrt_ge (by positivity) (by nlinarith)
  have hsplit : (1 - R ^ n) / ((n : ℝ) * ‖mu‖)
      = 1 / ((n : ℝ) * ‖mu‖) - R ^ n / ((n : ℝ) * ‖mu‖) := by
    ring
  rw [hsplit]
  have hhead : 1 / (n : ℝ) + eta ^ 2 / (2 * (n : ℝ)) ≤ 1 / ((n : ℝ) * ‖mu‖) := by
    rw [le_div_iff₀ hnmupos]
    have hexp : (1 / (n : ℝ) + eta ^ 2 / (2 * (n : ℝ))) * ((n : ℝ) * ‖mu‖)
        = (1 + eta ^ 2 / 2) * ‖mu‖ := by
      field_simp
    rw [hexp]
    calc (1 + eta ^ 2 / 2) * ‖mu‖ ≤ (1 / ‖mu‖) * ‖mu‖ :=
          mul_le_mul_of_nonneg_right hkey (norm_nonneg mu)
      _ = 1 := by field_simp
  linarith

end SendovN.JBoundN

#print axioms SendovN.JBoundN.integrand_expand
#print axioms SendovN.JBoundN.J_sum
#print axioms SendovN.JBoundN.J_closed_form_deg10
#print axioms SendovN.JBoundN.J_closed_form_deg11
#print axioms SendovN.JBoundN.inv_sqrt_ge
#print axioms SendovN.JBoundN.norm_J_ge
