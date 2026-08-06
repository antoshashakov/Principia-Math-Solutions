import Mathlib

set_option maxHeartbeats 4000000

namespace SendovN.RootUnity11

open Finset

/-!
# The degree-11 separation constant, without trigonometry

The degree-9 pattern with the new **quintic** Laurent identity: for `ω ≠ 0` and
`t := ω + ω⁻¹`,

    ω⁵ · (t⁵ + t⁴ - 4t³ - 3t² + 3t + 1) = ∑_{k<11} ωᵏ

(from the Chebyshev-type sums `ωʲ + ω⁻ʲ = pⱼ(t)`, `p₁…p₅ = t, t²-2, t³-3t,
t⁴-4t²+2, t⁵-5t³+5t`; their sum plus `1` is the quintic).  For an eleventh root of
unity `ω ≠ 1` the geometric sum vanishes, so `Q(t) = 0` with
`Q(t) = t⁵ + t⁴ - 4t³ - 3t² + 3t + 1` — the minimal polynomial of `2cos(2π/11)`
(irreducible: no factor split this time).  The largest root is beaten by
`τ₀ = 8413/5000 = 1.6826` via the factor-difference trick
`Q(t) - Q(τ₀) = (t - τ₀)·R(t)` with `R` an explicit quartic, positive on `[τ₀, 2]`
by termwise monotonicity, and `Q(τ₀) > 0` exact-rationally.  Hence
`t < τ₀` and `‖1 - ω‖² = 2 - t > 317400/10⁶ > 316969/10⁶ = (563/1000)²`.
The paper's Machin/arctan route to `2 sin(π/11)` is not used.
-/

/-! ### Step 2 — the nontrivial eleventh roots of unity stay away from `1` -/

/-- **`‖1 - ω‖ > 563/1000` for every eleventh root of unity other than `1`.** -/
theorem norm_one_sub_gt11 {om : ℂ} (h11 : om ^ 11 = 1) (hne : om ≠ 1) :
    (563/1000 : ℝ) < ‖1 - om‖ := by
  have hom0 : om ≠ 0 := by
    intro h
    rw [h] at h11
    norm_num at h11
  -- `‖ω‖ = 1`, by factoring `x¹¹ - 1`
  have hnorm : ‖om‖ = 1 := by
    have h1 : ‖om‖ ^ 11 = 1 := by rw [← norm_pow, h11, norm_one]
    have hfac : (‖om‖ - 1) * (‖om‖ ^ 10 + ‖om‖ ^ 9 + ‖om‖ ^ 8 + ‖om‖ ^ 7 + ‖om‖ ^ 6
        + ‖om‖ ^ 5 + ‖om‖ ^ 4 + ‖om‖ ^ 3 + ‖om‖ ^ 2 + ‖om‖ + 1) = 0 := by
      linear_combination h1
    have hpos : (0:ℝ) < ‖om‖ ^ 10 + ‖om‖ ^ 9 + ‖om‖ ^ 8 + ‖om‖ ^ 7 + ‖om‖ ^ 6
        + ‖om‖ ^ 5 + ‖om‖ ^ 4 + ‖om‖ ^ 3 + ‖om‖ ^ 2 + ‖om‖ + 1 := by positivity
    have := (mul_eq_zero.mp hfac).resolve_right hpos.ne'
    linarith
  -- `ω⁻¹ = conj ω`
  have hnsqR : Complex.normSq om = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]; norm_num
  have hinv : om⁻¹ = (starRingEnd ℂ) om := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [Complex.mul_conj, hnsqR]
    norm_num
  -- `t := 2 Re ω`, and `(t : ℂ) = ω + ω⁻¹`
  set t : ℝ := 2 * om.re with ht
  have hts : ((t : ℝ) : ℂ) = om + om⁻¹ := by
    rw [hinv, ht, ← Complex.add_conj]
  -- the geometric sum vanishes
  have hgeom : ∑ k ∈ range 11, om ^ k = 0 := by
    have hmul : (∑ k ∈ range 11, om ^ k) * (om - 1) = om ^ 11 - 1 := geom_sum_mul om 11
    rw [h11, sub_self] at hmul
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero_of_ne hne)
  -- the quintic Laurent identity: needs only `ω ≠ 0`
  have hid : om ^ 5 * ((om + om⁻¹) ^ 5 + (om + om⁻¹) ^ 4 - 4 * (om + om⁻¹) ^ 3
      - 3 * (om + om⁻¹) ^ 2 + 3 * (om + om⁻¹) + 1) = ∑ k ∈ range 11, om ^ k := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    field_simp
    ring
  rw [hgeom] at hid
  have hfacC : ((t : ℝ) : ℂ) ^ 5 + ((t : ℝ) : ℂ) ^ 4 - 4 * ((t : ℝ) : ℂ) ^ 3
      - 3 * ((t : ℝ) : ℂ) ^ 2 + 3 * ((t : ℝ) : ℂ) + 1 = 0 := by
    rw [hts]
    exact (mul_eq_zero.mp hid).resolve_left (pow_ne_zero 5 hom0)
  have hQt : t ^ 5 + t ^ 4 - 4 * t ^ 3 - 3 * t ^ 2 + 3 * t + 1 = 0 := by
    have hc : ((t ^ 5 + t ^ 4 - 4 * t ^ 3 - 3 * t ^ 2 + 3 * t + 1 : ℝ) : ℂ) = 0 := by
      push_cast; exact hfacC
    exact_mod_cast hc
  -- `‖1 - ω‖² = 2 - t`
  have hns : ‖1 - om‖ ^ 2 = 2 - t := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hre : (1 - om).re = 1 - om.re := by simp
    have him : (1 - om).im = -om.im := by simp
    rw [hre, him, ht]
    have hna : om.re * om.re + om.im * om.im = 1 := by
      rw [Complex.normSq_apply] at hnsqR; exact hnsqR
    linear_combination hna
  have ht2 : t ≤ 2 := by
    have h := Complex.re_le_norm om
    rw [hnorm] at h
    rw [ht]; linarith
  -- the largest root of the quintic is `< τ₀ = 8413/5000`, by the
  -- factor-difference trick `Q(t) - Q(τ₀) = (t - τ₀)·R(t)`
  have hlt : t < 8413/5000 := by
    by_contra hcon
    push_neg at hcon
    have hA : (0:ℝ) ≤ t - 8413/5000 := by linarith
    -- the quartic cofactor is positive on `[τ₀, 2]`, termwise
    have h2p : ((8413:ℝ)/5000) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num) hcon 2
    have h3p : ((8413:ℝ)/5000) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) hcon 3
    have h4p : ((8413:ℝ)/5000) ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ (by norm_num) hcon 4
    have hB : (0:ℝ) < t ^ 4 + (8413/5000 + 1) * t ^ 3
        + ((8413/5000) ^ 2 + 8413/5000 - 4) * t ^ 2
        + ((8413/5000) ^ 3 + (8413/5000) ^ 2 - 4 * (8413/5000) - 3) * t
        + ((8413/5000) ^ 4 + (8413/5000) ^ 3 - 4 * (8413/5000) ^ 2
          - 3 * (8413/5000) + 3) := by
      nlinarith [h2p, h3p, h4p, hcon, ht2]
    -- `(t-τ₀)·R(t) = Q(t) - Q(τ₀) = -Q(τ₀) < 0`, yet it is `≥ 0`
    nlinarith [mul_nonneg hA hB.le, hQt]
  have hval : (563/1000 : ℝ) ^ 2 = 316969/1000000 := by norm_num
  have hsq : (563/1000 : ℝ) ^ 2 < ‖1 - om‖ ^ 2 := by
    rw [hns, hval]; linarith
  nlinarith [hsq, norm_nonneg (1 - om)]

/-! ### Step 1 — the integral, and the constant it forces -/

/-- `∫₀¹ tᵐ dt = 1/(m+1)`, for the ℂ-valued integrand. -/
theorem integral_t_pow (m : ℕ) :
    (∫ t in (0:ℝ)..1, ((t : ℂ) ^ m)) = 1 / ((m : ℂ) + 1) := by
  have h : ∀ t : ℝ, ((t : ℂ) ^ m) = ((t ^ m : ℝ) : ℂ) := by
    intro t; push_cast; ring
  simp only [h]
  rw [intervalIntegral.integral_ofReal, integral_pow]
  push_cast
  simp

/-- `∫₀¹ (1 - tw)¹⁰ dt`, expanded. -/
theorem integral_one_sub_pow (w : ℂ) :
    (∫ t in (0:ℝ)..1, (1 - (t : ℂ) * w) ^ 10)
      = ∑ m ∈ range 11, ((10).choose m : ℂ) * (-w) ^ m / ((m : ℂ) + 1) := by
  have hexp : ∀ t : ℝ, (1 - (t : ℂ) * w) ^ 10
      = ∑ m ∈ range 11, ((10).choose m : ℂ) * (-w) ^ m * (t : ℂ) ^ m := by
    intro t
    rw [show (1 - (t : ℂ) * w) = ((t : ℂ) * (-w)) + 1 by ring, add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_pow]
    ring
  simp only [hexp]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_t_pow]
    ring
  · intro m _
    apply Continuous.intervalIntegrable
    fun_prop

/-- The `C(10,m)` binomial coefficients, as closed numerals. -/
theorem sum_closed (w : ℂ) :
    (∑ m ∈ range 11, ((10).choose m : ℂ) * (-w) ^ m / ((m : ℂ) + 1))
      = 1 - 5*w + 15*w^2 - 30*w^3 + 42*w^4 - 42*w^5 + 30*w^6 - 15*w^7
        + 5*w^8 - w^9 + w^10/11 := by
  have c0 : ((10:ℕ).choose 0 : ℂ) = 1 := by rw [show (10:ℕ).choose 0 = 1 by decide]; norm_num
  have c1 : ((10:ℕ).choose 1 : ℂ) = 10 := by rw [show (10:ℕ).choose 1 = 10 by decide]; norm_num
  have c2 : ((10:ℕ).choose 2 : ℂ) = 45 := by rw [show (10:ℕ).choose 2 = 45 by decide]; norm_num
  have c3 : ((10:ℕ).choose 3 : ℂ) = 120 := by
    rw [show (10:ℕ).choose 3 = 120 by decide]; norm_num
  have c4 : ((10:ℕ).choose 4 : ℂ) = 210 := by
    rw [show (10:ℕ).choose 4 = 210 by decide]; norm_num
  have c5 : ((10:ℕ).choose 5 : ℂ) = 252 := by
    rw [show (10:ℕ).choose 5 = 252 by decide]; norm_num
  have c6 : ((10:ℕ).choose 6 : ℂ) = 210 := by
    rw [show (10:ℕ).choose 6 = 210 by decide]; norm_num
  have c7 : ((10:ℕ).choose 7 : ℂ) = 120 := by
    rw [show (10:ℕ).choose 7 = 120 by decide]; norm_num
  have c8 : ((10:ℕ).choose 8 : ℂ) = 45 := by rw [show (10:ℕ).choose 8 = 45 by decide]; norm_num
  have c9 : ((10:ℕ).choose 9 : ℂ) = 10 := by rw [show (10:ℕ).choose 9 = 10 by decide]; norm_num
  have c10 : ((10:ℕ).choose 10 : ℂ) = 1 := by
    rw [show (10:ℕ).choose 10 = 1 by decide]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]
  push_cast
  ring

/-- **The degree-11 separation constant.**  A Grace–Walsh–Szegő point whose degree-ten
integral vanishes is farther than `563/1000` from the origin.

`2 sin(π/11)` enters here as a root of `t⁵ + t⁴ - 4t³ - 3t² + 3t + 1` (in
`t = 2 Re ω`), bounded by `τ₀ = 1.6826`. -/
theorem norm_gt_of_integral_zero11 {w : ℂ}
    (h : (∫ t in (0:ℝ)..1, (1 - (t : ℂ) * w) ^ 10) = 0) :
    (563/1000 : ℝ) < ‖w‖ := by
  rw [integral_one_sub_pow, sum_closed] at h
  have hw0 : w ≠ 0 := by
    intro hw
    rw [hw] at h
    norm_num at h
  -- `11w·(the sum) = 1 - (1-w)¹¹`, because `11·C(10,m)/(m+1) = C(11,m+1)`
  have h11 : (1 - w) ^ 11 = 1 := by linear_combination (-11*w) * h
  have hne : (1 - w) ≠ 1 := by
    intro hh
    exact hw0 (by linear_combination -hh)
  have hb := norm_one_sub_gt11 h11 hne
  simpa using hb

end SendovN.RootUnity11

#print axioms SendovN.RootUnity11.norm_one_sub_gt11
#print axioms SendovN.RootUnity11.integral_t_pow
#print axioms SendovN.RootUnity11.integral_one_sub_pow
#print axioms SendovN.RootUnity11.sum_closed
#print axioms SendovN.RootUnity11.norm_gt_of_integral_zero11
