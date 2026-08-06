import Mathlib

set_option maxHeartbeats 4000000

namespace SendovN.RootUnity10

open Finset

/-!
# The degree-10 separation constant, without trigonometry

The degree-9 pattern (`Sendov9/RootUnity.lean`) is followed exactly, except that the
single Laurent identity is replaced by a **case split at `ω⁵`**: from `ω¹⁰ = 1`,
`(ω⁵ - 1)(ω⁵ + 1) = 0`, and with `t := ω + ω⁻¹ = 2 Re ω`:

* `ω⁵ = 1, ω ≠ 1` : `ω²·(t² + t - 1) = 1 + ω + ω² + ω³ + ω⁴ = 0`, so `t² + t - 1 = 0`
  (the roots are `(-1 ± √5)/2 ≤ 0.62`);
* `ω⁵ = -1, ω ≠ -1` : `ω²·(t² - t - 1) = 1 - ω + ω² - ω³ + ω⁴ = 0`, so
  `t² - t - 1 = 0` (the binding branch: the golden ratio `t = (1+√5)/2 ≈ 1.6180`);
* `ω = -1` : `t = -2` directly.

In every case `t < 1618076/10⁶`, hence `‖1 - ω‖² = 2 - t > 381924/10⁶ = (309/500)²`.
The rational core is exactly `Sendov9to11.m10_certificate`
(`(2·(309/500) + 1)² < 5 ⟺ (309/500)² < 2 - (1+√5)/2`), realized here as the exact
factor-difference bound `(t - c)(t + c - 1) = (t² - t - 1) - (c² - c - 1)` at
`c = 1618076/10⁶` with `c² - c - 1 > 0`.  No `Real.sin` appears.
-/

/-! ### Step 2 — the nontrivial tenth roots of unity stay away from `1` -/

/-- **`‖1 - ω‖ > 309/500` for every tenth root of unity other than `1`.** -/
theorem norm_one_sub_gt10 {om : ℂ} (h10 : om ^ 10 = 1) (hne : om ≠ 1) :
    (309/500 : ℝ) < ‖1 - om‖ := by
  have hom0 : om ≠ 0 := by
    intro h
    rw [h] at h10
    norm_num at h10
  -- `‖ω‖ = 1`, by factoring `x¹⁰ - 1`
  have hnorm : ‖om‖ = 1 := by
    have h1 : ‖om‖ ^ 10 = 1 := by rw [← norm_pow, h10, norm_one]
    have hfac : (‖om‖ - 1) * (‖om‖ ^ 9 + ‖om‖ ^ 8 + ‖om‖ ^ 7 + ‖om‖ ^ 6 + ‖om‖ ^ 5
        + ‖om‖ ^ 4 + ‖om‖ ^ 3 + ‖om‖ ^ 2 + ‖om‖ + 1) = 0 := by
      linear_combination h1
    have hpos : (0:ℝ) < ‖om‖ ^ 9 + ‖om‖ ^ 8 + ‖om‖ ^ 7 + ‖om‖ ^ 6 + ‖om‖ ^ 5
        + ‖om‖ ^ 4 + ‖om‖ ^ 3 + ‖om‖ ^ 2 + ‖om‖ + 1 := by positivity
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
  -- `‖1 - ω‖² = 2 - t`
  have hns : ‖1 - om‖ ^ 2 = 2 - t := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hre : (1 - om).re = 1 - om.re := by simp
    have him : (1 - om).im = -om.im := by simp
    rw [hre, him, ht]
    have hna : om.re * om.re + om.im * om.im = 1 := by
      rw [Complex.normSq_apply] at hnsqR; exact hnsqR
    linear_combination hna
  -- the case split at `ω⁵`
  have hsplit : (om ^ 5 - 1) * (om ^ 5 + 1) = 0 := by linear_combination h10
  have hlt : t < 1618076/1000000 := by
    rcases mul_eq_zero.mp hsplit with h5 | h5
    · -- `ω⁵ = 1`: the quadratic `t² + t - 1 = 0`
      have h5' : om ^ 5 = 1 := by linear_combination h5
      have hgeom : ∑ k ∈ range 5, om ^ k = 0 := by
        have hmul : (∑ k ∈ range 5, om ^ k) * (om - 1) = om ^ 5 - 1 := geom_sum_mul om 5
        rw [h5', sub_self] at hmul
        exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero_of_ne hne)
      have hid : om ^ 2 * ((om + om⁻¹) ^ 2 + (om + om⁻¹) - 1)
          = ∑ k ∈ range 5, om ^ k := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]
        field_simp
        ring
      rw [hgeom] at hid
      have hfacC : ((t : ℝ) : ℂ) ^ 2 + ((t : ℝ) : ℂ) - 1 = 0 := by
        rw [hts]
        exact (mul_eq_zero.mp hid).resolve_left (pow_ne_zero 2 hom0)
      have hfacR : t ^ 2 + t - 1 = 0 := by
        have hc : ((t ^ 2 + t - 1 : ℝ) : ℂ) = 0 := by push_cast; exact hfacC
        exact_mod_cast hc
      -- both roots are `≤ (√5-1)/2 < 1.618076`
      by_contra hcon
      push_neg at hcon
      have hA : (0:ℝ) ≤ t - 1618076/1000000 := by linarith
      have hB : (0:ℝ) ≤ t + 1618076/1000000 + 1 := by linarith
      -- `(t-c)(t+c+1) = (t²+t-1) - (c²+c-1) = -(c²+c-1) < 0`, yet it is `≥ 0`
      nlinarith [mul_nonneg hA hB, hfacR]
    · -- `ω⁵ = -1`
      have h5' : om ^ 5 = -1 := by linear_combination h5
      by_cases hm1 : om = -1
      · -- `t = -2`
        have hre : om.re = -1 := by rw [hm1]; simp
        rw [ht, hre]; norm_num
      · -- the alternating sum vanishes
        have hmul : (om + 1) * (1 - om + om ^ 2 - om ^ 3 + om ^ 4) = om ^ 5 + 1 := by
          ring
        rw [h5'] at hmul
        norm_num at hmul
        have hne1 : om + 1 ≠ 0 := fun hcon' => hm1 (by linear_combination hcon')
        have halt : 1 - om + om ^ 2 - om ^ 3 + om ^ 4 = 0 := hmul.resolve_left hne1
        -- the Laurent identity: needs only `ω ≠ 0`
        have hid : om ^ 2 * ((om + om⁻¹) ^ 2 - (om + om⁻¹) - 1)
            = 1 - om + om ^ 2 - om ^ 3 + om ^ 4 := by
          field_simp
          ring
        rw [halt] at hid
        have hfacC : ((t : ℝ) : ℂ) ^ 2 - ((t : ℝ) : ℂ) - 1 = 0 := by
          rw [hts]
          exact (mul_eq_zero.mp hid).resolve_left (pow_ne_zero 2 hom0)
        have hfacR : t ^ 2 - t - 1 = 0 := by
          have hc : ((t ^ 2 - t - 1 : ℝ) : ℂ) = 0 := by push_cast; exact hfacC
          exact_mod_cast hc
        -- the golden ratio `(1+√5)/2 < 1.618076`, by the factor-difference trick
        by_contra hcon
        push_neg at hcon
        have hA : (0:ℝ) ≤ t - 1618076/1000000 := by linarith
        have hB : (0:ℝ) ≤ t + 1618076/1000000 - 1 := by linarith
        -- `(t-c)(t+c-1) = (t²-t-1) - (c²-c-1) = -(c²-c-1) < 0`, yet it is `≥ 0`
        nlinarith [mul_nonneg hA hB, hfacR]
  have hval : (309/500 : ℝ) ^ 2 = 381924/1000000 := by norm_num
  have hsq : (309/500 : ℝ) ^ 2 < ‖1 - om‖ ^ 2 := by
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

/-- `∫₀¹ (1 - tw)⁹ dt`, expanded. -/
theorem integral_one_sub_pow (w : ℂ) :
    (∫ t in (0:ℝ)..1, (1 - (t : ℂ) * w) ^ 9)
      = ∑ m ∈ range 10, ((9).choose m : ℂ) * (-w) ^ m / ((m : ℂ) + 1) := by
  have hexp : ∀ t : ℝ, (1 - (t : ℂ) * w) ^ 9
      = ∑ m ∈ range 10, ((9).choose m : ℂ) * (-w) ^ m * (t : ℂ) ^ m := by
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

/-- The `C(9,m)` binomial coefficients, as closed numerals. -/
theorem sum_closed (w : ℂ) :
    (∑ m ∈ range 10, ((9).choose m : ℂ) * (-w) ^ m / ((m : ℂ) + 1))
      = 1 - (9/2)*w + 12*w^2 - 21*w^3 + (126/5)*w^4 - 21*w^5 + 12*w^6
        - (9/2)*w^7 + w^8 - w^9/10 := by
  have c0 : ((9:ℕ).choose 0 : ℂ) = 1 := by rw [show (9:ℕ).choose 0 = 1 by decide]; norm_num
  have c1 : ((9:ℕ).choose 1 : ℂ) = 9 := by rw [show (9:ℕ).choose 1 = 9 by decide]; norm_num
  have c2 : ((9:ℕ).choose 2 : ℂ) = 36 := by rw [show (9:ℕ).choose 2 = 36 by decide]; norm_num
  have c3 : ((9:ℕ).choose 3 : ℂ) = 84 := by rw [show (9:ℕ).choose 3 = 84 by decide]; norm_num
  have c4 : ((9:ℕ).choose 4 : ℂ) = 126 := by rw [show (9:ℕ).choose 4 = 126 by decide]; norm_num
  have c5 : ((9:ℕ).choose 5 : ℂ) = 126 := by rw [show (9:ℕ).choose 5 = 126 by decide]; norm_num
  have c6 : ((9:ℕ).choose 6 : ℂ) = 84 := by rw [show (9:ℕ).choose 6 = 84 by decide]; norm_num
  have c7 : ((9:ℕ).choose 7 : ℂ) = 36 := by rw [show (9:ℕ).choose 7 = 36 by decide]; norm_num
  have c8 : ((9:ℕ).choose 8 : ℂ) = 9 := by rw [show (9:ℕ).choose 8 = 9 by decide]; norm_num
  have c9 : ((9:ℕ).choose 9 : ℂ) = 1 := by rw [show (9:ℕ).choose 9 = 1 by decide]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9]
  push_cast
  ring

/-- **The degree-10 separation constant.**  A Grace–Walsh–Szegő point whose degree-nine
integral vanishes is farther than `309/500` from the origin.

`2 sin(π/10) = (√5 - 1)/2` enters here as a root of `t² - t - 1` (in `t = 2 Re ω`). -/
theorem norm_gt_of_integral_zero10 {w : ℂ}
    (h : (∫ t in (0:ℝ)..1, (1 - (t : ℂ) * w) ^ 9) = 0) :
    (309/500 : ℝ) < ‖w‖ := by
  rw [integral_one_sub_pow, sum_closed] at h
  have hw0 : w ≠ 0 := by
    intro hw
    rw [hw] at h
    norm_num at h
  -- `10w·(the sum) = 1 - (1-w)¹⁰`, because `10·C(9,m)/(m+1) = C(10,m+1)`
  have h10 : (1 - w) ^ 10 = 1 := by linear_combination (-10*w) * h
  have hne : (1 - w) ≠ 1 := by
    intro hh
    exact hw0 (by linear_combination -hh)
  have hb := norm_one_sub_gt10 h10 hne
  simpa using hb

end SendovN.RootUnity10

#print axioms SendovN.RootUnity10.norm_one_sub_gt10
#print axioms SendovN.RootUnity10.integral_t_pow
#print axioms SendovN.RootUnity10.integral_one_sub_pow
#print axioms SendovN.RootUnity10.sum_closed
#print axioms SendovN.RootUnity10.norm_gt_of_integral_zero10
