import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.RootUnity

open Finset

/-!
# The separation constant, without trigonometry

Lemma 2.1 ends at a Grace–Walsh–Szegő point `w` with `‖w‖ < r` satisfying

    ∫₀¹ (1 - t w)⁸ dt = 0,

and the paper reads off `r > 2 sin(π/9) > 681/1000`.  The classical route runs through
`|1 - e^{2πik/9}| = 2 sin(πk/9)`; this file avoids `Real.sin` entirely.

**Step 1.**  `9w·∫₀¹(1-tw)⁸dt = 1 - (1-w)⁹` is a polynomial identity, because
`9·C(8,m)/(m+1) = C(9,m+1)`.  So a vanishing integral forces `w ≠ 0` (at `w = 0` the
integral is `1`) and `ω⁹ = 1` for `ω := 1 - w`.

**Step 2.**  The minimum of `‖1 - ω‖` over the eight nontrivial ninth roots of unity is
computed *algebraically*.  With `ω⁻¹ = conj ω` (norm one) put `t := 2 Re ω = ω + ω⁻¹`.
Then

    ω⁴ · ((t+1)(t³ - 3t + 1)) = ∑_{k<9} ωᵏ,

which is a **Laurent-polynomial identity** — it needs only `ω ≠ 0`, not `ω⁹ = 1`.  The
right side vanishes because `ω ≠ 1`, so `t = -1` or `t³ - 3t + 1 = 0`.  Since
`‖1 - ω‖² = 2 - t`, the first case gives `3`, and in the second `t < 1.536239` because
`s ↦ s³-3s+1` is increasing past `s = 1` and is already positive there.  Hence

    ‖1 - ω‖² > 2 - 1.536239 = 0.463761 = (681/1000)².

The cubic `t³ - 3t + 1` is of course the minimal polynomial of `2cos(2π/9)`, and
`1.536239` is a rational upper bound for `2cos(2π/9) ≈ 1.5320889`; the margin is 0.3%.
No `Real.sin`, no `Real.arg`, no root-of-unity enumeration appears.

Sendov's conjecture in degree nine remains unproven.
-/

/-! ### Step 2 — the nontrivial ninth roots of unity stay away from `1` -/

/-- **`‖1 - ω‖ > 681/1000` for every ninth root of unity other than `1`.**

Proved through the Laurent identity `ω⁴((t+1)(t³-3t+1)) = ∑_{k<9}ωᵏ` with
`t = ω + ω⁻¹`; no trigonometry. -/
theorem norm_one_sub_gt {om : ℂ} (h9 : om ^ 9 = 1) (hne : om ≠ 1) :
    (681/1000 : ℝ) < ‖1 - om‖ := by
  have hom0 : om ≠ 0 := by
    intro h
    rw [h] at h9
    norm_num at h9
  -- `‖ω‖ = 1`, by factoring `x⁹ - 1` rather than by any monotonicity lemma
  have hnorm : ‖om‖ = 1 := by
    have h1 : ‖om‖ ^ 9 = 1 := by rw [← norm_pow, h9, norm_one]
    have hfac : (‖om‖ - 1) * (‖om‖ ^ 8 + ‖om‖ ^ 7 + ‖om‖ ^ 6 + ‖om‖ ^ 5 + ‖om‖ ^ 4
        + ‖om‖ ^ 3 + ‖om‖ ^ 2 + ‖om‖ + 1) = 0 := by
      linear_combination h1
    have hpos : (0:ℝ) < ‖om‖ ^ 8 + ‖om‖ ^ 7 + ‖om‖ ^ 6 + ‖om‖ ^ 5 + ‖om‖ ^ 4
        + ‖om‖ ^ 3 + ‖om‖ ^ 2 + ‖om‖ + 1 := by positivity
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
  have hgeom : ∑ k ∈ range 9, om ^ k = 0 := by
    have hmul : (∑ k ∈ range 9, om ^ k) * (om - 1) = om ^ 9 - 1 := geom_sum_mul om 9
    rw [h9, sub_self] at hmul
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero_of_ne hne)
  -- the Laurent identity: needs only `ω ≠ 0`
  have hid : om ^ 4 * (((om + om⁻¹) + 1) * ((om + om⁻¹) ^ 3 - 3 * (om + om⁻¹) + 1))
      = ∑ k ∈ range 9, om ^ k := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    field_simp
    ring
  rw [hgeom] at hid
  have hfac : ((t : ℂ) + 1) * ((t : ℂ) ^ 3 - 3 * (t : ℂ) + 1) = 0 := by
    rw [hts]
    exact (mul_eq_zero.mp hid).resolve_left (pow_ne_zero 4 hom0)
  have hfacR : (t + 1) * (t ^ 3 - 3 * t + 1) = 0 := by
    have hc : (((t + 1) * (t ^ 3 - 3 * t + 1) : ℝ) : ℂ) = 0 := by push_cast; exact hfac
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
  -- the two branches of the factorisation
  have hlt : t < 1536239/1000000 := by
    rcases mul_eq_zero.mp hfacR with h | h
    · linarith
    · by_contra hcon
      push_neg at hcon
      have hA : (0:ℝ) ≤ t - 1536239/1000000 := by linarith
      have hB : (0:ℝ) < t ^ 2 + (1536239/1000000) * t + (1536239/1000000) ^ 2 - 3 := by
        nlinarith [hcon]
      -- `(t-a)(t²+at+a²-3) = (t³-3t+1) - (a³-3a+1) = -(a³-3a+1) < 0`, yet it is `≥ 0`
      nlinarith [mul_nonneg hA hB.le, h]
  have hval : (681/1000 : ℝ) ^ 2 = 463761/1000000 := by norm_num
  have hsq : (681/1000 : ℝ) ^ 2 < ‖1 - om‖ ^ 2 := by
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

/-- `∫₀¹ (1 - tw)⁸ dt`, expanded. -/
theorem integral_one_sub_pow (w : ℂ) :
    (∫ t in (0:ℝ)..1, (1 - (t : ℂ) * w) ^ 8)
      = ∑ m ∈ range 9, ((8).choose m : ℂ) * (-w) ^ m / ((m : ℂ) + 1) := by
  have hexp : ∀ t : ℝ, (1 - (t : ℂ) * w) ^ 8
      = ∑ m ∈ range 9, ((8).choose m : ℂ) * (-w) ^ m * (t : ℂ) ^ m := by
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

/-- The eight binomial coefficients, as closed numerals: `norm_num` evaluates
`C(8,0)` and `C(8,1)` through its `simp` set but leaves `C(8,m)` for `m ≥ 2`
un-reduced, which then blocks `ring`. -/
theorem sum_closed (w : ℂ) :
    (∑ m ∈ range 9, ((8).choose m : ℂ) * (-w) ^ m / ((m : ℂ) + 1))
      = 1 - 4*w + (28/3)*w^2 - 14*w^3 + 14*w^4 - (28/3)*w^5 + 4*w^6 - w^7 + w^8/9 := by
  have c0 : ((8:ℕ).choose 0 : ℂ) = 1 := by rw [show (8:ℕ).choose 0 = 1 by decide]; norm_num
  have c1 : ((8:ℕ).choose 1 : ℂ) = 8 := by rw [show (8:ℕ).choose 1 = 8 by decide]; norm_num
  have c2 : ((8:ℕ).choose 2 : ℂ) = 28 := by rw [show (8:ℕ).choose 2 = 28 by decide]; norm_num
  have c3 : ((8:ℕ).choose 3 : ℂ) = 56 := by rw [show (8:ℕ).choose 3 = 56 by decide]; norm_num
  have c4 : ((8:ℕ).choose 4 : ℂ) = 70 := by rw [show (8:ℕ).choose 4 = 70 by decide]; norm_num
  have c5 : ((8:ℕ).choose 5 : ℂ) = 56 := by rw [show (8:ℕ).choose 5 = 56 by decide]; norm_num
  have c6 : ((8:ℕ).choose 6 : ℂ) = 28 := by rw [show (8:ℕ).choose 6 = 28 by decide]; norm_num
  have c7 : ((8:ℕ).choose 7 : ℂ) = 8 := by rw [show (8:ℕ).choose 7 = 8 by decide]; norm_num
  have c8 : ((8:ℕ).choose 8 : ℂ) = 1 := by rw [show (8:ℕ).choose 8 = 1 by decide]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5, c6, c7, c8]
  push_cast
  ring

/-- **The separation constant.**  A Grace–Walsh–Szegő point whose degree-eight integral
vanishes is farther than `681/1000` from the origin.

This is where `2 sin(π/9)` enters the paper; here it enters as the largest root of
`t³ - 3t + 1`. -/
theorem norm_gt_of_integral_zero {w : ℂ}
    (h : (∫ t in (0:ℝ)..1, (1 - (t : ℂ) * w) ^ 8) = 0) :
    (681/1000 : ℝ) < ‖w‖ := by
  rw [integral_one_sub_pow, sum_closed] at h
  have hw0 : w ≠ 0 := by
    intro hw
    rw [hw] at h
    norm_num at h
  -- `9w·(the sum) = 1 - (1-w)⁹`, because `9·C(8,m)/(m+1) = C(9,m+1)`
  have h9 : (1 - w) ^ 9 = 1 := by linear_combination (-9*w) * h
  have hne : (1 - w) ≠ 1 := by
    intro hh
    exact hw0 (by linear_combination -hh)
  have hb := norm_one_sub_gt h9 hne
  simpa using hb

end Sendov9.RootUnity

#print axioms Sendov9.RootUnity.norm_one_sub_gt
#print axioms Sendov9.RootUnity.integral_t_pow
#print axioms Sendov9.RootUnity.integral_one_sub_pow
#print axioms Sendov9.RootUnity.sum_closed
#print axioms Sendov9.RootUnity.norm_gt_of_integral_zero
