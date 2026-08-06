import Mathlib
import SendovNData

set_option maxHeartbeats 4000000

/-!
# P2: `CoreN` — the derived quantities `Y, D, μ, u, η, r, σ` at general degree `n`

Port of `Sendov9/Core.lean` + `Sendov9/CoreProd.lean` + the two `RowPrep.lean`
bookkeeping bridges (`r_le`, `sigma_eq`), all parametric in `n ≥ 2` over `Fin (n-1)`,
attached directly to `SendovN.DataN` (no `Counterexample` middleman).

`centered_variance` is inlined verbatim from `Sendov9to11.lean` (the playground package
cannot import the sendov9-11 package); `localization_pointwise` is the degree-9 proof,
which was already degree-free.

Deviation: the centred deviations are named `dev` (not `D` as in the degree-9 file)
because `D` is the canonical `DataN` variable name here.
-/

namespace SendovN

open Finset

/-- `x ^ (-2 : ℤ) = 1 / x ^ 2`. -/
theorem zpow_neg_two (x : ℝ) : x ^ (-2 : ℤ) = 1 / x ^ 2 := by
  rw [zpow_neg, one_div]
  norm_cast

/-- **Paper eq. (variance)** (inlined verbatim from `Sendov9to11.lean`).  If `μ` is the
mean of `Y₁,…,Y_N`, then `D_j = Y_j - μ` satisfy `∑ |D_j|² = ∑ |Y_j|² - N|μ|²`. -/
theorem centered_variance {N : ℕ} (Y : Fin N → ℂ) (μ : ℂ)
    (hμ : ∑ j, Y j = (N : ℂ) * μ) :
    ∑ j, ‖Y j - μ‖ ^ 2 = (∑ j, ‖Y j‖ ^ 2) - (N : ℝ) * ‖μ‖ ^ 2 := by
  have hnorm : ∀ w : ℂ, ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := fun w => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hre : ∑ j, (Y j).re = (N : ℝ) * μ.re := by
    have h := congrArg Complex.re hμ
    simpa using h
  have him : ∑ j, (Y j).im = (N : ℝ) * μ.im := by
    have h := congrArg Complex.im hμ
    simpa using h
  have key : ∀ j : Fin N, ‖Y j - μ‖ ^ 2
      = ‖Y j‖ ^ 2 - 2 * (μ.re * (Y j).re + μ.im * (Y j).im) + ‖μ‖ ^ 2 := by
    intro j
    rw [hnorm, hnorm, hnorm]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  calc ∑ j, ‖Y j - μ‖ ^ 2
      = ∑ j : Fin N, (‖Y j‖ ^ 2
          - 2 * (μ.re * (Y j).re + μ.im * (Y j).im) + ‖μ‖ ^ 2) :=
        Finset.sum_congr rfl fun j _ => key j
    _ = (∑ j, ‖Y j‖ ^ 2)
          - (∑ j : Fin N, 2 * (μ.re * (Y j).re + μ.im * (Y j).im))
          + (∑ _j : Fin N, ‖μ‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ j, ‖Y j‖ ^ 2)
          - (2 * μ.re * (∑ j, (Y j).re) + 2 * μ.im * (∑ j, (Y j).im))
          + (N : ℝ) * ‖μ‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        congr 1
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ j, ‖Y j‖ ^ 2) - (N : ℝ) * ‖μ‖ ^ 2 := by
        rw [hre, him, hnorm]
        ring

/-- The localization inequality, pointwise (degree-free; verbatim from
`Sendov9/Core.lean`). -/
theorem localization_pointwise (a : ℝ) (w : ℂ) (hw : w ≠ 0)
    (hz : Complex.normSq ((a : ℂ) - w) ≤ 1) :
    1 ≤ 2 * a * (w⁻¹).re + (1 - a ^ 2) * Complex.normSq w⁻¹ := by
  have hN : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have hexp : Complex.normSq ((a : ℂ) - w)
      = a ^ 2 - 2 * a * w.re + Complex.normSq w := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have key : Complex.normSq w ≤ 2 * a * w.re + 1 - a ^ 2 := by
    rw [hexp] at hz; linarith
  have hrw : 2 * a * (w.re / Complex.normSq w) + (1 - a ^ 2) * (Complex.normSq w)⁻¹
      = (2 * a * w.re + 1 - a ^ 2) / Complex.normSq w := by
    field_simp; ring
  rw [Complex.inv_re, Complex.normSq_inv, hrw, le_div_iff₀ hN]
  linarith

namespace DataN

variable {n : ℕ} (D : DataN n)

/-- `rₖ = ‖a − zₖ‖`. -/
noncomputable def r (k : Fin (n - 1)) : ℝ := ‖(D.a : ℂ) - D.z k‖

/-- `σ = ∑ₖ rₖ⁻²`. -/
noncomputable def sigma : ℝ := ∑ k, (D.r k) ^ (-2 : ℤ)

/-- `μ`, the mean of the reciprocal critical-point distances. -/
noncomputable def mu : ℂ := (∑ j, ((D.a : ℂ) - D.zeta j)⁻¹) / (n - 1 : ℕ)

/-- `u = Re μ`. -/
noncomputable def u : ℝ := D.mu.re

/-- `Yⱼ = (a − ζⱼ)⁻¹`. -/
noncomputable def Y (j : Fin (n - 1)) : ℂ := ((D.a : ℂ) - D.zeta j)⁻¹

/-- `Dⱼ = Yⱼ − μ`, the centred deviations (named `dev`, since `D` is the data). -/
noncomputable def dev (j : Fin (n - 1)) : ℂ := D.Y j - D.mu

/-- `η = √(1 − |μ|²)`. -/
noncomputable def eta : ℝ := Real.sqrt (1 - Complex.normSq D.mu)

include D in
/-- `n − 1 ≥ 1`, cast-friendly. -/
theorem Npos : 0 < n - 1 := by have := D.hn; omega

include D in
/-- `univ : Finset (Fin (n-1))` is nonempty. -/
theorem univ_nonempty' : (Finset.univ : Finset (Fin (n - 1))).Nonempty :=
  ⟨⟨0, D.Npos⟩, Finset.mem_univ _⟩

include D in
theorem NC_ne : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := D.hn; omega)

include D in
theorem NR_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast D.Npos

/-! ### Basic facts about `Y`, `μ`, `D` -/

theorem norm_Y_lt_one (j : Fin (n - 1)) : ‖D.Y j‖ < 1 := by
  unfold Y
  rw [norm_inv, inv_lt_one_iff₀]
  right; exact D.hzeta j

theorem sum_Y : ∑ j, D.Y j = ((n - 1 : ℕ) : ℂ) * D.mu := by
  have hNC := D.NC_ne
  unfold mu Y
  field_simp

theorem mu_norm_lt_one : ‖D.mu‖ < 1 := by
  have hsum : ‖∑ j, D.Y j‖ < ((n - 1 : ℕ) : ℝ) := by
    calc ‖∑ j, D.Y j‖ ≤ ∑ j, ‖D.Y j‖ := norm_sum_le _ _
      _ < ∑ _j : Fin (n - 1), (1 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty D.univ_nonempty' fun j _ => D.norm_Y_lt_one j
      _ = ((n - 1 : ℕ) : ℝ) := by simp
  rw [D.sum_Y, norm_mul, Complex.norm_natCast] at hsum
  exact (mul_lt_iff_lt_one_right D.NR_pos).mp hsum

/-- The centred deviations sum to zero. -/
theorem sum_dev_zero : ∑ j, D.dev j = 0 := by
  unfold dev
  rw [Finset.sum_sub_distrib, D.sum_Y]
  simp

/-! ### The width `η` -/

theorem normSq_mu_lt_one : Complex.normSq D.mu < 1 := by
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [D.mu_norm_lt_one, norm_nonneg D.mu]

theorem eta_nonneg : 0 ≤ D.eta := Real.sqrt_nonneg _

theorem eta_sq : D.eta ^ 2 = 1 - Complex.normSq D.mu :=
  Real.sq_sqrt (by linarith [D.normSq_mu_lt_one])

/-- `η² ≤ 1 - u²`, since `|μ|² ≥ (Re μ)²`. -/
theorem eta_sq_le_one_sub_u_sq : D.eta ^ 2 ≤ 1 - D.u ^ 2 := by
  rw [D.eta_sq]
  have h : D.u ^ 2 ≤ Complex.normSq D.mu := by
    rw [Complex.normSq_apply]
    unfold u
    nlinarith [sq_nonneg D.mu.im]
  linarith

/-- **The variance bound.**  `∑ⱼ ‖Dⱼ‖² ≤ (n-1)·η²`: the `Yⱼ` sit in the closed unit
disk, so their spread about their own mean is at most `1 − |μ|²`. -/
theorem sum_normSq_dev_le : ∑ j, ‖D.dev j‖ ^ 2 ≤ ((n - 1 : ℕ) : ℝ) * D.eta ^ 2 := by
  have hvar := centered_variance D.Y D.mu D.sum_Y
  have hYle : ∑ j, ‖D.Y j‖ ^ 2 ≤ ((n - 1 : ℕ) : ℝ) := by
    calc ∑ j, ‖D.Y j‖ ^ 2 ≤ ∑ _j : Fin (n - 1), (1 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          nlinarith [D.norm_Y_lt_one j, norm_nonneg (D.Y j)]
      _ = ((n - 1 : ℕ) : ℝ) := by simp
  have heta : D.eta ^ 2 = 1 - ‖D.mu‖ ^ 2 := by
    rw [D.eta_sq, Complex.normSq_eq_norm_sq]
  have hexp : ((n - 1 : ℕ) : ℝ) * D.eta ^ 2
      = ((n - 1 : ℕ) : ℝ) - ((n - 1 : ℕ) : ℝ) * ‖D.mu‖ ^ 2 := by
    rw [heta]; ring
  unfold dev
  rw [hvar, hexp]
  linarith

/-! ### The zeros: `a ≠ zₖ`, `∏ rₖ > n`, `rₖ ≤ a + 1`, `σ` bridge -/

theorem sub_z_ne_zero (k : Fin (n - 1)) : (D.a : ℂ) - D.z k ≠ 0 := by
  intro h
  have h0 : ∏ k, ((D.a : ℂ) - D.z k) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h
  rw [← D.hprod] at h0
  have h1 : ∏ j, ((D.a : ℂ) - D.zeta j) = 0 := by
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact absurd (Nat.cast_eq_zero.mp h') (by have := D.hn; omega)
    · exact h'
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp h1
  have hzj := D.hzeta j
  rw [hj, norm_zero] at hzj
  linarith

theorem r_pos (k : Fin (n - 1)) : 0 < D.r k :=
  norm_pos_iff.mpr (D.sub_z_ne_zero k)

/-- **`∏ₖ rₖ > n`.**  Norms of `hprod`, with every `‖a − ζⱼ‖ > 1`. -/
theorem prod_r_gt_n : (n : ℝ) < ∏ k, D.r k := by
  have h1 : ∏ k, D.r k = ‖∏ k, ((D.a : ℂ) - D.z k)‖ := by
    rw [Complex.norm_prod]
    rfl
  have hgt : (1 : ℝ) < ∏ j, ‖(D.a : ℂ) - D.zeta j‖ := by
    calc (1 : ℝ) = ∏ _j : Fin (n - 1), (1 : ℝ) := by simp
      _ < ∏ j, ‖(D.a : ℂ) - D.zeta j‖ :=
          Finset.prod_lt_prod_of_nonempty (fun j _ => zero_lt_one)
            (fun j _ => D.hzeta j) D.univ_nonempty'
  rw [h1, ← D.hprod, norm_mul, Complex.norm_prod, Complex.norm_natCast]
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h0 : 0 < n := by have := D.hn; omega
    exact_mod_cast h0
  have hmul := mul_lt_mul_of_pos_left hgt hnpos
  rw [mul_one] at hmul
  exact hmul

/-- `rₖ ≤ a + 1`, from the triangle inequality and `‖zₖ‖ ≤ 1`. -/
theorem r_le (k : Fin (n - 1)) : D.r k ≤ D.a + 1 := by
  have h := norm_sub_le ((D.a : ℝ) : ℂ) (D.z k)
  have hre : ‖((D.a : ℝ) : ℂ)‖ = D.a := by
    rw [Complex.norm_real, Real.norm_of_nonneg D.ha0]
  rw [hre] at h
  have := D.hz k
  calc D.r k = ‖(D.a : ℂ) - D.z k‖ := rfl
    _ ≤ D.a + ‖D.z k‖ := h
    _ ≤ D.a + 1 := by linarith

/-- `σ` in the form the `SigmaRows` instances prove a bound for. -/
theorem sigma_eq : D.sigma = ∑ k, 1 / (D.r k) ^ 2 := by
  show ∑ k, (D.r k) ^ (-2 : ℤ) = _
  exact Finset.sum_congr rfl fun k _ => zpow_neg_two (D.r k)

/-! ### The localization inequality and `a = 1` -/

/-- **Localization.**  `(n-1) ≤ (n-1)·a·u + (1 − a²)·σ`. -/
theorem localization :
    ((n - 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) * D.a * D.u + (1 - D.a ^ 2) * D.sigma := by
  have hpt : ∀ k, 1 ≤ 2 * D.a * ((((D.a : ℂ) - D.z k))⁻¹).re
      + (1 - D.a ^ 2) * Complex.normSq (((D.a : ℂ) - D.z k))⁻¹ := by
    intro k
    refine localization_pointwise D.a _ (D.sub_z_ne_zero k) ?_
    have hid : (D.a : ℂ) - ((D.a : ℂ) - D.z k) = D.z k := by ring
    rw [hid, Complex.normSq_eq_norm_sq]
    nlinarith [D.hz k, norm_nonneg (D.z k)]
  have hsummed : ((n - 1 : ℕ) : ℝ) ≤ 2 * D.a * (∑ k, ((((D.a : ℂ) - D.z k))⁻¹).re)
      + (1 - D.a ^ 2) * ∑ k, Complex.normSq (((D.a : ℂ) - D.z k))⁻¹ := by
    rw [Finset.mul_sum, Finset.mul_sum]
    have hN : ((n - 1 : ℕ) : ℝ) = ∑ _k : Fin (n - 1), (1 : ℝ) := by simp
    rw [hN, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => hpt k
  have h2 : ((n - 1 : ℕ) : ℂ) * D.mu = 2 * ∑ k, (((D.a : ℂ) - D.z k))⁻¹ := by
    unfold mu
    rw [mul_comm, div_mul_cancel₀ _ D.NC_ne]
    exact D.hsum
  have hre : ∑ k, ((((D.a : ℂ) - D.z k))⁻¹).re = ((n - 1 : ℕ) : ℝ) * D.u / 2 := by
    have h := congrArg Complex.re h2
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.re_sum, Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero,
      sub_zero] at h
    unfold u
    linarith
  have hnsq : ∑ k, Complex.normSq (((D.a : ℂ) - D.z k))⁻¹ = D.sigma := by
    unfold sigma
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.normSq_inv, Complex.normSq_eq_norm_sq, zpow_neg_two, one_div]
    rfl
  rw [hre, hnsq] at hsummed
  linarith

/-- **`a = 1` is excluded outright**: localization degenerates to `u ≥ 1`,
against `‖μ‖ < 1`. -/
theorem one_excluded (ha : D.a = 1) : False := by
  have hloc := D.localization
  rw [ha] at hloc
  norm_num at hloc
  have hu : D.u < 1 := lt_of_le_of_lt (Complex.re_le_norm D.mu) D.mu_norm_lt_one
  nlinarith [D.NR_pos]

end DataN

end SendovN

#print axioms SendovN.centered_variance
#print axioms SendovN.localization_pointwise
#print axioms SendovN.DataN.norm_Y_lt_one
#print axioms SendovN.DataN.sum_Y
#print axioms SendovN.DataN.mu_norm_lt_one
#print axioms SendovN.DataN.sum_dev_zero
#print axioms SendovN.DataN.eta_sq
#print axioms SendovN.DataN.eta_sq_le_one_sub_u_sq
#print axioms SendovN.DataN.sum_normSq_dev_le
#print axioms SendovN.DataN.sub_z_ne_zero
#print axioms SendovN.DataN.r_pos
#print axioms SendovN.DataN.prod_r_gt_n
#print axioms SendovN.DataN.r_le
#print axioms SendovN.DataN.sigma_eq
#print axioms SendovN.DataN.localization
#print axioms SendovN.DataN.one_excluded
