import Mathlib
import Sendov9.Data

set_option maxHeartbeats 4000000

namespace Sendov9

open Finset

/-!
## Provenance

**This file is `Instantiate2.lean` with its local `structure Counterexample` deleted and
`import Sendov9.Data` added — nothing else changed.**  It is produced mechanically, so
that the derivations below attach to the *canonical* `Sendov9.Counterexample`, the one
`Data.toCounterexample` actually produces from a polynomial.

The reason it has to exist: `Data.lean` and `Instantiate2.lean` each declare their own
`Sendov9.Counterexample` with identical fields (both files were written to gate
standalone, before the lake library).  Identical or not, two declarations of the same
name cannot be co-imported, so the endgame needs exactly one of them — and it must be
`Data`'s, since that is the end of the polynomial bridge.

Everything below is byte-identical to `Instantiate2.lean`, which gates independently;
that is what makes this a re-attachment rather than a re-proof.
-/

/-!
# Stage 3, part 2: the centred deviations `Dⱼ` and the width `η`

`Instantiate.lean` derived `a ≠ zₖ`, `∏rₖ > 9`, `‖μ‖ < 1` and the localization
inequality from the `Counterexample` structure.  Both remaining ranges then need one
more layer: the critical-point data `Yⱼ = (a - ζⱼ)⁻¹`, its centring `Dⱼ = Yⱼ - μ`, and
the width `η = √(1 - |μ|²)` — the quantity every `eₘ` bound in `EmBounds.lean` and
every Bernstein certificate is stated against.

The one fact that makes the whole `eₘ` chain work is `sum_normSq_D_le`: the eight `Yⱼ`
lie in the closed unit disk, so their variance about their own mean is at most
`1 - |μ|²`.  That is `8η²`, which is exactly the hypothesis shape `EmBounds.e3_bound`
and `EmBounds.e4_bound` consume.

`one_excluded` finishes `a = 1` outright at the structure level, with no separation
bound and hence **no Grace–Walsh–Szegő**: at `a = 1` localization degenerates to
`u ≥ 1`, against `‖μ‖ < 1`.
-/

namespace Counterexample

variable (C : Counterexample)

noncomputable def r (k : Fin 8) : ℝ := ‖(C.a : ℂ) - C.z k‖
noncomputable def sigma : ℝ := ∑ k, (C.r k) ^ (-2 : ℤ)
noncomputable def mu : ℂ := (∑ j, ((C.a : ℂ) - C.zeta j)⁻¹) / 8
noncomputable def u : ℝ := C.mu.re

/-- `Yⱼ = (a - ζⱼ)⁻¹`, the reciprocals of the critical-point distances. -/
noncomputable def Y (j : Fin 8) : ℂ := ((C.a : ℂ) - C.zeta j)⁻¹

/-- `Dⱼ = Yⱼ - μ`, the centred deviations. -/
noncomputable def D (j : Fin 8) : ℂ := C.Y j - C.mu

/-- `η = √(1 - |μ|²)`, the width the `eₘ` bounds are stated against. -/
noncomputable def eta : ℝ := Real.sqrt (1 - Complex.normSq C.mu)

end Counterexample

/-- `x ^ (-2 : ℤ) = 1 / x ^ 2` (restated from `Connect.lean`). -/
theorem zpow_neg_two (x : ℝ) : x ^ (-2 : ℤ) = 1 / x ^ 2 := by
  rw [zpow_neg, one_div]
  norm_cast

/-! ### Basic facts about `Y`, `μ`, `D` -/

theorem norm_Y_lt_one (C : Counterexample) (j : Fin 8) : ‖C.Y j‖ < 1 := by
  unfold Counterexample.Y
  rw [norm_inv, inv_lt_one_iff₀]
  right; exact C.hzeta j

theorem sum_Y (C : Counterexample) : ∑ j, C.Y j = 8 * C.mu := by
  unfold Counterexample.mu Counterexample.Y
  field_simp

theorem mu_norm_lt_one (C : Counterexample) : ‖C.mu‖ < 1 := by
  have hsum : ‖∑ j, C.Y j‖ < 8 := by
    calc ‖∑ j, C.Y j‖ ≤ ∑ j, ‖C.Y j‖ := norm_sum_le _ _
      _ < ∑ _j : Fin 8, (1 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun j _ => norm_Y_lt_one C j
      _ = 8 := by simp
  rw [sum_Y C, norm_mul] at hsum
  have h8 : ‖(8 : ℂ)‖ = 8 := by norm_num
  rw [h8] at hsum
  linarith

/-- The centred deviations sum to zero — the hypothesis every `eₘ` bound needs. -/
theorem sum_D_zero (C : Counterexample) : ∑ j, C.D j = 0 := by
  unfold Counterexample.D
  rw [Finset.sum_sub_distrib, sum_Y C]
  simp

/-! ### The width `η` -/

theorem normSq_mu_lt_one (C : Counterexample) : Complex.normSq C.mu < 1 := by
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [mu_norm_lt_one C, norm_nonneg C.mu]

theorem eta_nonneg (C : Counterexample) : 0 ≤ C.eta := Real.sqrt_nonneg _

theorem eta_sq (C : Counterexample) : C.eta ^ 2 = 1 - Complex.normSq C.mu :=
  Real.sq_sqrt (by linarith [normSq_mu_lt_one C])

/-- `η² ≤ 1 - u²`, since `|μ|² ≥ (Re μ)²`.  Step 3a of the boundary range wants this. -/
theorem eta_sq_le_one_sub_u_sq (C : Counterexample) : C.eta ^ 2 ≤ 1 - C.u ^ 2 := by
  rw [eta_sq C]
  have h : C.u ^ 2 ≤ Complex.normSq C.mu := by
    rw [Complex.normSq_apply]
    unfold Counterexample.u
    nlinarith [sq_nonneg C.mu.im]
  linarith

/-- **The variance bound.**  `∑ⱼ ‖Dⱼ‖² ≤ 8η²` — the eight `Yⱼ` sit in the closed unit
disk, so their spread about their own mean is at most `1 - |μ|²`.  This is exactly the
hypothesis `EmBounds.e3_bound` / `EmBounds.e4_bound` consume. -/
theorem sum_normSq_D_le (C : Counterexample) : ∑ j, ‖C.D j‖ ^ 2 ≤ 8 * C.eta ^ 2 := by
  have hre : ∑ j, (C.Y j).re = 8 * C.mu.re := by
    have := congrArg Complex.re (sum_Y C)
    simpa [Complex.re_sum, Complex.mul_re] using this
  have him : ∑ j, (C.Y j).im = 8 * C.mu.im := by
    have := congrArg Complex.im (sum_Y C)
    simpa [Complex.im_sum, Complex.mul_im] using this
  -- the variance identity, expanded coordinatewise
  have hvar : ∑ j, Complex.normSq (C.Y j - C.mu)
      = (∑ j, Complex.normSq (C.Y j)) - 8 * Complex.normSq C.mu := by
    have hexp : ∀ j, Complex.normSq (C.Y j - C.mu)
        = Complex.normSq (C.Y j)
          - 2 * ((C.Y j).re * C.mu.re + (C.Y j).im * C.mu.im) + Complex.normSq C.mu := by
      intro j
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring
    simp only [hexp]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hcross : ∑ j, 2 * ((C.Y j).re * C.mu.re + (C.Y j).im * C.mu.im)
        = 16 * Complex.normSq C.mu := by
      rw [← Finset.mul_sum]
      have hsplit : ∑ j, ((C.Y j).re * C.mu.re + (C.Y j).im * C.mu.im)
          = (∑ j, (C.Y j).re) * C.mu.re + (∑ j, (C.Y j).im) * C.mu.im := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      rw [hsplit, hre, him, Complex.normSq_apply]
      ring
    rw [hcross]
    simp [Complex.normSq_apply]
    ring
  have hYle : ∑ j, Complex.normSq (C.Y j) ≤ 8 := by
    calc ∑ j, Complex.normSq (C.Y j) ≤ ∑ _j : Fin 8, (1:ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Complex.normSq_eq_norm_sq]
          nlinarith [norm_Y_lt_one C j, norm_nonneg (C.Y j)]
      _ = 8 := by simp
  have hconv : ∑ j, ‖C.D j‖ ^ 2 = ∑ j, Complex.normSq (C.Y j - C.mu) :=
    Finset.sum_congr rfl fun j _ => (Complex.normSq_eq_norm_sq _).symm
  rw [hconv, hvar, eta_sq C]
  linarith

/-! ### `a = 1` -/

/-- Restated from `Instantiate.lean`. -/
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

theorem sub_z_ne_zero (C : Counterexample) (k : Fin 8) : (C.a : ℂ) - C.z k ≠ 0 := by
  intro h
  have h0 : ∏ k, ((C.a : ℂ) - C.z k) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h
  rw [← C.hprod] at h0
  have h1 : ∏ j, ((C.a : ℂ) - C.zeta j) = 0 := by
    rcases mul_eq_zero.mp h0 with h' | h'
    · norm_num at h'
    · exact h'
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp h1
  have hzj := C.hzeta j
  rw [hj, norm_zero] at hzj
  linarith

/-- Restated from `Instantiate.lean`. -/
theorem localization (C : Counterexample) :
    8 ≤ 8 * C.a * C.u + (1 - C.a ^ 2) * C.sigma := by
  set w : Fin 8 → ℂ := fun k => (C.a : ℂ) - C.z k with hwdef
  have hpt : ∀ k, 1 ≤ 2 * C.a * ((w k)⁻¹).re + (1 - C.a ^ 2) * Complex.normSq (w k)⁻¹ := by
    intro k
    refine localization_pointwise C.a (w k) (sub_z_ne_zero C k) ?_
    have hid : (C.a : ℂ) - w k = C.z k := by rw [hwdef]; ring
    rw [hid, Complex.normSq_eq_norm_sq]
    nlinarith [C.hz k, norm_nonneg (C.z k)]
  have hsummed : 8 ≤ 2 * C.a * (∑ k, ((w k)⁻¹).re)
      + (1 - C.a ^ 2) * ∑ k, Complex.normSq (w k)⁻¹ := by
    rw [Finset.mul_sum, Finset.mul_sum]
    have h8 : (8 : ℝ) = ∑ _k : Fin 8, (1 : ℝ) := by simp
    rw [h8, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => hpt k
  have h4 : (4 : ℂ) * C.mu = ∑ k, (w k)⁻¹ := by
    unfold Counterexample.mu
    rw [C.hsum, hwdef]
    ring
  have hre : ∑ k, ((w k)⁻¹).re = 4 * C.u := by
    rw [← Complex.re_sum, ← h4]
    simp [Counterexample.u, Complex.mul_re]
  have hnsq : ∑ k, Complex.normSq (w k)⁻¹ = C.sigma := by
    unfold Counterexample.sigma
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.normSq_inv, Complex.normSq_eq_norm_sq, zpow_neg_two, one_div]
    rfl
  rw [hre, hnsq] at hsummed
  linarith

/-- **`a = 1` is excluded outright.**  No separation bound, hence no
Grace–Walsh–Szegő: localization degenerates to `u ≥ 1`, against `‖μ‖ < 1`. -/
theorem one_excluded (C : Counterexample) (ha : C.a = 1) : False := by
  have hloc := localization C
  rw [ha] at hloc
  norm_num at hloc
  have hu : C.u < 1 := lt_of_le_of_lt (Complex.re_le_norm C.mu) (mu_norm_lt_one C)
  linarith

end Sendov9

#print axioms Sendov9.norm_Y_lt_one
#print axioms Sendov9.sum_Y
#print axioms Sendov9.mu_norm_lt_one
#print axioms Sendov9.sum_D_zero
#print axioms Sendov9.normSq_mu_lt_one
#print axioms Sendov9.eta_nonneg
#print axioms Sendov9.eta_sq
#print axioms Sendov9.eta_sq_le_one_sub_u_sq
#print axioms Sendov9.sum_normSq_D_le
#print axioms Sendov9.localization
#print axioms Sendov9.one_excluded
