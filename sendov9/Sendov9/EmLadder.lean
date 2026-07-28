import Mathlib
import Sendov9.MaclaurinFull

set_option maxHeartbeats 4000000

namespace Sendov9.EmLadder

open Finset

/-!
# The `eₘ` ladder for `m ≥ 5` — the last consumer of the discharged Maclaurin

Equation (2.13) of the paper needs `|eₘ(D)| ≤ cₘ ηᵐ` for `2 ≤ m ≤ 8`, with

    (c₂,…,c₈) = (4, 264/35, 24, 56, 28, 8, 1).

`m = 2,3,4` come from Newton's identities and are already hypothesis-free
(`NewtonWiring.e3_bound'`, `e4_bound'`).  For `m ≥ 5` the constants are exactly the
binomial coefficients `C(8,m) = (56, 28, 8, 1)`, and the paper's route is Maclaurin
applied to `|D₁|,…,|D₈|` followed by Cauchy–Schwarz.

That route is now unconditional, because Maclaurin at `n = 8` is a **theorem** here
(`Mac.maclaurin_eight`, proved by smoothing rather than real-rootedness).  The chain is

    ‖eₘ(D)‖ ≤ eₘ(‖D‖)                             (triangle + `Complex.norm_prod`)
            ≤ C(8,m) · ((∑ⱼ‖Dⱼ‖)/8)ᵐ              (`Mac.maclaurin_eight`)
            ≤ C(8,m) · ηᵐ                          (Cauchy–Schwarz + `∑‖Dⱼ‖² ≤ 8η²`)

The Cauchy–Schwarz step is `sq_sum_le_card_mul_sum_sq`, which lives at the **root**
namespace despite being about `Finset`s (`Mathlib/Algebra/Order/Chebyshev.lean` opens
`Finset` but declares no `namespace Finset`).

Note the bound is proved for **every** `m`, not just `m ≥ 5`: above `m = 8` both sides
are handled by `powersetCard` being empty, and below `m = 5` the statement is true but
weaker than the Newton constants the paper actually uses.

Sendov's conjecture in degree nine remains unproven.
-/

/-- `eₘ` of a complex family — the same definition as `EmBounds.esD` and `Sigma22.esD`. -/
noncomputable def esD (D : Fin 8 → ℂ) (m : ℕ) : ℂ :=
  ∑ s ∈ (univ : Finset (Fin 8)).powersetCard m, ∏ j ∈ s, D j

/-- The triangle inequality, termwise: `‖eₘ(D)‖ ≤ eₘ(‖D‖)`. -/
theorem norm_esD_le (D : Fin 8 → ℂ) (m : ℕ) :
    ‖esD D m‖ ≤ ∑ s ∈ (univ : Finset (Fin 8)).powersetCard m, ∏ j ∈ s, ‖D j‖ := by
  refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
  exact Finset.sum_congr rfl fun s _ => Complex.norm_prod _ _

/-- **Cauchy–Schwarz.**  `∑‖Dⱼ‖² ≤ 8η²` gives `∑‖Dⱼ‖ ≤ 8η`. -/
theorem sum_norm_le (D : Fin 8 → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2) :
    ∑ j, ‖D j‖ ≤ 8 * eta := by
  have hcard : ((univ : Finset (Fin 8)).card : ℝ) = 8 := by simp
  have hcs : (∑ j, ‖D j‖) ^ 2 ≤ ((univ : Finset (Fin 8)).card : ℝ) * ∑ j, ‖D j‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hcard] at hcs
  have hS : 0 ≤ ∑ j, ‖D j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  nlinarith [hS, heta, hcs, hD]

/-- **The ladder.**  `‖eₘ(D)‖ ≤ C(8,m) ηᵐ`, unconditionally in `m`.

At `m = 5,6,7,8` the constants `C(8,m) = 56, 28, 8, 1` are exactly the paper's
`(c₅,…,c₈)`. -/
theorem em_bound (D : Fin 8 → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2) (m : ℕ) :
    ‖esD D m‖ ≤ ((8:ℕ).choose m : ℝ) * eta ^ m := by
  have h1 := norm_esD_le D m
  have h2 := Mac.maclaurin_eight (fun j => ‖D j‖) (fun j => norm_nonneg _) m
  simp only [Mac.E] at h2
  have h3 : ∑ j, ‖D j‖ ≤ 8 * eta := sum_norm_le D eta heta hD
  have hS : 0 ≤ ∑ j, ‖D j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have h4 : ((∑ j, ‖D j‖) / 8) ^ m ≤ eta ^ m := by
    refine pow_le_pow_left₀ (by positivity) ?_ m
    linarith
  have hc : (0:ℝ) ≤ ((8:ℕ).choose m : ℝ) := by positivity
  calc ‖esD D m‖ ≤ ∑ s ∈ (univ : Finset (Fin 8)).powersetCard m, ∏ j ∈ s, ‖D j‖ := h1
    _ ≤ ((8:ℕ).choose m : ℝ) * ((∑ j, ‖D j‖) / 8) ^ m := h2
    _ ≤ ((8:ℕ).choose m : ℝ) * eta ^ m := by
        exact mul_le_mul_of_nonneg_left h4 hc

/-! ### The four constants the paper names -/

theorem e5_bound (D : Fin 8 → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2) : ‖esD D 5‖ ≤ 56 * eta ^ 5 := by
  have := em_bound D eta heta hD 5
  norm_num at this
  exact this

theorem e6_bound (D : Fin 8 → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2) : ‖esD D 6‖ ≤ 28 * eta ^ 6 := by
  have := em_bound D eta heta hD 6
  norm_num at this
  exact this

theorem e7_bound (D : Fin 8 → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2) : ‖esD D 7‖ ≤ 8 * eta ^ 7 := by
  have := em_bound D eta heta hD 7
  norm_num at this
  exact this

theorem e8_bound (D : Fin 8 → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2) : ‖esD D 8‖ ≤ eta ^ 8 := by
  have := em_bound D eta heta hD 8
  norm_num at this
  exact this

end Sendov9.EmLadder

#print axioms Sendov9.EmLadder.norm_esD_le
#print axioms Sendov9.EmLadder.sum_norm_le
#print axioms Sendov9.EmLadder.em_bound
#print axioms Sendov9.EmLadder.e5_bound
#print axioms Sendov9.EmLadder.e6_bound
#print axioms Sendov9.EmLadder.e7_bound
#print axioms Sendov9.EmLadder.e8_bound
