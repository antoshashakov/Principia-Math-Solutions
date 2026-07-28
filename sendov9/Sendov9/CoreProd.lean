import Mathlib
import Sendov9.Core

set_option maxHeartbeats 4000000

namespace Sendov9.CoreProd

open Finset

/-!
# `∏ₖ rₖ > 9`, attached to the canonical `Counterexample`

`Instantiate.lean` proves this, but against its own copy of `Counterexample`, so it
cannot be co-imported with `Core` (which came from `Instantiate2.lean` and already owns
`sub_z_ne_zero`, `localization`, and the rest).  Rather than transplant the whole file a
second time — the overlap with `Core` is about a dozen names — only the two declarations
that are actually missing are copied here, verbatim.

`prod_r_gt_nine` is the second of the two hypotheses every row of the middle range
carries.  With it discharged, the only input left standing between `MidRows.mid_excluded`
and an unconditional theorem is the separation bound `rₖ > m₀`, which is exactly where
Grace–Walsh–Szegő enters.

Sendov's conjecture in degree nine remains unproven.
-/

/-- Copied verbatim from `Instantiate.lean`. -/
theorem r_pos (C : Counterexample) (k : Fin 8) : 0 < C.r k :=
  norm_pos_iff.mpr (sub_z_ne_zero C k)

/-- **`∏ₖ rₖ > 9`.**  Norms of `hprod`, with every `‖a - ζⱼ‖ > 1`.  Copied verbatim from
`Instantiate.lean`, where it is proved against the other copy of the structure. -/
theorem prod_r_gt_nine (C : Counterexample) : 9 < ∏ k, C.r k := by
  have h1 : ∏ k, C.r k = ‖∏ k, ((C.a : ℂ) - C.z k)‖ := by
    rw [Complex.norm_prod]
    rfl
  have hgt : (1 : ℝ) < ∏ j, ‖(C.a : ℂ) - C.zeta j‖ := by
    calc (1 : ℝ) = ∏ _j : Fin 8, (1 : ℝ) := by simp
      _ < ∏ j, ‖(C.a : ℂ) - C.zeta j‖ :=
          Finset.prod_lt_prod_of_nonempty (fun j _ => zero_lt_one)
            (fun j _ => C.hzeta j) ⟨0, Finset.mem_univ 0⟩
  rw [h1, ← C.hprod, norm_mul, Complex.norm_prod]
  have h9 : ‖(9 : ℂ)‖ = 9 := by norm_num
  rw [h9]
  linarith

end Sendov9.CoreProd

#print axioms Sendov9.CoreProd.r_pos
#print axioms Sendov9.CoreProd.prod_r_gt_nine
