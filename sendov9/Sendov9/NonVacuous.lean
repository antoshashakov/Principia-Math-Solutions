import Mathlib
import Sendov9.Final

set_option maxHeartbeats 400000

namespace Sendov9.NonVacuous

open Polynomial

/-!
# The master theorem is not vacuous

The one genuine defect this campaign turned up was a statement that was *true for the
wrong reason*: the originally carried `GraceWalshSzego` was vacuous at `n = 0`, which
would have made every dependent theorem trivial without leaving a trace in
`#print axioms` (`GWSFix.not_graceWalshSzego`).  The lesson recorded at the time was to
instantiate every new `Prop` at a concrete witness before depending on it.

This file applies that lesson to the master theorem itself.  `p = X⁹` is monic of degree
nine with every zero in the closed unit disk (all nine of them at the origin), so the
hypotheses of `Final.sendov_degree_nine_general` are satisfiable and the theorem
delivers an actual critical point.  A theorem with unsatisfiable hypotheses would prove
nothing at all, in exactly the same silent way.
-/

theorem X_pow_nine_roots_norm (w : ℂ) (hw : w ∈ (X ^ 9 : ℂ[X]).roots) : ‖w‖ ≤ 1 := by
  have h := (Polynomial.mem_roots'.mp hw).2
  have hz : w ^ 9 = 0 := by
    simpa [Polynomial.IsRoot] using h
  have hw0 : w = 0 := pow_eq_zero_iff (n := 9) (by norm_num) |>.mp hz
  simp [hw0]

theorem zero_mem_roots : (0 : ℂ) ∈ (X ^ 9 : ℂ[X]).roots := by
  refine Polynomial.mem_roots'.mpr ⟨pow_ne_zero 9 Polynomial.X_ne_zero, ?_⟩
  simp [Polynomial.IsRoot]

/-- **The master theorem applied at a concrete polynomial.**  Not vacuous: the
hypotheses are met by `X⁹`, and the conclusion is a genuine critical point within
distance one of the zero `0`. -/
theorem sanity : ∃ z ∈ (derivative (X ^ 9 : ℂ[X])).roots, ‖(0 : ℂ) - z‖ ≤ 1 :=
  Final.sendov_degree_nine_general (by simp) X_pow_nine_roots_norm zero_mem_roots

end Sendov9.NonVacuous

#print axioms Sendov9.NonVacuous.X_pow_nine_roots_norm
#print axioms Sendov9.NonVacuous.zero_mem_roots
#print axioms Sendov9.NonVacuous.sanity
