import Mathlib
import SendovNStatement

set_option maxHeartbeats 400000

namespace SendovN.NonVacuous

open Polynomial

/-!
# The degree-10 and degree-11 theorems are not vacuous

The one genuine defect the degree-nine campaign turned up was a statement that was *true
for the wrong reason*: the originally carried `GraceWalshSzego` was vacuous at `n = 0`,
which would have made every dependent theorem trivial without leaving a trace in
`#print axioms` (`GWSFix.not_graceWalshSzego`).  The lesson recorded at the time was to
instantiate every new `Prop` at a concrete witness before depending on it, and
`Sendov9/NonVacuous.lean` applies it to the degree-nine master theorem.

This file is the degrees-10/11 twin.  `p = X¹⁰` is monic of degree ten with every zero in
the closed unit disk (all ten of them at the origin), and likewise `p = X¹¹` in degree
eleven, so the hypotheses of `SendovN.Final10.sendov_degree_ten_general` and
`SendovN.Final11.sendov_degree_eleven_general` are satisfiable and each theorem delivers
an actual critical point.  A theorem with unsatisfiable hypotheses would prove nothing at
all, in exactly the same silent way.
-/

theorem X_pow_ten_roots_norm (w : ℂ) (hw : w ∈ (X ^ 10 : ℂ[X]).roots) : ‖w‖ ≤ 1 := by
  have h := (Polynomial.mem_roots'.mp hw).2
  have hz : w ^ 10 = 0 := by
    simpa [Polynomial.IsRoot] using h
  have hw0 : w = 0 := pow_eq_zero_iff (n := 10) (by norm_num) |>.mp hz
  simp [hw0]

theorem zero_mem_roots_ten : (0 : ℂ) ∈ (X ^ 10 : ℂ[X]).roots := by
  refine Polynomial.mem_roots'.mpr ⟨pow_ne_zero 10 Polynomial.X_ne_zero, ?_⟩
  simp [Polynomial.IsRoot]

theorem X_pow_eleven_roots_norm (w : ℂ) (hw : w ∈ (X ^ 11 : ℂ[X]).roots) : ‖w‖ ≤ 1 := by
  have h := (Polynomial.mem_roots'.mp hw).2
  have hz : w ^ 11 = 0 := by
    simpa [Polynomial.IsRoot] using h
  have hw0 : w = 0 := pow_eq_zero_iff (n := 11) (by norm_num) |>.mp hz
  simp [hw0]

theorem zero_mem_roots_eleven : (0 : ℂ) ∈ (X ^ 11 : ℂ[X]).roots := by
  refine Polynomial.mem_roots'.mpr ⟨pow_ne_zero 11 Polynomial.X_ne_zero, ?_⟩
  simp [Polynomial.IsRoot]

/-- **The degree-ten theorem applied at a concrete polynomial.**  Not vacuous: the
hypotheses are met by `X¹⁰`, and the conclusion is a genuine critical point within
distance one of the zero `0`. -/
theorem sanity10 : ∃ z ∈ (derivative (X ^ 10 : ℂ[X])).roots, ‖(0 : ℂ) - z‖ ≤ 1 :=
  Final10.sendov_degree_ten_general (by simp) X_pow_ten_roots_norm zero_mem_roots_ten

/-- **The degree-eleven theorem applied at a concrete polynomial.**  Not vacuous: the
hypotheses are met by `X¹¹`, and the conclusion is a genuine critical point within
distance one of the zero `0`. -/
theorem sanity11 : ∃ z ∈ (derivative (X ^ 11 : ℂ[X])).roots, ‖(0 : ℂ) - z‖ ≤ 1 :=
  Final11.sendov_degree_eleven_general (by simp) X_pow_eleven_roots_norm
    zero_mem_roots_eleven

end SendovN.NonVacuous

#print axioms SendovN.NonVacuous.X_pow_ten_roots_norm
#print axioms SendovN.NonVacuous.zero_mem_roots_ten
#print axioms SendovN.NonVacuous.X_pow_eleven_roots_norm
#print axioms SendovN.NonVacuous.zero_mem_roots_eleven
#print axioms SendovN.NonVacuous.sanity10
#print axioms SendovN.NonVacuous.sanity11
