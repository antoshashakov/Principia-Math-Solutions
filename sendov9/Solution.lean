/-
SOLUTION FILE — the same two statements as `Challenge.lean`, proved.

Each proof is a direct term assignment from the development (`Sendov9.Final`). A term
assignment forces Lean to check that the development's statement and the trusted statement
in `Challenge.lean` are DEFINITIONALLY EQUAL. Since both are phrased purely in Mathlib's
own vocabulary (`Polynomial.roots`, `Polynomial.derivative`, `Polynomial.natDegree`, the
norm on `ℂ`), they are in fact syntactically identical up to binder names: there is no
transport lemma doing hidden work, and no project-specific definition standing between the
statement and its meaning.

The `#print axioms` lines are a redundant local audit; Comparator performs the
authoritative check of the footprints against `Challenge.lean`. Expected footprints:
  • sendov_degree_nine         : [propext, Classical.choice, Quot.sound]
  • sendov_degree_nine_general : [propext, Classical.choice, Quot.sound]
-/
import Sendov9
set_option autoImplicit false

namespace Sendov9.Statement

open Polynomial

/-- **Sendov's conjecture in degree nine (monic form).** -/
theorem sendov_degree_nine {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1 :=
  _root_.Sendov9.Final.sendov_degree_nine hm hdeg hroots ha

/-- **Sendov's conjecture in degree nine.** -/
theorem sendov_degree_nine_general {p : ℂ[X]} (hdeg : p.natDegree = 9)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1 :=
  _root_.Sendov9.Final.sendov_degree_nine_general hdeg hroots ha

#print axioms sendov_degree_nine
#print axioms sendov_degree_nine_general

end Sendov9.Statement
