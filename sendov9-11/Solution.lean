/-
SOLUTION FILE (degree nine) — the two degree-nine statements of `Challenge.lean`, proved.

Each proof is a direct term assignment from the development (`Sendov9.Final`). A term
assignment forces Lean to check that the development's statement and the trusted statement
in `Challenge.lean` are DEFINITIONALLY EQUAL. Since both are phrased purely in Mathlib's
own vocabulary (`Polynomial.roots`, `Polynomial.derivative`, `Polynomial.natDegree`, the
norm on `ℂ`), they are in fact syntactically identical up to binder names: there is no
transport lemma doing hidden work, and no project-specific definition standing between the
statement and its meaning.

WHY THIS FILE IS DEGREE NINE ONLY. The four degree-10/11 statements live in
`Solution1011.lean`. They are the same six statements as before, split across two solution
modules exactly as `erdos1054/` ships one bridge module per master (see the root README's
"Conventions" section). The split is a COST boundary, not a mathematical one: the
degree-10/11 statement module `Sendov1011/SendovNStatement.lean` has all 582 box
certificates in its import closure (~10 CPU-hours of kernel `decide`), so a single
`Solution.lean` holding all six forces every consumer — including the fast degree-nine CI
— to pay for the whole degrees-10/11 corpus. With the split, THIS file's import closure is
exactly the 46-module `Sendov9` library and Mathlib, and nothing else.

Comparator configs: `comparator/sendov9_monic.json`, `comparator/sendov9_general.json`,
`comparator/all.json` (all three name `Solution` as `solution_module`); the degree-10/11
configs name `Solution1011`. `Challenge.lean` is shared by both groups — it is
Mathlib-only, so it is cheap for either.

The `#print axioms` lines are a redundant local audit; Comparator performs the
authoritative check of the footprints against `Challenge.lean`. Expected footprints:
[propext, Classical.choice, Quot.sound].
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
