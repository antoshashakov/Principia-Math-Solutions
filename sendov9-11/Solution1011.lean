/-
SOLUTION FILE (degrees ten and eleven) — the four degree-10/11 statements of
`Challenge.lean`, proved.

Companion to `Solution.lean`, which holds the two degree-nine statements. Together the two
files prove all six statements of the single trusted `Challenge.lean`; the repository
already ships more than one solution module per solution folder where that is the right
shape (`erdos1054/` has three, one bridge per master — see the root README's
"Conventions" section).

WHY THE SPLIT. `Solution.lean`'s import closure is the 46-module `Sendov9` library and
nothing else, so degree nine is cheap to build and to compare. THIS file imports
`SendovNStatement`, whose import closure is the ENTIRE degrees-10/11 development: the
parametric `SendovN` core, the generated assembly layer, and all 582 kernel-`decide` box
certificates in `boxes10/` and `boxes11v2/` (~10 CPU-hours). Keeping the two in one file
would force every consumer of the degree-nine statements — including the fast CI job on
every push — to pay that cost. The boundary is one of build cost only: the statements
themselves are unchanged, in the same namespace, with the same direct term assignments.

Each proof is a direct term assignment from the development (`SendovN.Final10` /
`SendovN.Final11`, i.e. `Sendov1011/SendovNStatement.lean`). A term assignment forces Lean
to check that the development's statement and the trusted statement in `Challenge.lean`
are DEFINITIONALLY EQUAL. Both are phrased purely in Mathlib's own vocabulary
(`Polynomial.roots`, `Polynomial.derivative`, `Polynomial.natDegree`, the norm on `ℂ`), so
they are in fact syntactically identical up to binder names: there is no transport lemma
doing hidden work, and no project-specific definition standing between the statement and
its meaning.

Comparator configs: `comparator/sendov10.json`, `comparator/sendov11.json`,
`comparator/all1011.json` (all three name `Solution1011` as `solution_module` and the same
shared `Challenge` as `challenge_module`).

CI: building this module builds the whole 582-box corpus, so it is NOT part of the fast
per-push job. It is built by `.github/workflows/sendov1011-full.yml`
(`workflow_dispatch` only); the certificates themselves are re-checked one file at a time
by the sharded `.github/workflows/sendov1011-boxes.yml`.

The `#print axioms` lines are a redundant local audit; Comparator performs the
authoritative check of the footprints against `Challenge.lean`. Expected footprints (all
four): [propext, Classical.choice, Quot.sound].
-/
import SendovNStatement
set_option autoImplicit false

namespace Sendov1011.Statement

open Polynomial

/-- **Sendov's conjecture in degree ten (monic form).** -/
theorem sendov_degree_ten {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 10)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1 :=
  _root_.SendovN.Final10.sendov_degree_ten hm hdeg hroots ha

/-- **Sendov's conjecture in degree ten.** -/
theorem sendov_degree_ten_general {p : ℂ[X]} (hdeg : p.natDegree = 10)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1 :=
  _root_.SendovN.Final10.sendov_degree_ten_general hdeg hroots ha

/-- **Sendov's conjecture in degree eleven (monic form).** -/
theorem sendov_degree_eleven {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 11)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1 :=
  _root_.SendovN.Final11.sendov_degree_eleven hm hdeg hroots ha

/-- **Sendov's conjecture in degree eleven.** -/
theorem sendov_degree_eleven_general {p : ℂ[X]} (hdeg : p.natDegree = 11)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1 :=
  _root_.SendovN.Final11.sendov_degree_eleven_general hdeg hroots ha

#print axioms sendov_degree_ten
#print axioms sendov_degree_ten_general
#print axioms sendov_degree_eleven
#print axioms sendov_degree_eleven_general

end Sendov1011.Statement
