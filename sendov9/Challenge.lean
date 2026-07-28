/-
TRUSTED CHALLENGE FILE — the statements, without proofs.

This file is the audit surface. Comparator (github.com/leanprover/comparator) checks that
the corresponding declarations in `Solution.lean` prove EXACTLY these statements, using no
axioms beyond the permitted list in `comparator/*.json`:
  • `sendov_degree_nine`         — [propext, Quot.sound, Classical.choice]  (axiom-free).
  • `sendov_degree_nine_general` — [propext, Quot.sound, Classical.choice]  (axiom-free).

The `sorry`s below are deliberate and are the only `sorry`s in this directory.

IMPORT CLOSURE: **Mathlib only.**

The other solutions in this repository carry a `Statement.lean` holding the definitions
their statements rest on; Sendov's conjecture needs none. Every notion below is
Mathlib's own — `Polynomial.roots` (the multiset of zeros with multiplicity),
`Polynomial.derivative`, `Polynomial.natDegree`, and the norm on `ℂ`. So the trusted
surface is this file and Mathlib, with no project-specific definitions to audit at all.
That is why there is no `definition_names` entry in `comparator/all.json`.

WHAT EACH STATEMENT SAYS, in words:

  sendov_degree_nine          Let `p` be a MONIC complex polynomial of degree nine, all of
                              whose zeros lie in the closed unit disk. Then for every zero
                              `a` of `p`, some zero `z` of `p'` satisfies `‖a - z‖ ≤ 1`.

  sendov_degree_nine_general  The same without the monic normalization: for every complex
                              polynomial of degree nine with all zeros in the closed unit
                              disk, and every zero `a`, some critical point lies within
                              distance one of `a`. This is the form Sendov's conjecture is
                              usually quoted in, and it is the headline result.

Degree nine was open. Brown–Xiang settled `n ≤ 8` (1999); Tao settled all sufficiently
large `n` (2020); the only prior degree-nine claim is Meng, arXiv:1705.07235, unpublished
since 2018 and publicly doubted. The mathematics formalized here is Anton Shakov's
(`paper/sendov9.tex`); the contribution of this directory is the machine-checked
verification.
-/
import Mathlib
set_option autoImplicit false

namespace Sendov9.Statement

open Polynomial

/-- **Sendov's conjecture in degree nine (monic form).** -/
theorem sendov_degree_nine {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1 := by
  sorry

/-- **Sendov's conjecture in degree nine.** -/
theorem sendov_degree_nine_general {p : ℂ[X]} (hdeg : p.natDegree = 9)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1 := by
  sorry

end Sendov9.Statement
