/-
TRUSTED CHALLENGE FILE — the statement, without proof.

This file is the audit surface, together with `HRTLambda0/Statement.lean` (the
definitions) and Mathlib. Comparator (github.com/leanprover/comparator) checks that the
corresponding declaration in `Solution.lean` proves EXACTLY this statement, using no
axioms beyond the permitted list in `comparator/all.json`:
  • `lambda0_independent_of_reduction` — [propext, Quot.sound, Classical.choice].

The `sorry` below is deliberate and is the only `sorry` in this directory.

IMPORT CLOSURE: `HRTLambda0.Statement` (definitions only) and Mathlib.

WHAT THE STATEMENT SAYS, in words — read it CAREFULLY, because the honesty of this
solution folder lives in the hypothesis:

  lambda0_independent_of_reduction
      IF the window `g` satisfies `ZakReduction g` — the paper's analytic reduction
      (Zak transform, fibre dichotomy, degree identity, Jensen's formula on the fibre),
      packaged as a single named HYPOTHESIS that is NOT proved in this repository —
      THEN the four time–frequency translates of `g` at
      `Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)}` are linearly independent over `ℂ`.

This is a CONDITIONAL result. The HRT conjecture at `Λ₀` (Heil 2006, Conjecture 9.2(a);
Heil–Speegle, Conjecture 2) is NOT claimed unconditionally here. What is machine-checked
is the paper's endgame: that the reduction SUFFICES.
-/
import HRTLambda0.Statement
set_option autoImplicit false

namespace HRTLambda0.Statement

/-- **HRT at `Λ₀`, conditional on the analytic reduction** (the paper's endgame). -/
theorem lambda0_independent_of_reduction {g : ℝ → ℂ}
    (h : HRTLambda0.ZakReduction g) : HRTLambda0.Lambda0Independent g := by
  sorry

end HRTLambda0.Statement
