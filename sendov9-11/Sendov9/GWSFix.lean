import Mathlib

set_option maxHeartbeats 400000

namespace Sendov9.GWSFix

open Finset

/-!
# The carried `GraceWalshSzego` hypothesis is FALSE as stated

Assembling the last step of GWS turned up a defect in the campaign's own statement, so
this file records it before anything is built on top.

`Master.GraceWalshSzego` is stated as

```
∀ (n : ℕ) (u : Fin n → ℂ) (R : ℝ), (∀ j, ‖u j‖ < R) →
  ∃ w : ℂ, ‖w‖ < R ∧ (∫₀¹ ∏ⱼ(1 - t uⱼ)) = (∫₀¹ (1 - t w)ⁿ)
```

At `n = 0` the hypothesis `∀ j : Fin 0, ‖u j‖ < R` is **vacuously true for every `R`**,
including negative ones, while the conclusion demands a `w` with `‖w‖ < R`.  Taking
`R = -1` refutes it: no complex number has negative norm.  `not_graceWalshSzego` below
is that refutation.

This matters beyond tidiness.  A carried hypothesis that is false makes every theorem
depending on it **vacuous** — `Master.Separation` is stated as `GraceWalshSzego → …`,
so with the current wording it is provable by `absurd` and says nothing.  The whole
point of regime (c) (carry classical results as hypotheses, never as axioms) is that
the hypotheses stay *true*; a false one is worse than an axiom, because it silently
trivialises rather than announcing itself in `#print axioms`.

The fix is one hypothesis.  `GraceWalshSzegoPos` adds `0 < n`, which is what the
classical theorem actually requires (the coincidence theorem is about the roots of a
degree-`n` polynomial) and is satisfied at every use site — the paper only ever
invokes it at `n = 8`.  `pos_of_use` records that the guard is free where it is needed:
with at least one point in the family, `R` is forced positive anyway.
-/

/-- Verbatim copy of `Master.GraceWalshSzego`. -/
noncomputable def GraceWalshSzego : Prop :=
  ∀ (n : ℕ) (u : Fin n → ℂ) (R : ℝ), (∀ j, ‖u j‖ < R) →
    ∃ w : ℂ, ‖w‖ < R ∧
      (∫ t in (0:ℝ)..1, ∏ j, (1 - (t : ℂ) * u j))
        = (∫ t in (0:ℝ)..1, (1 - (t : ℂ) * w) ^ n)

/-- **The statement as carried is false.**  At `n = 0` the hypothesis is vacuous, so
`R = -1` is admissible while the conclusion demands `‖w‖ < -1`. -/
theorem not_graceWalshSzego : ¬ GraceWalshSzego := by
  intro h
  obtain ⟨w, hw, -⟩ := h 0 (fun j => j.elim0) (-1) (fun j => j.elim0)
  have := norm_nonneg w
  linarith

/-- The corrected statement: the classical theorem is about a degree-`n` polynomial,
so it needs `0 < n`. -/
noncomputable def GraceWalshSzegoPos : Prop :=
  ∀ (n : ℕ) (u : Fin n → ℂ) (R : ℝ), 0 < n → (∀ j, ‖u j‖ < R) →
    ∃ w : ℂ, ‖w‖ < R ∧
      (∫ t in (0:ℝ)..1, ∏ j, (1 - (t : ℂ) * u j))
        = (∫ t in (0:ℝ)..1, (1 - (t : ℂ) * w) ^ n)

/-- The added guard costs nothing at the use sites: one point in the family already
forces `R > 0`, and the paper only ever invokes GWS at `n = 8`. -/
theorem pos_of_use {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) (R : ℝ)
    (hu : ∀ j, ‖u j‖ < R) : 0 < R :=
  lt_of_le_of_lt (norm_nonneg (u ⟨0, hn⟩)) (hu ⟨0, hn⟩)

end Sendov9.GWSFix

#print axioms Sendov9.GWSFix.not_graceWalshSzego
#print axioms Sendov9.GWSFix.pos_of_use
