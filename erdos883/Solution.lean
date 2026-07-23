/-
SOLUTION FILE — the same two statements as `Challenge.lean`, proved.

Each proof is a direct term assignment from the development (`Erdos883.Core`), forcing
Lean to check that the development's statement and the trusted statement in
`Challenge.lean` are definitionally equal.

Expected footprints (both): [propext, Classical.choice, Quot.sound].
-/
import Erdos883
import Erdos883.Statement
set_option autoImplicit false

namespace Erdos883.Statement
open Finset

/-- **Erdős #883, threshold sharpness.** -/
theorem erdos883_threshold_sharp (n : ℕ) :
    ∃ A ⊆ Icc 1 n, A.card = T n ∧
      ∀ L : ℕ, Odd L → ¬ HasCycleLength (coprimeGraph A) L :=
  Erdos883.erdos883_threshold_sharp n

/-- **Erdős #883, ceiling sharpness and attainment.** -/
theorem erdos883_ceiling_sharp (n : ℕ) (hn : 1 ≤ n) :
    ∃ A ⊆ Icc 1 n, A.card = T n + 1 ∧
      (∀ t : ℕ, 1 ≤ t → t ≤ q n → HasCycleLength (coprimeGraph A) (2 * t + 1)) ∧
      (∀ t : ℕ, q n < t → ¬ HasCycleLength (coprimeGraph A) (2 * t + 1)) :=
  Erdos883.erdos883_ceiling_sharp n hn

#print axioms erdos883_threshold_sharp
#print axioms erdos883_ceiling_sharp

end Erdos883.Statement
