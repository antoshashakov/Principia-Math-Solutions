/-
TRUSTED CHALLENGE FILE — the statements, without proofs.

This file is the audit surface. Comparator (github.com/leanprover/comparator) checks
that the corresponding declarations in `Solution.lean` prove EXACTLY these statements,
using no axioms beyond [propext, Quot.sound, Classical.choice] (axiom-free).

The `sorry`s below are deliberate and are the only `sorry`s in the repository.

WHAT EACH STATEMENT SAYS, in words:

  erdos883_threshold_sharp   The threshold cannot be lowered: for every n there is
                             A ⊆ [1,n] with |A| = T n whose coprime graph contains
                             no odd cycle at all. (Take the multiples of 2 or 3:
                             the evens and the odd multiples of 3 are each
                             independent, so the graph is bipartite.)

  erdos883_ceiling_sharp     The ceiling 2⋅q n + 1 cannot be raised, and is attained:
                             for every n ≥ 1 there is A ⊆ [1,n] with |A| = T n + 1
                             whose coprime graph contains the odd cycles of every
                             length 2t+1 with 1 ≤ t ≤ q n and NO odd cycle longer
                             than 2⋅q n + 1. (Take all evens plus the q n + 1
                             smallest odd numbers.)

The forcing direction (`Erdos883.Statement.erdos883Forcing`) is deliberately NOT
claimed here — it is not yet formalized; see `VERIFICATION.md`.
-/
import Erdos883.Statement
set_option autoImplicit false

namespace Erdos883.Statement
open Finset

/-- **Erdős #883, threshold sharpness.** Some `A ⊆ [1,n]` of size exactly `T n`
has a bipartite coprime graph: no odd cycle of any length. -/
theorem erdos883_threshold_sharp (n : ℕ) :
    ∃ A ⊆ Icc 1 n, A.card = T n ∧
      ∀ L : ℕ, Odd L → ¬ HasCycleLength (coprimeGraph A) L := by
  sorry

/-- **Erdős #883, ceiling sharpness and attainment.** Some `A ⊆ [1,n]` of size
`T n + 1` realizes every forced odd cycle length `2t+1`, `1 ≤ t ≤ q n`, and no
longer odd cycle. Hence the conjectured ceiling `2⋅q n + 1` is best possible. -/
theorem erdos883_ceiling_sharp (n : ℕ) (hn : 1 ≤ n) :
    ∃ A ⊆ Icc 1 n, A.card = T n + 1 ∧
      (∀ t : ℕ, 1 ≤ t → t ≤ q n → HasCycleLength (coprimeGraph A) (2 * t + 1)) ∧
      (∀ t : ℕ, q n < t → ¬ HasCycleLength (coprimeGraph A) (2 * t + 1)) := by
  sorry

end Erdos883.Statement
