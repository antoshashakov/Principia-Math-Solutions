/-
SOLUTION FILE — the same two statements as `Challenge.lean`, proved.

Each proof is a direct term assignment from the development (`Erdos361.Core`). A term
assignment forces Lean to check that the development's statement and the trusted statement
in `Challenge.lean` are DEFINITIONALLY EQUAL — which, since the development imports
`Erdos361.Statement`, is immediate. There is no transport lemma doing hidden work.

The `#print axioms` lines are a redundant local audit; Comparator performs the authoritative
check of the footprints against `Challenge.lean`. Expected footprints:
  • erdos361_cge1      : [propext, Classical.choice, Quot.sound]
  • erdos361_irregular : [propext, Classical.choice, Quot.sound]
-/
import Erdos361
import Erdos361.Statement
set_option autoImplicit false

namespace Erdos361.Statement
open Filter Topology

/-- **Erdős #361, regular range.** -/
theorem erdos361_cge1 (M n : ℕ) (hn : 1 ≤ n) (hM : n ≤ M) :
    F M n = M - (n + 1) / 2 :=
  Erdos361.erdos361_cge1 M n hn hM

/-- **Erdős #361, irregularity (c ∈ (0,1)).** -/
theorem erdos361_irregular (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ¬ ∃ L : ℝ, Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (nhds L) :=
  Erdos361.erdos361_irregular c hc0 hc1

#print axioms erdos361_cge1
#print axioms erdos361_irregular

end Erdos361.Statement
