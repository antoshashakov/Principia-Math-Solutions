/-
TRUSTED CHALLENGE FILE — the statements, without proofs.

This file is the audit surface. Comparator (github.com/leanprover/comparator) checks that
the corresponding declarations in `Solution.lean` prove EXACTLY these statements, using no
axioms beyond the permitted list in `comparator/*.json`:
  • `erdos361_cge1`      — [propext, Quot.sound, Classical.choice]  (axiom-free).
  • `erdos361_irregular` — [propext, Quot.sound, Classical.choice]  (axiom-free). Alon 1987
    Thm 1.1, formerly postulated, is now PROVED in `Erdos361/Core.lean` (general-h Dias da
    Silva–Hamidoune from Mathlib's Combinatorial Nullstellensatz, on the subsequence n = 2p).

The `sorry`s below are deliberate and are the only `sorry`s in the repository.

Import closure: `Erdos361.Statement` (definitions only) and Mathlib. Nothing
from the development is trusted here.

WHAT EACH STATEMENT SAYS, in words:

  erdos361_cge1      For 1 ≤ n ≤ M, the max cardinality of a subset of [1,M] with no subset
                     summing to n equals M − ⌈n/2⌉ (here `(n+1)/2` = ⌈n/2⌉ in ℕ). Hence for
                     c ≥ 1, f_c(n)/n → c − 1/2: the regular range.

  erdos361_irregular Erdős–Graham irregularity. For every real c ∈ (0,1) the sequence
                     f_c(n)/n = F ⌊cn⌋ n / n does NOT converge.
-/
import Erdos361.Statement
set_option autoImplicit false

namespace Erdos361.Statement
open Filter Topology

/-- **Erdős #361, regular range.** For `1 ≤ n ≤ M`, `F M n = M − ⌈n/2⌉`. -/
theorem erdos361_cge1 (M n : ℕ) (hn : 1 ≤ n) (hM : n ≤ M) :
    F M n = M - (n + 1) / 2 := by
  sorry

/-- **Erdős #361, irregularity (c ∈ (0,1)).** `f_c(n)/n` does not converge. -/
theorem erdos361_irregular (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ¬ ∃ L : ℝ, Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (nhds L) := by
  sorry

end Erdos361.Statement
