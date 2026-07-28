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
open scoped Pointwise

/-- **Erdős #361, regular range.** For `1 ≤ n ≤ M`, `F M n = M − ⌈n/2⌉`. -/
theorem erdos361_cge1 (M n : ℕ) (hn : 1 ≤ n) (hM : n ≤ M) :
    F M n = M - (n + 1) / 2 := by
  sorry

/-- **Erdős #361, irregularity (c ∈ (0,1)).** `f_c(n)/n` does not converge. -/
theorem erdos361_irregular (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ¬ ∃ L : ℝ, Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (nhds L) := by
  sorry

/-- **Erdős #361, Part 1 — Basile's Problem 7.1 (snd = 3 linear case).** For every `ε > 0` there is an
`E₀` such that for all `E ≥ E₀`, every `A ⊆ [1,E]` of density `≥ 1/3 + ε` represents every even
`t ∈ (2E, 3E)` with `3 ∤ t` (i.e. `¬ Avoids A t`). The single hypothesis `hFreiman` is Freiman's
`3k-3` theorem (`|B+B| ≥ min{L,2|B|-3}+|B|`, here in the range `L ≥ 2|B|-3` and for gcd-`1` sets) —
a standard published result not in Mathlib, carried as a hypothesis, never an axiom. The Lean is
otherwise fully axiom-free; in particular Alon's Prop 2.5 good core and the located covering are
*proved* in-development (`good_core_exists`, `hLev_covering`), the latter avoiding Lev 1997 entirely. -/
theorem basile71_unconditional (ε : ℝ) (hε : 0 < ε)
    (hFreiman : ∀ (B' : Finset ℕ) (L' : ℕ), B' ⊆ Finset.Icc 0 L' → 0 ∈ B' → L' ∈ B' →
      3 ≤ B'.card → 2 * B'.card - 3 ≤ L' → B'.gcd id = 1 → 3 * B'.card - 3 ≤ (B' + B').card) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 3 + ε) * E ≤ (A.card : ℝ) →
      ∀ t : ℕ, 2 * E < t → t < 3 * E → 2 ∣ t → ¬ 3 ∣ t → ¬ Avoids A t := by
  sorry

end Erdos361.Statement
