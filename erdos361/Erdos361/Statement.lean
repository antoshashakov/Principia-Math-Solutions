/-
TRUSTED STATEMENT LAYER — Erdős Problem #361.

Import closure: Mathlib only. Contains ONLY definitions plus the SINGLE trusted external
postulate `alon_zero_sum` — Alon 1987 [Subset Sums, J. Number Theory 27 (1987) 196–205,
Thm 1.1], ε-form `0 < |B| ≤ k`, verbatim; not in Mathlib. This file + `Challenge.lean` are
the entire audit surface: read them and you have read everything you must trust.

The definitions are verbatim copies of the development's (`Erdos361/Core.lean`, namespace
`Erdos361`, which imports this file); `Solution.lean` proves each headline theorem by direct
term assignment, forcing Lean to check the two agree.
-/
import Mathlib
set_option autoImplicit false

namespace Erdos361.Statement
open Finset
open scoped Classical
def Avoids (A : Finset ℕ) (n : ℕ) : Prop := ∀ B ⊆ A, B.sum id = n → B = ∅
noncomputable def Avoiders (M n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 M).powerset.filter (fun A => Avoids A n)
noncomputable def F (M n : ℕ) : ℕ := (Avoiders M n).sup Finset.card
noncomputable def Fc (c : ℝ) (n : ℕ) : ℕ := F ⌊c * n⌋₊ n
axiom alon_zero_sum : ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset (ZMod N), ((1 / (k : ℝ) + ε) * N < A.card) →
      ∃ B : Finset (ZMod N), B ⊆ A ∧ B.Nonempty ∧ B.card ≤ k ∧ (∑ b ∈ B, b) = 0
end Erdos361.Statement
