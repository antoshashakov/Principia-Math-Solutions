/-
TRUSTED STATEMENT LAYER — Erdős Problem #883 (first question).

Import closure: Mathlib only. Contains ONLY definitions — no axioms, no sorries.
This file + `Challenge.lean` are the audit surface: read them and you have read
everything you must trust.

The problem (erdosproblems.com/883, Erdős–Sárközy [ErSa97]): for A ⊆ {1,…,n} let
G(A) be the graph on A joining coprime integers. If |A| > ⌊n/2⌋ + ⌊n/3⌋ − ⌊n/6⌋,
must G(A) contain all odd cycles of length ≤ n/3 + 1?

`T n` is the threshold ⌊n/2⌋ + ⌊n/3⌋ − ⌊n/6⌋ (the number of m ≤ n divisible by 2
or 3) and `q n = ⌊n/3⌋ − ⌊n/6⌋` (the number of odd multiples of 3 up to n), so the
conjectured sharp ceiling is length `2 * q n + 1` (which is n/3 + 1 when 6 ∣ n).

`erdos883Forcing` is the forcing statement itself, as a `Prop`; the sharpness
statements (the threshold `T n` cannot be lowered, the ceiling `2 q + 1` cannot be
raised) are stated in `Challenge.lean` and proved in `Solution.lean`.
-/
import Mathlib
set_option autoImplicit false

namespace Erdos883.Statement

open Finset

/-- The coprime graph of a finite set `A` of naturals: two distinct members of
`A` are adjacent iff they are coprime. (Vertex type is `ℕ`; vertices outside `A`
are isolated.) -/
def coprimeGraph (A : Finset ℕ) : SimpleGraph ℕ where
  Adj x y := x ≠ y ∧ x ∈ A ∧ y ∈ A ∧ Nat.Coprime x y
  symm := ⟨fun _ _ ⟨hne, hx, hy, hco⟩ => ⟨hne.symm, hy, hx, hco.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- `G` contains a cycle of length `L`. -/
def HasCycleLength (G : SimpleGraph ℕ) (L : ℕ) : Prop :=
  ∃ (v : ℕ) (w : G.Walk v v), w.IsCycle ∧ w.length = L

/-- The Erdős–Sárközy threshold `⌊n/2⌋ + ⌊n/3⌋ − ⌊n/6⌋`: the number of integers
in `[1, n]` divisible by 2 or by 3. -/
def T (n : ℕ) : ℕ := n / 2 + n / 3 - n / 6

/-- `q n = ⌊n/3⌋ − ⌊n/6⌋`: the number of odd multiples of 3 in `[1, n]`. -/
def q (n : ℕ) : ℕ := n / 3 - n / 6

/-- **Erdős #883, first question (sharp form; Erdős–Sárközy conjecture, c = 1/6).**
Any `A ⊆ [1, n]` with `|A| > T n` spans every odd cycle length `3, 5, …, 2⋅q n + 1`
in the coprime graph. This `Prop` is the forcing statement of record; it is NOT
proved in this repository (see `VERIFICATION.md`). -/
def erdos883Forcing : Prop :=
  ∀ (n : ℕ) (A : Finset ℕ), A ⊆ Icc 1 n → T n < A.card →
    ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ q n → HasCycleLength (coprimeGraph A) (2 * ℓ + 1)

end Erdos883.Statement
