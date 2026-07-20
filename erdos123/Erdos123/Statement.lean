/-
TRUSTED STATEMENT LAYER — Erdős Problem #123 and the local limit law.

This module exists so that `Challenge.lean` has a SMALL, AUDITABLE import closure.
It imports only Mathlib and contains ONLY definitions — no theorem, no proof, no
unproved placeholder of any kind, and no additional postulate. A reviewer who wants to
convince themselves that the formalized statements say what the paper says has to read
this file and `Challenge.lean`, and nothing else.

Every definition below is a verbatim copy of the corresponding definition in the
development (`Erdos123/Band.lean`, `Erdos123/GBand.lean`, `Erdos123/GLCLTAsymptotic.lean`,
all in namespace `Erdos123Band`). The copies are not merely intended to agree — the
agreement is CHECKED: `Solution.lean` proves each headline theorem in this file's
vocabulary by direct term assignment from the development's theorem, which forces Lean
to verify the two definition sets are definitionally equal. If a copy drifted, that file
would fail to compile.
-/

import Mathlib

set_option autoImplicit false

namespace Erdos123.Statement

/-! ## The set in question -/

/-- The positive integers representable as `a^k * b^l * c^m` with natural exponents. -/
def Smooth3 (a b c : ℕ) : Set ℕ :=
  {x | ∃ k l m : ℕ, x = a ^ k * b ^ l * c ^ m}

/-- No member of `s` divides another (divisibility antichain on distinct elements). -/
def IsPrimitive (s : Finset ℕ) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ¬x ∣ y

/-- Every sufficiently large natural number is the sum of a primitive finset of `A`.
This is the "d-complete" of Erdős #123. -/
def IsDComplete (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ s : Finset ℕ, (∀ x ∈ s, x ∈ A) ∧ IsPrimitive s ∧ s.sum id = n

/-- Pairwise coprimality of the three bases. -/
def PairwiseCoprime3 (a b c : ℕ) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c

/-! ## The band and its moments -/

/-- The multiplicative band `Smooth3 a b c ∩ [x, (p/q)·x)` as a finset. -/
noncomputable def GBand (a b c p q x : ℕ) : Finset ℕ :=
  letI := Classical.decPred (fun s => s ∈ Smooth3 a b c ∧ x ≤ s ∧ q * s < p * x)
  (Finset.range (2 * p * x)).filter (fun s => s ∈ Smooth3 a b c ∧ x ≤ s ∧ q * s < p * x)

/-- Band first moment `S₁ = ∑_{s ∈ B_x} s`. -/
noncomputable def GS1 (a b c p q x : ℕ) : ℕ := (GBand a b c p q x).sum id

/-- Band second moment `S₂ = ∑_{s ∈ B_x} s²`. -/
noncomputable def GS2 (a b c p q x : ℕ) : ℕ := (GBand a b c p q x).sum (fun s => s ^ 2)

/-! ## The statistics of the random subset sum

`Y_x = ∑_{s ∈ B_x} s·ξ_s` with `ξ_s` i.i.d. uniform on `{0,1}`. No measure-theoretic
probability is used: `P(Y_x = n)` is the finite ratio `gProb` below. -/

/-- `σ_x = √(S₂)/2`, the standard deviation of `Y_x`. -/
noncomputable def gSigma (a b c p q x : ℕ) : ℝ := Real.sqrt (GS2 a b c p q x) / 2

/-- `μ_x = S₁/2`, the mean of `Y_x`. -/
noncomputable def gMu (a b c p q x : ℕ) : ℝ := (GS1 a b c p q x : ℝ) / 2

/-- `P(Y_x = n)`: the fraction of subsets of the band summing to `n`. -/
noncomputable def gProb (a b c p q x n : ℕ) : ℝ :=
  ((((GBand a b c p q x).powerset.filter (fun T => ∑ s ∈ T, s = n)).card : ℕ) : ℝ)
    / 2 ^ (GBand a b c p q x).card

/-! ## Frequency energy

The paper's `Q_x(t) = ∑_{s ∈ B_x} ‖s t‖²`, where `‖y‖` is the distance from `y` to the
nearest integer. `y - round y` realizes that distance up to sign, and the square kills
the sign. -/

/-- The energy `Q_x(t) = ∑_{s ∈ B_x} ‖s t‖²`. -/
noncomputable def GQenergy (a b c p q x : ℕ) (t : ℝ) : ℝ :=
  ∑ s ∈ GBand a b c p q x, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2

end Erdos123.Statement
