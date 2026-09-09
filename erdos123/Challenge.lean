/-
TRUSTED CHALLENGE FILE — the statements, without proofs.

This file is the audit surface. Comparator (github.com/leanprover/comparator) checks
that the corresponding declarations in `Solution.lean` prove EXACTLY these statements
and use no axioms beyond `propext`, `Quot.sound`, `Classical.choice`.

The `sorry`s below are deliberate and are the only `sorry`s in the repository. Any
`sorry` scan must exclude this file; see `VERIFICATION.md`.

IMPORT CLOSURE: Mathlib only, as Palomar's Challenge policy requires. The definitions
in the first namespace block below are a verbatim copy of `Erdos123/Statement.lean`, the
module the development and `Solution.lean` import; Comparator checks that the two
copies agree declaration by declaration, so a drift between them fails the check.

WHAT EACH STATEMENT SAYS, in words:

  erdos123_dcomplete'          Erdős #123. For pairwise-coprime a,b,c > 1 the set
                               {a^k b^ℓ c^m} is d-complete: every large n is the sum of
                               a finite DIVISIBILITY-ANTICHAIN of elements of that set.

  erdos123_dcomplete_real      The same, localized: the antichain can be taken inside a
                               single short band [x, ρx) for any real ρ ∈ (1, min(a,b,c)).

  glclt_coverage               Local CLT, coverage half. For large x every n in the full
                               central window (2n − S₁)² ≤ S₂ — i.e. |n − μ_x| ≤ σ_x — is
                               a subset sum of the band. No shrinkage constant.

  glclt_asymptotic             Local CLT, limit law itself. P(Y_x = n) equals the Gaussian
                               density at n up to o(1/σ_x), UNIFORMLY in n. The ∀ n sits
                               inside the ∃ X₀, which is what "uniformly in n" means.

DEPENDENCY NOTE. All four statements are unconditional and self-contained. This
repository proves them outright; none of them assumes a literature result. See
`formalization.yaml` (`status.main_results[].literature_dependencies`, all empty) and
§3 of `STATUS.md` for the one place the accompanying paper goes further than the Lean
does (the effectivity claims — the thresholds here are existential, not explicit).
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

namespace Erdos123.Statement

/-- **Erdős Problem #123.** For pairwise-coprime `a, b, c > 1`, the set `{a^k b^ℓ c^m}`
is d-complete. -/
theorem erdos123_dcomplete' :
    ∀ a b c : ℕ, 1 < a → 1 < b → 1 < c → PairwiseCoprime3 a b c →
      IsDComplete (Smooth3 a b c) := by
  sorry

/-- **Erdős #123, localized to a band of any real ratio** `ρ ∈ (1, min(a,b,c))`. -/
theorem erdos123_dcomplete_real (a b c : ℕ) (ρ : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hρ1 : 1 < ρ) (hρd : ρ < min a (min b c)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ x : ℕ, ∃ T : Finset ℕ,
        (∀ s ∈ T, s ∈ Smooth3 a b c ∧ (x : ℝ) ≤ s ∧ (s : ℝ) < ρ * x) ∧
        IsPrimitive T ∧ T.sum id = n := by
  sorry

/-- **Local CLT, coverage half.** Every `n` in the full central window
`(2n − S₁)² ≤ S₂` is a subset sum of the band, for all large `x`. -/
theorem glclt_coverage (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      (2 * (n : ℤ) - (GS1 a b c p q x : ℤ)) ^ 2 ≤ (GS2 a b c p q x : ℤ) →
      ∃ T : Finset ℕ, T ⊆ GBand a b c p q x ∧ T.sum id = n := by
  sorry

/-- **The local limit law.** `P(Y_x = n) = (1/(√(2π)σ_x))·exp(−(n−μ_x)²/(2σ_x²)) + o(1/σ_x)`,
uniformly in `n`. -/
theorem glclt_asymptotic (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      |gProb a b c p q x n
         - (1 / (Real.sqrt (2 * Real.pi) * gSigma a b c p q x))
             * Real.exp (-(((n : ℝ) - gMu a b c p q x) ^ 2
                 / (2 * gSigma a b c p q x ^ 2)))|
        ≤ ε / gSigma a b c p q x := by
  sorry

/-- **Rigidity, eq. (3.1).** The set of frequencies of energy at most `z` has measure at
most `(1/x)·exp(C(1 + z/L)·log(L+2))`. The circle `ℝ/ℤ` is realized as `[0,1)`. -/
theorem glow_energy_measure_general (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ z₀ C₄ : ℝ, ∃ X₂ : ℕ, 0 < z₀ ∧ 1 ≤ C₄ ∧ ∀ x : ℕ, X₂ ≤ x → ∀ z : ℝ,
      0 ≤ z → z ≤ z₀ * Real.log x ^ 2 →
        MeasureTheory.volume
            {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ z}
          ≤ ENNReal.ofReal ((1 / (x : ℝ)) *
              Real.exp (C₄ * (1 + z / Real.log x) * Real.log (Real.log x + 2))) := by
  sorry

/-- **Rigidity, eq. (3.2).** Very low energy forces `t` to be within `δ/x` of an integer,
with the paper's calibration `δ·min(a,b,c) ≤ 1/8`. -/
theorem gvery_low_sharp (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ κ₀ δ : ℝ, ∃ X₅ : ℕ, 0 < κ₀ ∧ 0 < δ ∧
      δ * ((min a (min b c) : ℕ) : ℝ) ≤ 1 / 8 ∧ ∀ x : ℕ, X₅ ≤ x → ∀ t : ℝ,
        GQenergy a b c p q x t < κ₀ * Real.log x → ∃ r : ℤ, |t - (r : ℝ)| ≤ δ / (x : ℝ) := by
  sorry

end Erdos123.Statement
