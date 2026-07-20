/-
TRUSTED CHALLENGE FILE — the statements, without proofs.

This file is the audit surface. Comparator (github.com/leanprover/comparator) checks
that the corresponding declarations in `Solution.lean` prove EXACTLY these statements
and use no axioms beyond `propext`, `Quot.sound`, `Classical.choice`.

The `sorry`s below are deliberate and are the only `sorry`s in the repository. Any
`sorry` scan must exclude this file; see `VERIFICATION.md`.

Import closure: `Erdos123.Statement` (definitions only) and Mathlib. Nothing from the
development is trusted here.

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

import Erdos123.Statement

set_option autoImplicit false

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
