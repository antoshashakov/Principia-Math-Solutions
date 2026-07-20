/-
SOLUTION FILE — the same four statements as `Challenge.lean`, proved.

Each proof is a direct term assignment from the development's theorem. That is
deliberate: a term assignment forces Lean to check that the development's statement and
the trusted statement in `Challenge.lean` are DEFINITIONALLY EQUAL, which in turn forces
every definition copied into `Erdos123/Statement.lean` to agree with its original in
namespace `Erdos123Band`. There is no transport lemma doing hidden work, and no room for
the copies to have drifted.

The `#print axioms` lines at the bottom are a redundant local audit; Comparator performs
the authoritative axiom check against `Challenge.lean`.
-/

import Erdos123
import Erdos123.Statement

set_option autoImplicit false

namespace Erdos123.Statement

/-- **Erdős Problem #123.** -/
theorem erdos123_dcomplete' :
    ∀ a b c : ℕ, 1 < a → 1 < b → 1 < c → PairwiseCoprime3 a b c →
      IsDComplete (Smooth3 a b c) :=
  Erdos123Band.erdos123_dcomplete'

/-- **Erdős #123, localized to a band of any real ratio.** -/
theorem erdos123_dcomplete_real (a b c : ℕ) (ρ : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hρ1 : 1 < ρ) (hρd : ρ < min a (min b c)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ x : ℕ, ∃ T : Finset ℕ,
        (∀ s ∈ T, s ∈ Smooth3 a b c ∧ (x : ℝ) ≤ s ∧ (s : ℝ) < ρ * x) ∧
        IsPrimitive T ∧ T.sum id = n :=
  Erdos123Band.erdos123_dcomplete_real a b c ρ ha hb hc hco hρ1 hρd

/-- **Local CLT, coverage half.** -/
theorem glclt_coverage (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      (2 * (n : ℤ) - (GS1 a b c p q x : ℤ)) ^ 2 ≤ (GS2 a b c p q x : ℤ) →
      ∃ T : Finset ℕ, T ⊆ GBand a b c p q x ∧ T.sum id = n :=
  Erdos123Band.glclt_coverage a b c p q ha hb hc hco hq hqp hpd

/-- **The local limit law**, uniformly in `n`. -/
theorem glclt_asymptotic (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      |gProb a b c p q x n
         - (1 / (Real.sqrt (2 * Real.pi) * gSigma a b c p q x))
             * Real.exp (-(((n : ℝ) - gMu a b c p q x) ^ 2
                 / (2 * gSigma a b c p q x ^ 2)))|
        ≤ ε / gSigma a b c p q x :=
  Erdos123Band.glclt_asymptotic a b c p q ha hb hc hco hq hqp hpd

/-- **Rigidity, eq. (3.1).** -/
theorem glow_energy_measure_general (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ z₀ C₄ : ℝ, ∃ X₂ : ℕ, 0 < z₀ ∧ 1 ≤ C₄ ∧ ∀ x : ℕ, X₂ ≤ x → ∀ z : ℝ,
      0 ≤ z → z ≤ z₀ * Real.log x ^ 2 →
        MeasureTheory.volume
            {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ z}
          ≤ ENNReal.ofReal ((1 / (x : ℝ)) *
              Real.exp (C₄ * (1 + z / Real.log x) * Real.log (Real.log x + 2))) :=
  Erdos123Band.glow_energy_measure_general a b c p q ha hb hc hco hq hqp hpd

/-- **Rigidity, eq. (3.2).** -/
theorem gvery_low_sharp (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ κ₀ δ : ℝ, ∃ X₅ : ℕ, 0 < κ₀ ∧ 0 < δ ∧
      δ * ((min a (min b c) : ℕ) : ℝ) ≤ 1 / 8 ∧ ∀ x : ℕ, X₅ ≤ x → ∀ t : ℝ,
        GQenergy a b c p q x t < κ₀ * Real.log x → ∃ r : ℤ, |t - (r : ℝ)| ≤ δ / (x : ℝ) :=
  Erdos123Band.gvery_low_sharp a b c p q ha hb hc hco hq hqp hpd

#print axioms erdos123_dcomplete'
#print axioms erdos123_dcomplete_real
#print axioms glclt_coverage
#print axioms glclt_asymptotic
#print axioms glow_energy_measure_general
#print axioms gvery_low_sharp

end Erdos123.Statement
