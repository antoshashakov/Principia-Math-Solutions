/-
# Sendov 9/10/11: the conditional capstone

`Sendov9to11.lean` states `PaperMainTheorem := Sendov 9 ∧ Sendov 10 ∧ Sendov 11`
but never concludes it, and never states an implication into it either — so
there is no place where the unproved inputs are named.  `HRTLambda0.lean` does
this properly, via `ZakReduction`; this file does the same for Sendov.

The split is exactly the paper's own:

* the **analytic reduction** (Grace–Walsh–Szegő and the separation lemma, the
  reciprocal-square extremum, variance-under-differentiation, the centered
  elementary-symmetric bounds, and the assembly of the certificate polynomial
  from the integral identity) is bundled into one named hypothesis,
  `CertificateReduction`;
* the **finite half** — positivity of the certificate polynomials on the boxes
  covering `a ∈ [0,1]` — is `CoveringPositive`, and *that* is what the
  machine-checked box files discharge.

`sendov_of_reduction` shows those two together give `Sendov n`.  Nothing here is
an `axiom` and nothing is `sorry`-ed: the analytic content is a hypothesis, and
its absence is visible in the statement rather than hidden in prose.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Sendov911Capstone

open Finset

/-! ## The statement (identical to `Sendov911.Sendov`) -/

/-- **Sendov's conjecture in degree `n`.** -/
def Sendov (n : ℕ) : Prop :=
  ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
    (∀ z ∈ p.roots, ‖z‖ ≤ 1) →
    ∀ a ∈ p.roots, ∃ ζ : ℂ, (Polynomial.derivative p).IsRoot ζ ∧ ‖a - ζ‖ ≤ 1

/-! ## Certificate boxes

A box carries its bidegree, its integer monomial table, and the positive scale
`D`; the polynomial it certifies is `∑ (A k l / D) · U^k · V^l` on `[0,1]²`,
which is the paper's certificate polynomial after the affine pullback. -/

/-- One certificate box: bidegree, integer coefficient table, scale. -/
structure Box where
  nx : ℕ
  ny : ℕ
  A : ℕ → ℕ → ℤ
  D : ℝ
  hD : 0 < D

/-- The polynomial a box certifies, on the unit square. -/
noncomputable def Box.poly (b : Box) (U V : ℝ) : ℝ :=
  ∑ k ∈ range (b.nx + 1), ∑ l ∈ range (b.ny + 1), ((b.A k l : ℝ) / b.D) * U ^ k * V ^ l

/-- The finite half: every box in the covering family is positive on `[0,1]²`.
This is precisely what each machine-checked `box_positive` supplies. -/
def CoveringPositive (boxes : List Box) : Prop :=
  ∀ b ∈ boxes, ∀ U V : ℝ, 0 ≤ U → U ≤ 1 → 0 ≤ V → V ≤ 1 → 0 < b.poly U V

/-- The analytic half, stated as a hypothesis.  A counterexample in degree `n`
is driven — by separation, the reciprocal normalization, the product constraint,
the localization inequality and the integral identity — into one of the boxes of
the covering family, at a point of the unit square where that box's certificate
polynomial is **non-positive**.

Everything the paper proves before its finite checks is contained in this one
predicate, and nothing else in this file assumes any of it. -/
def CertificateReduction (n : ℕ) (boxes : List Box) : Prop :=
  ¬ Sendov n →
    ∃ b ∈ boxes, ∃ U V : ℝ, 0 ≤ U ∧ U ≤ 1 ∧ 0 ≤ V ∧ V ≤ 1 ∧ b.poly U V ≤ 0

/-- **The capstone.**  The analytic reduction plus the machine-checked finite
positivity gives Sendov's conjecture in degree `n`. -/
theorem sendov_of_reduction {n : ℕ} {boxes : List Box}
    (hred : CertificateReduction n boxes) (hpos : CoveringPositive boxes) :
    Sendov n := by
  by_contra hbad
  obtain ⟨b, hb, U, V, hU0, hU1, hV0, hV1, hle⟩ := hred hbad
  exact absurd (hpos b hb U V hU0 hU1 hV0 hV1) (not_lt.mpr hle)

/-- The paper's headline, in the same conditional form. -/
theorem paper_main_of_reduction
    {b9 b10 b11 : List Box}
    (h9 : CertificateReduction 9 b9) (p9 : CoveringPositive b9)
    (h10 : CertificateReduction 10 b10) (p10 : CoveringPositive b10)
    (h11 : CertificateReduction 11 b11) (p11 : CoveringPositive b11) :
    Sendov 9 ∧ Sendov 10 ∧ Sendov 11 :=
  ⟨sendov_of_reduction h9 p9, sendov_of_reduction h10 p10, sendov_of_reduction h11 p11⟩

/-! ## Assembling `CoveringPositive` from the individual box files

Each generated box file proves exactly `0 < ∑ ... ((tab Adata k l : ℝ)/Dscale) * U^k * V^l`
for its own data, which is `Box.poly` of the corresponding `Box`.  The two
lemmas below are the glue: a singleton family, and consing one more certified
box onto a certified family. -/

theorem coveringPositive_nil : CoveringPositive [] := by
  intro b hb
  cases hb

theorem coveringPositive_cons {b : Box} {rest : List Box}
    (hb : ∀ U V : ℝ, 0 ≤ U → U ≤ 1 → 0 ≤ V → V ≤ 1 → 0 < b.poly U V)
    (hrest : CoveringPositive rest) :
    CoveringPositive (b :: rest) := by
  intro c hc U V hU0 hU1 hV0 hV1
  rcases List.mem_cons.mp hc with h | h
  · subst h; exact hb U V hU0 hU1 hV0 hV1
  · exact hrest c h U V hU0 hU1 hV0 hV1

end Sendov911Capstone
