/-
# Sendov's conjecture in degrees nine, ten and eleven — Lean 4 formalization

Companion to the paper

  *Sendov's Conjecture in Degrees Nine, Ten, and Eleven* (`papers/sendov-9-11.tex`),

which proves Sendov's conjecture for `n ∈ {9, 10, 11}`, extending Brown–Xiang
(`n ≤ 8`).  The paper's architecture is: a reciprocal normalization, a product
constraint, a localization inequality, and an exact integral identity, reducing
the analytic problem to positivity of explicit bivariate polynomials on rational
rectangles, certified by exact-rational tensor-product Bernstein coefficients
(18 + 1 certificates for `n = 9`, 50 + 1 for `n = 10`, 530 + 1 for `n = 11`).

## What this file proves (all axiom-free, no `sorry`)

* `Sendov` — the conjecture stated for a degree-`n` monic complex polynomial.
* `bernstein_lower_bound` / `bernstein_positive` — **paper Lemma "bernstein"**, the
  engine behind every one of the 598 certificates: a bivariate polynomial whose
  tensor-product Bernstein coefficients are all `≥ c` is `≥ c` on `[0,1]²`;
  `bernstein_lower_bound_univariate` is the one-variable form used for the
  quadratic certificates.
* `quadratic_bernstein` — paper eq. (bern-conversion) in bidegree two;
  `affine_to_unit_square` — the substitution `a = α + (β-α)U`, `η = YV` that
  carries each rational rectangle into `[0,1]²`;
  `degree9_small_a_certificate` — one of the paper's certificates run end to end
  through that pipeline inside the kernel.
* `localization_identity` / `localization_ge_one` — the pointwise identity
  `2a·Re X + (1-a²)|X|² = 1 + (1-|z|²)|X|²` behind paper eq. (localization).
* `scalar_bound` — paper eq. (scalar), `1/√(1-η²) ≥ 1 + η²/2`.
* `centered_variance` — paper eq. (variance), `∑|Y_j-μ|² = ∑|Y_j|² - N|μ|²`.
* `bad_at_one_impossible` — the paper's uniform disposal of `a = 1` in every degree.
* the paper's exact rational certificates that are pure arithmetic:
  `m9_cubic_certificate`, `m10_certificate`, `degree10_small_a_product`,
  `degree11_small_a_product`, `degree9_boundary_integer`,
  `degree9_small_a_quadratic`.

## What this file does NOT prove

Nothing here is declared as an `axiom`; the deep inputs simply do not appear.
Discharging them is out of reach of a single session and, in the last case, of
Lean's kernel at this scale:

* **Grace–Walsh–Szegő** and the separation Lemma built on it (paper Lemma
  "separation").  Not in Mathlib.
* The reciprocal-square extremum (paper Lemma "sigma") — maximizing a convex
  function over a section of a box at an extreme point.
* The variance-under-differentiation lemma (paper Lemma "variance-derivative") —
  the Schur-complement characterisation of `f'/N` as a compression, plus Schur
  triangularization.
* The centered elementary-symmetric bounds (paper Lemma "centered-esp"):
  Newton's identities, the Cauchy coefficient estimate, and the Schoenberg-type
  bound.
* The certificate assembly (paper Prop "full-certificate" / "split-certificate"),
  which needs the integral identity `I = ∫₀ᵃ G` and Jensen-type estimates.
* The **598 exact Bernstein coefficient evaluations** themselves.  Each is a
  finite exact-rational computation; `bernstein_lower_bound` is precisely the
  bridge that turns them into positivity, but reproducing tens of thousands of
  rational coefficients inside the kernel is a separate (large) engineering task.
  The paper's Python + SymPy verifiers remain the authority for those.

## Axiom footprint

`#print axioms` at the bottom; the intended footprint is exactly
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace Sendov911

open scoped BigOperators

/-! ## The statement -/

/-- **Sendov's conjecture in degree `n`.**  If every zero of a monic complex
polynomial of degree `n` lies in the closed unit disc, then for every zero `a`
some zero `ζ` of the derivative satisfies `|a - ζ| ≤ 1`.  Zeros are counted with
multiplicity (`Polynomial.roots` is a multiset). -/
def Sendov (n : ℕ) : Prop :=
  ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
    (∀ z ∈ p.roots, ‖z‖ ≤ 1) →
    ∀ a ∈ p.roots, ∃ ζ : ℂ, (Polynomial.derivative p).IsRoot ζ ∧ ‖a - ζ‖ ≤ 1

/-- The paper's main theorem is `Sendov 9 ∧ Sendov 10 ∧ Sendov 11`.  Brown–Xiang
had `Sendov n` for `n ≤ 8`. -/
def PaperMainTheorem : Prop := Sendov 9 ∧ Sendov 10 ∧ Sendov 11

/-! ## Paper Lemma "bernstein": tensor-product Bernstein positivity

This is the engine behind every certificate in the paper.  After the affine
substitution `a = α + (β-α)U`, `η = Y V`, each certificate polynomial is expanded
in the tensor-product Bernstein basis of its bidegree and its coefficients are
compared with an exact rational lower bound (`1/2100` for degree nine interior,
`1/3100` for degree ten interior, `1/2800` for degree eleven interior, and
`1/100`, `7/100`, `3/50` for the three boundary certificates). -/

/-- The univariate Bernstein basis polynomial `binom(r,i) Uⁱ (1-U)^{r-i}`. -/
noncomputable def bern (r i : ℕ) (U : ℝ) : ℝ :=
  (r.choose i : ℝ) * U ^ i * (1 - U) ^ (r - i)

theorem bern_nonneg (r i : ℕ) {U : ℝ} (h0 : 0 ≤ U) (h1 : U ≤ 1) :
    0 ≤ bern r i U := by
  have h : (0 : ℝ) ≤ 1 - U := by linarith
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0 i)) (pow_nonneg h _)

/-- The Bernstein basis of degree `r` is a partition of unity. -/
theorem sum_bern (r : ℕ) (U : ℝ) :
    ∑ i ∈ Finset.range (r + 1), bern r i U = 1 := by
  calc ∑ i ∈ Finset.range (r + 1), bern r i U
      = ∑ i ∈ Finset.range (r + 1), U ^ i * (1 - U) ^ (r - i) * (r.choose i : ℝ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [bern]
        ring
    _ = ((U + (1 - U)) : ℝ) ^ r := (add_pow U (1 - U) r).symm
    _ = 1 := by norm_num

/-- **Paper Lemma "bernstein" (quantitative form).**  If every tensor-product
Bernstein coefficient of `R` is at least `c`, then `R ≥ c` on `[0,1]²`. -/
theorem bernstein_lower_bound {r s : ℕ} {c : ℝ} (b : ℕ → ℕ → ℝ)
    (hb : ∀ i ∈ Finset.range (r + 1), ∀ j ∈ Finset.range (s + 1), c ≤ b i j)
    {U V : ℝ} (hU0 : 0 ≤ U) (hU1 : U ≤ 1) (hV0 : 0 ≤ V) (hV1 : V ≤ 1) :
    c ≤ ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (s + 1),
          b i j * (bern r i U * bern s j V) := by
  have hbase : ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (s + 1),
      c * (bern r i U * bern s j V) = c := by
    calc ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (s + 1),
          c * (bern r i U * bern s j V)
        = c * ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (s + 1),
            bern r i U * bern s j V := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      _ = c * ((∑ i ∈ Finset.range (r + 1), bern r i U) *
              (∑ j ∈ Finset.range (s + 1), bern s j V)) := by
          rw [Finset.sum_mul_sum]
      _ = c := by rw [sum_bern, sum_bern]; ring
  calc c = ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (s + 1),
            c * (bern r i U * bern s j V) := hbase.symm
    _ ≤ ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (s + 1),
            b i j * (bern r i U * bern s j V) := by
        refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
        exact mul_le_mul_of_nonneg_right (hb i hi j hj)
          (mul_nonneg (bern_nonneg _ _ hU0 hU1) (bern_nonneg _ _ hV0 hV1))

/-- Univariate form of the same bound, used for the paper's one-variable
certificates (the quadratics `S a² - N λ a + N - S` on each subinterval). -/
theorem bernstein_lower_bound_univariate {r : ℕ} {c : ℝ} (b : ℕ → ℝ)
    (hb : ∀ i ∈ Finset.range (r + 1), c ≤ b i)
    {U : ℝ} (hU0 : 0 ≤ U) (hU1 : U ≤ 1) :
    c ≤ ∑ i ∈ Finset.range (r + 1), b i * bern r i U := by
  calc c = ∑ i ∈ Finset.range (r + 1), c * bern r i U := by
        rw [← Finset.mul_sum, sum_bern, mul_one]
    _ ≤ ∑ i ∈ Finset.range (r + 1), b i * bern r i U :=
        Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (hb i hi) (bern_nonneg _ _ hU0 hU1)

/-- **Paper Lemma "bernstein".**  All tensor-product Bernstein coefficients
positive (uniformly bounded below by `c > 0`) implies `R > 0` on `[0,1]²`. -/
theorem bernstein_positive {r s : ℕ} {c : ℝ} (hc : 0 < c) (b : ℕ → ℕ → ℝ)
    (hb : ∀ i ∈ Finset.range (r + 1), ∀ j ∈ Finset.range (s + 1), c ≤ b i j)
    {U V : ℝ} (hU0 : 0 ≤ U) (hU1 : U ≤ 1) (hV0 : 0 ≤ V) (hV1 : V ≤ 1) :
    0 < ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (s + 1),
          b i j * (bern r i U * bern s j V) :=
  lt_of_lt_of_le hc (bernstein_lower_bound b hb hU0 hU1 hV0 hV1)

/-- **Paper eq. (bern-conversion), degree two.**  The degree-two Bernstein
coefficients of `A U² + B U + C` are `C`, `C + B/2`, `A + B + C`. -/
theorem quadratic_bernstein (A B C U : ℝ) :
    A * U ^ 2 + B * U + C
      = C * bern 2 0 U + (C + B / 2) * bern 2 1 U + (A + B + C) * bern 2 2 U := by
  norm_num [bern]
  ring

/-- **The affine substitution used before every certificate.**  A point of the
rational rectangle `[α,β] × [0,Y]` pulls back into the unit square under
`a = α + (β-α)U`, `η = Y V`, which is where Lemma "bernstein" applies. -/
theorem affine_to_unit_square {α β Y a η : ℝ} (hab : α < β) (hY : 0 < Y)
    (ha : a ∈ Set.Icc α β) (hη : η ∈ Set.Icc (0 : ℝ) Y) :
    ((a - α) / (β - α) ∈ Set.Icc (0 : ℝ) 1 ∧ η / Y ∈ Set.Icc (0 : ℝ) 1)
      ∧ a = α + (β - α) * ((a - α) / (β - α)) ∧ η = Y * (η / Y) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hη1, hη2⟩ := hη
  have hd : (0 : ℝ) < β - α := by linarith
  refine ⟨⟨⟨div_nonneg (by linarith) hd.le, (div_le_one hd).mpr (by linarith)⟩,
    ⟨div_nonneg hη1 hY.le, (div_le_one hY).mpr hη2⟩⟩, ?_, ?_⟩
  · field_simp
    ring
  · field_simp

/-- **A worked certificate, run through the paper's own pipeline.**  The
degree-nine small-`a` quadratic `S₀a² - 8a + 8 - S₀` with `S₀ = 1101/200`, pulled
back to `[0,1]` by `a = (9/20)U`, has degree-two Bernstein coefficients
`499/200`, `139/200`, `781/80000` — all at least `781/80000`.  Lemma "bernstein"
then delivers the paper's bound on `[0, 9/20]` with no ad-hoc inequality, exactly
as the ancillary verifiers do for the 598 real certificates. -/
theorem degree9_small_a_certificate {U : ℝ} (hU0 : 0 ≤ U) (hU1 : U ≤ 1) :
    (781 : ℝ) / 80000
      ≤ (1101 / 200 : ℝ) * ((9 / 20) * U) ^ 2 - 8 * ((9 / 20) * U) + 8 - 1101 / 200 := by
  set b : ℕ → ℝ := fun i => if i = 0 then 499 / 200 else if i = 1 then 139 / 200
    else 781 / 80000 with hbdef
  have hrep : (1101 / 200 : ℝ) * ((9 / 20) * U) ^ 2 - 8 * ((9 / 20) * U) + 8 - 1101 / 200
      = ∑ i ∈ Finset.range 3, b i * bern 2 i U := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num [hbdef, bern]
    ring
  rw [hrep]
  refine bernstein_lower_bound_univariate b ?_ hU0 hU1
  intro i hi
  rw [Finset.mem_range] at hi
  rcases i with _ | _ | _ | i
  · norm_num [hbdef]
  · norm_num [hbdef]
  · norm_num [hbdef]
  · exact absurd hi (by omega)

/-! ## The reciprocal normalization: the localization inequality

With `a` real and `X = 1/(a - z)`, the paper computes
`2a·Re X + (1-a²)|X|² = 1 + (1-|z|²)|X|² ≥ 1`, and sums over `k` to get
`aNu + (1-a²)σ ≥ N` (paper eq. (localization)). -/

/-- **Paper eq. (localization), pointwise identity.**  For real `a` and `X ≠ 0`,
writing `z = a - X⁻¹` (equivalently `X = 1/(a-z)`),
`2a·Re X + (1-a²)|X|² = 1 + (1-|z|²)|X|²`. -/
theorem localization_identity (a : ℝ) (X : ℂ) (hX : X ≠ 0) :
    2 * a * X.re + (1 - a ^ 2) * ‖X‖ ^ 2
      = 1 + (1 - ‖(a : ℂ) - X⁻¹‖ ^ 2) * ‖X‖ ^ 2 := by
  have hnorm : ∀ w : ℂ, ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := fun w => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  -- Clear the inverse by multiplying through by `X`.
  have hmul : ((a : ℂ) - X⁻¹) * X = (a : ℂ) * X - 1 := by
    rw [sub_mul, inv_mul_cancel₀ hX]
  have hkey : ‖(a : ℂ) - X⁻¹‖ ^ 2 * ‖X‖ ^ 2 = ‖(a : ℂ) * X - 1‖ ^ 2 := by
    rw [← mul_pow, ← norm_mul, hmul]
  have hexp : ‖(a : ℂ) * X - 1‖ ^ 2 = a ^ 2 * ‖X‖ ^ 2 - 2 * a * X.re + 1 := by
    rw [hnorm, hnorm]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
    ring
  have hsplit : (1 - ‖(a : ℂ) - X⁻¹‖ ^ 2) * ‖X‖ ^ 2
      = ‖X‖ ^ 2 - ‖(a : ℂ) * X - 1‖ ^ 2 := by
    rw [sub_mul, one_mul, hkey]
  rw [hsplit, hexp]
  ring

/-- **Paper eq. (localization).**  Since the zero `z = a - X⁻¹` lies in the closed
unit disc, `2a·Re X + (1-a²)|X|² ≥ 1`. -/
theorem localization_ge_one (a : ℝ) (X : ℂ) (hX : X ≠ 0)
    (hz : ‖(a : ℂ) - X⁻¹‖ ≤ 1) :
    1 ≤ 2 * a * X.re + (1 - a ^ 2) * ‖X‖ ^ 2 := by
  rw [localization_identity a X hX]
  have h1 : ‖(a : ℂ) - X⁻¹‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg ((a : ℂ) - X⁻¹)]
  have h2 : (0 : ℝ) ≤ ‖X‖ ^ 2 := sq_nonneg _
  nlinarith

/-- **The case `a = 1`, disposed of uniformly in every degree.**  At `a = 1` the
localization inequality reads `Nu ≥ N`, so `u ≥ 1`; but `u ≤ |μ| < 1`. -/
theorem bad_at_one_impossible {N : ℕ} {u v : ℝ} (hN : 0 < N)
    (hloc : (N : ℝ) * 1 ≤ (N : ℝ) * u) (hmu : u ^ 2 + v ^ 2 < 1) : False := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : 1 ≤ u := le_of_mul_le_mul_left hloc hNpos
  nlinarith [sq_nonneg v]

/-! ## Paper eq. (variance): centering the reciprocal critical points -/

/-- **Paper eq. (variance).**  If `μ` is the mean of `Y₁,…,Y_N`, then the centered
points `D_j = Y_j - μ` satisfy `∑ |D_j|² = ∑ |Y_j|² - N|μ|²`. -/
theorem centered_variance {N : ℕ} (Y : Fin N → ℂ) (μ : ℂ)
    (hμ : ∑ j, Y j = (N : ℂ) * μ) :
    ∑ j, ‖Y j - μ‖ ^ 2 = (∑ j, ‖Y j‖ ^ 2) - (N : ℝ) * ‖μ‖ ^ 2 := by
  have hnorm : ∀ w : ℂ, ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := fun w => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hre : ∑ j, (Y j).re = (N : ℝ) * μ.re := by
    have h := congrArg Complex.re hμ
    simpa using h
  have him : ∑ j, (Y j).im = (N : ℝ) * μ.im := by
    have h := congrArg Complex.im hμ
    simpa using h
  have key : ∀ j : Fin N, ‖Y j - μ‖ ^ 2
      = ‖Y j‖ ^ 2 - 2 * (μ.re * (Y j).re + μ.im * (Y j).im) + ‖μ‖ ^ 2 := by
    intro j
    rw [hnorm, hnorm, hnorm]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  calc ∑ j, ‖Y j - μ‖ ^ 2
      = ∑ j : Fin N, (‖Y j‖ ^ 2
          - 2 * (μ.re * (Y j).re + μ.im * (Y j).im) + ‖μ‖ ^ 2) :=
        Finset.sum_congr rfl fun j _ => key j
    _ = (∑ j, ‖Y j‖ ^ 2)
          - (∑ j : Fin N, 2 * (μ.re * (Y j).re + μ.im * (Y j).im))
          + (∑ _j : Fin N, ‖μ‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ j, ‖Y j‖ ^ 2)
          - (2 * μ.re * (∑ j, (Y j).re) + 2 * μ.im * (∑ j, (Y j).im))
          + (N : ℝ) * ‖μ‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        congr 1
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ j, ‖Y j‖ ^ 2) - (N : ℝ) * ‖μ‖ ^ 2 := by
        rw [hre, him, hnorm]
        ring

/-! ## Paper eq. (scalar) -/

/-- **Paper eq. (scalar).**  `1/√(1-η²) ≥ 1 + η²/2` for `0 ≤ η < 1`, certified by
`(1 + η²/2)²(1-η²) = 1 - (3/4)η⁴ - (1/4)η⁶ ≤ 1`. -/
theorem scalar_bound {η : ℝ} (h0 : 0 ≤ η) (h1 : η < 1) :
    1 + η ^ 2 / 2 ≤ 1 / Real.sqrt (1 - η ^ 2) := by
  have hpos : (0 : ℝ) < 1 - η ^ 2 := by nlinarith
  have hA0 : 0 < Real.sqrt (1 - η ^ 2) := Real.sqrt_pos.mpr hpos
  have hA2 : Real.sqrt (1 - η ^ 2) ^ 2 = 1 - η ^ 2 := Real.sq_sqrt hpos.le
  have key : (1 + η ^ 2 / 2) * Real.sqrt (1 - η ^ 2) ≤ 1 := by
    nlinarith [hA2, hA0.le, sq_nonneg (η ^ 2), sq_nonneg (η ^ 3),
      mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + η ^ 2 / 2) hA0.le]
  rw [le_div_iff₀ hA0]
  exact key

/-! ## Exact rational certificates appearing verbatim in the paper

Each of these is a finite exact-rational (or integer) inequality asserted in the
paper; `norm_num` reproduces it in the kernel. -/

/-- **Paper §Degree nine.**  `m₉ = 681/1000 < 2 sin(π/9)` is certified by
`3 - (3m₉ - m₉³)² = 16853534459219919/10¹⁸ > 0`. -/
theorem m9_cubic_certificate :
    3 - (3 * (681 / 1000 : ℚ) - (681 / 1000 : ℚ) ^ 3) ^ 2
      = 16853534459219919 / 10 ^ 18 := by
  norm_num

/-- **Paper §Degree ten.**  `m₁₀ = 309/500 < 2 sin(π/10) = (√5-1)/2` is equivalent
to `(2 m₁₀ + 1)² < 5`. -/
theorem m10_certificate : (2 * (309 / 500 : ℚ) + 1) ^ 2 < 5 := by norm_num

/-- **Paper §Degree ten.**  For `0 ≤ a ≤ 29/100` the product inequality fails:
`(129/100)⁹ < 10`. -/
theorem degree10_small_a_product : ((129 / 100 : ℚ)) ^ 9 < 10 := by norm_num

/-- **Paper §Degree eleven.**  For `0 ≤ a ≤ 27/100` the product inequality fails:
`(127/100)¹⁰ < 11`. -/
theorem degree11_small_a_product : ((127 / 100 : ℚ)) ^ 10 < 11 := by norm_num

/-- **Paper §Degree nine, boundary.**  The exact integer inequality
`200² · 19⁹ < 1629² · 10¹⁰`. -/
theorem degree9_boundary_integer : (200 : ℕ) ^ 2 * 19 ^ 9 < 1629 ^ 2 * 10 ^ 10 := by
  norm_num

set_option linter.unusedVariables false in
/-- **Paper §Degree nine, interval `[0, 9/20]`.**  With `S₀ = 1101/200`, the
quadratic `S₀a² - 8a + 8 - S₀` is bounded below on `[0, 9/20]` by its value
`781/80000` at the right endpoint, so localization forces `u > 1` there. -/
theorem degree9_small_a_quadratic {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 9 / 20) :
    (781 : ℝ) / 80000 ≤ (1101 / 200 : ℝ) * a ^ 2 - 8 * a + 8 - 1101 / 200 := by
  nlinarith [h0, mul_nonneg (by linarith : (0 : ℝ) ≤ 9 / 20 - a)
    (by linarith : (0 : ℝ) ≤ 8 - 1101 / 200 * (a + 9 / 20))]

end Sendov911

#print axioms Sendov911.bern_nonneg
#print axioms Sendov911.sum_bern
#print axioms Sendov911.bernstein_lower_bound
#print axioms Sendov911.bernstein_lower_bound_univariate
#print axioms Sendov911.bernstein_positive
#print axioms Sendov911.quadratic_bernstein
#print axioms Sendov911.affine_to_unit_square
#print axioms Sendov911.degree9_small_a_certificate
#print axioms Sendov911.localization_identity
#print axioms Sendov911.localization_ge_one
#print axioms Sendov911.bad_at_one_impossible
#print axioms Sendov911.centered_variance
#print axioms Sendov911.scalar_bound
#print axioms Sendov911.m9_cubic_certificate
#print axioms Sendov911.m10_certificate
#print axioms Sendov911.degree10_small_a_product
#print axioms Sendov911.degree11_small_a_product
#print axioms Sendov911.degree9_boundary_integer
#print axioms Sendov911.degree9_small_a_quadratic
