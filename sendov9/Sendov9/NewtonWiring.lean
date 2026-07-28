import Mathlib

set_option maxHeartbeats 4000000


set_option maxHeartbeats 4000000

namespace Sendov9.Newton

open Finset MvPolynomial

/-!
# Discharging `NewtonCentred`: the `MvPolynomial` → `Fin 8` bridge

`EmBounds.lean` carries

```
NewtonCentred : ∀ D : Fin 8 → ℂ, ∑ j, D j = 0 →
  3·e₃(D) = p₃(D)  ∧  4·e₄(D) = p₂(D)²/2 - p₄(D)
```

as a hypothesis.  Mathlib *does* have Newton's identities, but only for
`MvPolynomial σ R` — as an identity between formal polynomials, not between numbers.
The gap is one `aeval`.

The bridge is cheap because both `MvPolynomial.esymm` and `MvPolynomial.psum` are
*defined* in exactly the shape a concrete family wants:

    esymm σ R n = ∑ t ∈ powersetCard n univ, ∏ i ∈ t, X i
    psum  σ R n = ∑ i, X i ^ n

so `aeval x` commutes straight through the sums and products (`aeval_esymm`,
`aeval_psum` below).  Everything after that is bookkeeping: instantiate
`mul_esymm_eq_sum` at `k = 2,3,4`, turn the filtered antidiagonal into a `range` sum,
and substitute `e₁ = p₁ = 0`.

Note `newton_two/three/four` are stated over an arbitrary `CommRing` — the centring
hypothesis is what specialises them.  `e₄` is stated as `8·e₄ = p₂² - 2p₄` there
because a general `CommRing` cannot divide by two; the `/2` form is recovered over `ℂ`
at the end.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- `eₙ` of a concrete family (same shape as `EmBounds.esD`). -/
noncomputable def e (x : ι → R) (n : ℕ) : R := ∑ t ∈ powersetCard n univ, ∏ i ∈ t, x i

/-- `pₙ` of a concrete family. -/
def p (x : ι → R) (n : ℕ) : R := ∑ i, x i ^ n

/-! ### The bridge -/

/-- `aeval` sends the formal elementary symmetric polynomial to the concrete one. -/
theorem aeval_esymm (x : ι → R) (n : ℕ) : aeval x (MvPolynomial.esymm ι R n) = e x n := by
  simp [MvPolynomial.esymm, e]

/-- `aeval` sends the formal power sum to the concrete one. -/
theorem aeval_psum (x : ι → R) (n : ℕ) : aeval x (MvPolynomial.psum ι R n) = p x n := by
  simp [MvPolynomial.psum, p]

@[simp] theorem e_zero (x : ι → R) : e x 0 = 1 := by simp [e]

theorem e_one (x : ι → R) : e x 1 = ∑ i, x i := by simp [e, Finset.powersetCard_one]

theorem p_one (x : ι → R) : p x 1 = ∑ i, x i := by simp [p]

/-- The filtered antidiagonal in Newton's identity is just `range k`: the only pair with
`a.1 ≥ k` is `(k, 0)`, which the filter drops. -/
theorem sum_filter_antidiagonal {M : Type*} [AddCommMonoid M] (k : ℕ) (f : ℕ × ℕ → M) :
    ∑ a ∈ antidiagonal k with a.1 < k, f a = ∑ j ∈ range k, f (j, k - j) := by
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [lt_irrefl, if_false, add_zero]
  exact Finset.sum_congr rfl fun j hj => if_pos (Finset.mem_range.mp hj)

/-- **Newton's identities, transported to a concrete family.**  This is
`MvPolynomial.mul_esymm_eq_sum` under `aeval`, with the antidiagonal flattened. -/
theorem newton (x : ι → R) (k : ℕ) :
    (k : R) * e x k
      = (-1) ^ (k + 1) * ∑ j ∈ range k, (-1) ^ j * e x j * p x (k - j) := by
  have h := congrArg (aeval (R := R) x) (MvPolynomial.mul_esymm_eq_sum ι R k)
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
    aeval_esymm, aeval_psum] at h
  rw [sum_filter_antidiagonal] at h
  exact h

/-! ### The three orders we need -/

theorem newton_two (x : ι → R) : 2 * e x 2 = e x 1 * p x 1 - p x 2 := by
  have h := newton x 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
  simp only [e_zero, pow_zero, pow_one, one_mul, zero_add] at h
  push_cast at h
  linear_combination h

theorem newton_three (x : ι → R) :
    3 * e x 3 = p x 3 - e x 1 * p x 2 + e x 2 * p x 1 := by
  have h := newton x 3
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero] at h
  simp only [e_zero, pow_zero, pow_one, one_mul, zero_add] at h
  push_cast at h
  linear_combination h

theorem newton_four (x : ι → R) :
    4 * e x 4 = -p x 4 + e x 1 * p x 3 - e x 2 * p x 2 + e x 3 * p x 1 := by
  have h := newton x 4
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero] at h
  simp only [e_zero, pow_zero, pow_one, one_mul, zero_add] at h
  push_cast at h
  linear_combination h

/-! ### Centring

`∑ xᵢ = 0` kills `e₁` and `p₁` simultaneously, which is the whole point: `3e₃` loses its
correction term outright, and `4e₄` keeps only `-e₂p₂`, where `2e₂ = -p₂`. -/

variable (x : ι → R)

theorem e_two_centred (hz : ∑ i, x i = 0) : 2 * e x 2 = -p x 2 := by
  have h := newton_two x
  rw [e_one, hz, zero_mul] at h
  linear_combination h

/-- **Centred Newton at order 3.**  `3e₃ = p₃`. -/
theorem newton_three_centred (hz : ∑ i, x i = 0) : 3 * e x 3 = p x 3 := by
  have h := newton_three x
  rw [e_one, p_one, hz, zero_mul, mul_zero] at h
  linear_combination h

/-- **Centred Newton at order 4.**  `8e₄ = p₂² - 2p₄` (the `/2`-free form). -/
theorem newton_four_centred (hz : ∑ i, x i = 0) :
    8 * e x 4 = p x 2 ^ 2 - 2 * p x 4 := by
  have h4 := newton_four x
  rw [e_one, p_one, hz, zero_mul, mul_zero] at h4
  have h2 := e_two_centred x hz
  -- 4e₄ = -p₄ - e₂p₂ and 2e₂ = -p₂, so 8e₄ = -2p₄ - (2e₂)p₂ = -2p₄ + p₂²
  linear_combination 2 * h4 - p x 2 * h2

end Sendov9.Newton



set_option maxHeartbeats 4000000

namespace Sendov9.Em

open Finset

/-!
# The `eₘ` bounds (equation 3.8), and why two identities are carried

The paper's constants are `(c₂,…,c₈) = (4, 264/35, 24, 56, 28, 8, 1)`.  Their origin
splits three ways:

* `m = 2`  — `e₂ = -p₂/2` from `∑Dⱼ = 0`.  **Proved** (`Stage2bc.lean`).
* `m = 3, 4` — Newton's identities `3e₃ = p₃` and `4e₄ = p₂²/2 - p₄`, again using
  `∑Dⱼ = 0`.  **Carried as `NewtonCentred`**, see below.
* `m ≥ 5`  — Maclaurin applied to `|D₁|,…,|D₈|` then Cauchy–Schwarz.  **Carried as
  `MaclaurinIneq`.**

## Why `m = 3, 4` cannot fall back on Maclaurin

Maclaurin alone gives `e₃ ≤ C(8,3)η³ = 56η³` and `e₄ ≤ C(8,4)η⁴ = 70η⁴`, against the
`264/35 ≈ 7.54` and `24` the certificates were built with — factors of 7.4 and 2.9.
The sharper route through `S₂` is *worse* (`68.4η³` at `m = 3`), because
`e₂(|D|) ≤ 32η²` loses exactly the cancellation that centring provides.  So the
`∑Dⱼ = 0` cancellation is load-bearing at `m = 3, 4`, not a convenience, and the
constants cannot be weakened without regenerating all 19 certificates — which at a
0.16% margin they would not survive.

Mathlib's Newton identities live in `MvPolynomial` and need an `aeval` bridge to a
concrete `Fin 8` family; that bridge is the honest remaining work here.  Carrying the
two identities as an explicit hypothesis keeps the footprint at
`[propext, Classical.choice, Quot.sound]` and states the boundary where a reader sees it.
-/

/-- The `m`-th elementary symmetric function, as in `Sigma22.lean`. -/
noncomputable def esD (D : Fin 8 → ℂ) (m : ℕ) : ℂ :=
  ∑ s ∈ (univ : Finset (Fin 8)).powersetCard m, ∏ j ∈ s, D j

/-- **Carried hypothesis.** Newton's identities for a centred family of eight, at the
two orders where the cancellation is load-bearing.  Elementary and classical; the
`MvPolynomial`→`Fin 8` bridge is the remaining work. -/
def NewtonCentred : Prop :=
  ∀ D : Fin 8 → ℂ, ∑ j, D j = 0 →
    (3 * esD D 3 = ∑ j, (D j) ^ 3) ∧
    (4 * esD D 4 = (∑ j, (D j) ^ 2) ^ 2 / 2 - ∑ j, (D j) ^ 4)

/-- Triangle inequality for a power sum. -/
theorem norm_power_sum_le (D : Fin 8 → ℂ) (k : ℕ) :
    ‖∑ j, (D j) ^ k‖ ≤ ∑ j, ‖D j‖ ^ k := by
  calc ‖∑ j, (D j) ^ k‖ ≤ ∑ j, ‖(D j) ^ k‖ := norm_sum_le _ _
    _ = ∑ j, ‖D j‖ ^ k := by simp [norm_pow]

theorem sum_fourth_le_sq_sq (D : Fin 8 → ℂ) :
    ∑ j, ‖D j‖ ^ 4 ≤ (∑ j, ‖D j‖ ^ 2) ^ 2 := by
  have hnn : ∀ j : Fin 8, (0:ℝ) ≤ ‖D j‖ ^ 2 := fun j => by positivity
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := (univ : Finset (Fin 8)))
    (f := fun j => ‖D j‖ ^ 2) (fun j _ => hnn j)
  calc ∑ j, ‖D j‖ ^ 4 = ∑ j, (‖D j‖ ^ 2) ^ 2 :=
        Finset.sum_congr rfl fun j _ => by ring
    _ ≤ (∑ j, ‖D j‖ ^ 2) ^ 2 := h

/-- **`|e₄| ≤ 24η⁴`**, the paper's `c₄`.  From `4e₄ = p₂²/2 - p₄`:
`|p₂²/2| ≤ 32η⁴` and `|p₄| ≤ (∑|Dⱼ|²)² ≤ 64η⁴`, totalling `96η⁴`. -/
theorem e4_bound (newton : NewtonCentred) (D : Fin 8 → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hz : ∑ j, D j = 0) (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2) :
    ‖esD D 4‖ ≤ 24 * eta ^ 4 := by
  obtain ⟨-, h4⟩ := newton D hz
  have hp2 : ‖∑ j, (D j) ^ 2‖ ≤ 8 * eta ^ 2 :=
    le_trans (norm_power_sum_le D 2) hD
  have hp4 : ‖∑ j, (D j) ^ 4‖ ≤ 64 * eta ^ 4 := by
    have h1 := norm_power_sum_le D 4
    have h2 := sum_fourth_le_sq_sq D
    have hnn : (0:ℝ) ≤ ∑ j, ‖D j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
    nlinarith [h1, h2, hD, hnn]
  have hkey : ‖4 * esD D 4‖ ≤ 96 * eta ^ 4 := by
    rw [h4]
    have hsq : ‖(∑ j, (D j) ^ 2) ^ 2 / 2‖ ≤ 32 * eta ^ 4 := by
      rw [norm_div, norm_pow]
      have : ‖(2:ℂ)‖ = 2 := by norm_num
      rw [this]
      nlinarith [hp2, norm_nonneg (∑ j, (D j) ^ 2)]
    calc ‖(∑ j, (D j) ^ 2) ^ 2 / 2 - ∑ j, (D j) ^ 4‖
        ≤ ‖(∑ j, (D j) ^ 2) ^ 2 / 2‖ + ‖∑ j, (D j) ^ 4‖ := norm_sub_le _ _
      _ ≤ 32 * eta ^ 4 + 64 * eta ^ 4 := by linarith
      _ = 96 * eta ^ 4 := by ring
  have h4n : ‖4 * esD D 4‖ = 4 * ‖esD D 4‖ := by
    rw [norm_mul]; norm_num
  rw [h4n] at hkey
  linarith

/-- **`|e₃| ≤ 264η³/35`**, the paper's `c₃`.  From `3e₃ = p₃`, then
`∑|Dⱼ|³ ≤ (∑|Dⱼ|²)^{3/2} ≤ (8η²)^{3/2} = 16√2 η³`, and `16√2/3 < 264/35`. -/
theorem e3_bound (newton : NewtonCentred) (D : Fin 8 → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hz : ∑ j, D j = 0) (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2) :
    ‖esD D 3‖ ≤ 264 / 35 * eta ^ 3 := by
  obtain ⟨h3, -⟩ := newton D hz
  have hnn : (0:ℝ) ≤ ∑ j, ‖D j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  -- ∑|D|³ ≤ (∑|D|²)^{3/2}, via max ≤ ℓ²-norm
  have hcube : ∑ j, ‖D j‖ ^ 3 ≤ Real.sqrt (∑ i, ‖D i‖ ^ 2) * ∑ j, ‖D j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hle : ‖D j‖ ^ 2 ≤ ∑ i, ‖D i‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ‖D i‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j)
    have h : ‖D j‖ ≤ Real.sqrt (∑ i, ‖D i‖ ^ 2) := by
      calc ‖D j‖ = Real.sqrt (‖D j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ _ := Real.sqrt_le_sqrt hle
    calc ‖D j‖ ^ 3 = ‖D j‖ * ‖D j‖ ^ 2 := by ring
      _ ≤ Real.sqrt (∑ i, ‖D i‖ ^ 2) * ‖D j‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h (by positivity)
  have hs : Real.sqrt (∑ i, ‖D i‖ ^ 2) ≤ Real.sqrt 8 * eta := by
    have := Real.sqrt_le_sqrt hD
    rwa [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8), Real.sqrt_sq heta] at this
  have hsqrt8 : Real.sqrt 8 < 99 / 35 := by
    have h8 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 8, h8]
  have hp3 : ‖∑ j, (D j) ^ 3‖ ≤ Real.sqrt 8 * eta * (8 * eta ^ 2) := by
    refine le_trans (norm_power_sum_le D 3) (le_trans hcube ?_)
    exact mul_le_mul hs hD hnn (by positivity)
  have h3n : ‖3 * esD D 3‖ = 3 * ‖esD D 3‖ := by rw [norm_mul]; norm_num
  rw [h3] at h3n
  -- h3n : ‖∑ⱼ Dⱼ³‖ = 3‖e₃‖.  Scale √8 < 99/35 by 8η³ ≥ 0 explicitly; nlinarith will
  -- not find that product on its own.
  have heta3 : (0:ℝ) ≤ 8 * eta ^ 3 := by positivity
  have hstep : Real.sqrt 8 * eta * (8 * eta ^ 2) ≤ 99 / 35 * (8 * eta ^ 3) := by
    have hre : Real.sqrt 8 * eta * (8 * eta ^ 2) = Real.sqrt 8 * (8 * eta ^ 3) := by ring
    rw [hre]
    exact mul_le_mul_of_nonneg_right (le_of_lt hsqrt8) heta3
  linarith [hp3, h3n, hstep]

end Sendov9.Em



namespace Sendov9.Em

/-- **The carried hypothesis is a theorem.**  `Sendov9.Newton` supplies the
`MvPolynomial`→`Fin 8` bridge; this proves `Sendov9.Em.NewtonCentred` itself, so every
consumer below can be instantiated unconditionally. -/
theorem newtonCentred : NewtonCentred := by
  intro D hz
  have he : ∀ m, esD D m = Sendov9.Newton.e D m := fun m => rfl
  have hp : ∀ m, Sendov9.Newton.p D m = ∑ j, (D j) ^ m := fun m => rfl
  refine ⟨?_, ?_⟩
  · rw [he, ← hp 3]
    exact Sendov9.Newton.newton_three_centred D hz
  · have h := Sendov9.Newton.newton_four_centred D hz
    rw [hp, hp] at h
    rw [he]
    linear_combination h / 2

/-- `e₄` bound, hypothesis-free. -/
theorem e4_bound' (D : Fin 8 → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hz : ∑ j, D j = 0) (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2) :
    ‖esD D 4‖ ≤ 24 * eta ^ 4 :=
  e4_bound newtonCentred D eta heta hz hD

/-- `e₃` bound, hypothesis-free. -/
theorem e3_bound' (D : Fin 8 → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hz : ∑ j, D j = 0) (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2) :
    ‖esD D 3‖ ≤ 264 / 35 * eta ^ 3 :=
  e3_bound newtonCentred D eta heta hz hD

end Sendov9.Em

#print axioms Sendov9.Em.newtonCentred
#print axioms Sendov9.Em.e4_bound'
#print axioms Sendov9.Em.e3_bound'
