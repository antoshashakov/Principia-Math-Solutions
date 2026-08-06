import Mathlib
import SendovNSigma

set_option maxHeartbeats 4000000

/-!
# P6 (partial): the Newton bridge and the *easy* `c_m` cases — `e₂`, `e₃`, `e_N`

The hard half of P6 (the Cauchy coefficient estimate via roots-of-unity extraction,
for `4 ≤ m ≤ N−1`) is **not** attempted here — it is one of the plan's three genuinely
creative pieces. This file banks the parts the plan marks easy:

* the generic `MvPolynomial → concrete family` Newton bridge (verbatim from
  `Sendov9/NewtonWiring.lean`, which was already parametric in `ι`);
* `e2_bound` : `‖e₂‖ ≤ (N/2)·η²`  (centred Newton at order 2);
* `e3_bound` : `‖e₃‖ ≤ N·η³` for `N ≤ 10`  (via `max‖Dⱼ‖² ≤ (N−1)V/N` — the plan's
  improved route; the degree-9 `√V` route fails at `N = 10`);
* `eN_bound` : `‖e_N‖ ≤ η^N`  (AM–GM over the `N` factors).

These give `c₂ = 9/2, c₃ = 9, c₉ = 1` at `N = 9` and `c₂ = 5, c₃ = 10, c₁₀ = 1`
at `N = 10` — six of the seventeen entries of the two `c`-tables.
-/

namespace SendovN.Newton

open Finset MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- `eₙ` of a concrete family (same shape as `SendovN.esD`). -/
noncomputable def e (x : ι → R) (n : ℕ) : R := ∑ t ∈ powersetCard n univ, ∏ i ∈ t, x i

/-- `pₙ` of a concrete family. -/
def p (x : ι → R) (n : ℕ) : R := ∑ i, x i ^ n

/-- `aeval` sends the formal elementary symmetric polynomial to the concrete one. -/
theorem aeval_esymm (x : ι → R) (n : ℕ) :
    aeval x (MvPolynomial.esymm ι R n) = e x n := by
  simp [MvPolynomial.esymm, e]

/-- `aeval` sends the formal power sum to the concrete one. -/
theorem aeval_psum (x : ι → R) (n : ℕ) :
    aeval x (MvPolynomial.psum ι R n) = p x n := by
  simp [MvPolynomial.psum, p]

@[simp] theorem e_zero (x : ι → R) : e x 0 = 1 := by simp [e]

theorem e_one (x : ι → R) : e x 1 = ∑ i, x i := by simp [e, Finset.powersetCard_one]

theorem p_one (x : ι → R) : p x 1 = ∑ i, x i := by simp [p]

/-- The filtered antidiagonal in Newton's identity is just `range k`. -/
theorem sum_filter_antidiagonal {M : Type*} [AddCommMonoid M] (k : ℕ) (f : ℕ × ℕ → M) :
    ∑ a ∈ antidiagonal k with a.1 < k, f a = ∑ j ∈ range k, f (j, k - j) := by
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [lt_irrefl, if_false, add_zero]
  exact Finset.sum_congr rfl fun j hj => if_pos (Finset.mem_range.mp hj)

/-- **Newton's identities, transported to a concrete family.** -/
theorem newton (x : ι → R) (k : ℕ) :
    (k : R) * e x k
      = (-1) ^ (k + 1) * ∑ j ∈ range k, (-1) ^ j * e x j * p x (k - j) := by
  have h := congrArg (aeval (R := R) x) (MvPolynomial.mul_esymm_eq_sum ι R k)
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
    aeval_esymm, aeval_psum] at h
  rw [sum_filter_antidiagonal] at h
  exact h

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

/-- **Centred Newton at order 4.**  `8e₄ = p₂² − 2p₄`. -/
theorem newton_four_centred (hz : ∑ i, x i = 0) :
    8 * e x 4 = p x 2 ^ 2 - 2 * p x 4 := by
  have h4 := newton_four x
  rw [e_one, p_one, hz, zero_mul, mul_zero] at h4
  have h2 := e_two_centred x hz
  linear_combination 2 * h4 - p x 2 * h2

end SendovN.Newton

namespace SendovN.EspEasy

open Finset

variable {N : ℕ}

/-- Triangle inequality for a power sum. -/
theorem norm_power_sum_le (D : Fin N → ℂ) (k : ℕ) :
    ‖∑ j, (D j) ^ k‖ ≤ ∑ j, ‖D j‖ ^ k := by
  calc ‖∑ j, (D j) ^ k‖ ≤ ∑ j, ‖(D j) ^ k‖ := norm_sum_le _ _
    _ = ∑ j, ‖D j‖ ^ k := by simp [norm_pow]

/-- **`‖e₂‖ ≤ (N/2)·η²`** — the `c₂` entry, from centred Newton at order 2. -/
theorem e2_bound (D : Fin N → ℂ) (eta : ℝ)
    (hz : ∑ j, D j = 0) (hD : ∑ j, ‖D j‖ ^ 2 ≤ (N : ℝ) * eta ^ 2) :
    ‖esD D 2‖ ≤ (N : ℝ) / 2 * eta ^ 2 := by
  have h2 : 2 * esD D 2 = -(∑ j, (D j) ^ 2) := Newton.e_two_centred D hz
  have hn : ‖(2 : ℂ) * esD D 2‖ = 2 * ‖esD D 2‖ := by
    rw [norm_mul]; norm_num
  have hb : ‖∑ j, (D j) ^ 2‖ ≤ (N : ℝ) * eta ^ 2 :=
    le_trans (norm_power_sum_le D 2) hD
  have hle : 2 * ‖esD D 2‖ ≤ (N : ℝ) * eta ^ 2 := by
    rw [← hn, h2, norm_neg]; exact hb
  linarith

/-- The centred max-coordinate bound: `N·‖Dⱼ‖² ≤ (N−1)·∑‖Dₖ‖²` for every `j`. -/
theorem max_coord_sq_le (D : Fin N → ℂ) (hz : ∑ j, D j = 0) (j : Fin N) :
    (N : ℝ) * ‖D j‖ ^ 2 ≤ ((N : ℝ) - 1) * ∑ k, ‖D k‖ ^ 2 := by
  -- `Dⱼ = −∑_{k ≠ j} Dₖ`
  have hsum : ∑ k ∈ univ.erase j, D k = -(D j) := by
    have h := Finset.sum_erase_add univ D (Finset.mem_univ j)
    rw [hz] at h
    linear_combination h
  have hcard : (univ.erase j).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j)]
    simp
  -- Cauchy–Schwarz on the erased sum
  have hcs : (∑ k ∈ univ.erase j, ‖D k‖) ^ 2
      ≤ ((univ.erase j).card : ℝ) * ∑ k ∈ univ.erase j, ‖D k‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (univ.erase j)
      (fun _ => (1 : ℝ)) (fun k => ‖D k‖)
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have htri : ‖D j‖ ≤ ∑ k ∈ univ.erase j, ‖D k‖ := by
    calc ‖D j‖ = ‖∑ k ∈ univ.erase j, D k‖ := by rw [hsum, norm_neg]
      _ ≤ ∑ k ∈ univ.erase j, ‖D k‖ := norm_sum_le _ _
  have herase : ∑ k ∈ univ.erase j, ‖D k‖ ^ 2 = (∑ k, ‖D k‖ ^ 2) - ‖D j‖ ^ 2 := by
    have h := Finset.sum_erase_add univ (fun k => ‖D k‖ ^ 2) (Finset.mem_univ j)
    linarith [h]
  have hN1 : ((univ.erase j).card : ℝ) = (N : ℝ) - 1 := by
    rw [hcard]
    have hpos : 1 ≤ N := Fin.pos j
    push_cast [Nat.cast_sub hpos]
    ring
  have hDj2 : ‖D j‖ ^ 2 ≤ ((N : ℝ) - 1) * ((∑ k, ‖D k‖ ^ 2) - ‖D j‖ ^ 2) := by
    have h1 : ‖D j‖ ^ 2 ≤ (∑ k ∈ univ.erase j, ‖D k‖) ^ 2 := by
      have hnn : (0 : ℝ) ≤ ∑ k ∈ univ.erase j, ‖D k‖ :=
        Finset.sum_nonneg fun k _ => norm_nonneg _
      nlinarith [htri, norm_nonneg (D j)]
    calc ‖D j‖ ^ 2 ≤ (∑ k ∈ univ.erase j, ‖D k‖) ^ 2 := h1
      _ ≤ ((univ.erase j).card : ℝ) * ∑ k ∈ univ.erase j, ‖D k‖ ^ 2 := hcs
      _ = ((N : ℝ) - 1) * ((∑ k, ‖D k‖ ^ 2) - ‖D j‖ ^ 2) := by rw [hN1, herase]
  nlinarith [hDj2]

/-- **`‖e₃‖ ≤ N·η³`** for `N ≤ 10` — the `c₃` entry, via the improved
`max‖Dⱼ‖ ≤ √(N−1)·η` route (the plan's Part 3 `m = 3` recipe). -/
theorem e3_bound (hN10 : N ≤ 10) (D : Fin N → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hz : ∑ j, D j = 0) (hD : ∑ j, ‖D j‖ ^ 2 ≤ (N : ℝ) * eta ^ 2) :
    ‖esD D 3‖ ≤ (N : ℝ) * eta ^ 3 := by
  have hV0 : (0 : ℝ) ≤ ∑ k, ‖D k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => by positivity
  set B : ℝ := Real.sqrt ((N : ℝ) - 1) * eta with hB
  have hB0 : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) heta
  -- every coordinate is bounded by `B`
  have hcoord : ∀ j : Fin N, ‖D j‖ ≤ B := by
    intro j
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have := Fin.pos j
      exact_mod_cast this
    have h1 := max_coord_sq_le D hz j
    have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by
      have h1N : 1 ≤ N := Fin.pos j
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1N
      linarith
    have h2 : ‖D j‖ ^ 2 ≤ ((N : ℝ) - 1) * eta ^ 2 := by
      have h3 : (N : ℝ) * ‖D j‖ ^ 2 ≤ ((N : ℝ) - 1) * ((N : ℝ) * eta ^ 2) :=
        le_trans h1 (mul_le_mul_of_nonneg_left hD hN1)
      have h4 : ((N : ℝ) - 1) * ((N : ℝ) * eta ^ 2)
          = (N : ℝ) * (((N : ℝ) - 1) * eta ^ 2) := by ring
      rw [h4] at h3
      exact le_of_mul_le_mul_left h3 hNpos
    have hBsq : B ^ 2 = ((N : ℝ) - 1) * eta ^ 2 := by
      rw [hB, mul_pow, Real.sq_sqrt hN1]
    have := Real.sqrt_le_sqrt (hBsq ▸ h2)
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hB0] at this
  -- `∑‖D‖³ ≤ B·V ≤ B·N·η²`
  have hcube : ∑ j, ‖D j‖ ^ 3 ≤ B * ((N : ℝ) * eta ^ 2) := by
    calc ∑ j, ‖D j‖ ^ 3 ≤ ∑ j, B * ‖D j‖ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          calc ‖D j‖ ^ 3 = ‖D j‖ * ‖D j‖ ^ 2 := by ring
            _ ≤ B * ‖D j‖ ^ 2 :=
                mul_le_mul_of_nonneg_right (hcoord j) (by positivity)
      _ = B * ∑ j, ‖D j‖ ^ 2 := by rw [← Finset.mul_sum]
      _ ≤ B * ((N : ℝ) * eta ^ 2) := mul_le_mul_of_nonneg_left hD hB0
  -- `3‖e₃‖ = ‖p₃‖`
  have h3 : 3 * esD D 3 = ∑ j, (D j) ^ 3 := Newton.newton_three_centred D hz
  have h3n : 3 * ‖esD D 3‖ = ‖∑ j, (D j) ^ 3‖ := by
    rw [← h3, norm_mul]
    norm_num
  -- `√(N−1) ≤ 3` for `N ≤ 10`
  have hsq3 : Real.sqrt ((N : ℝ) - 1) ≤ 3 := by
    have hle : (N : ℝ) - 1 ≤ 9 := by
      have : (N : ℝ) ≤ 10 := by exact_mod_cast hN10
      linarith
    calc Real.sqrt ((N : ℝ) - 1) ≤ Real.sqrt 9 := Real.sqrt_le_sqrt hle
      _ = 3 := by
          rw [show (9 : ℝ) = 3 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
  have hp3 : ‖∑ j, (D j) ^ 3‖ ≤ B * ((N : ℝ) * eta ^ 2) :=
    le_trans (norm_power_sum_le D 3) hcube
  have hBle : B * ((N : ℝ) * eta ^ 2) ≤ 3 * ((N : ℝ) * eta ^ 3) := by
    have hNn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hexp : B * ((N : ℝ) * eta ^ 2)
        = Real.sqrt ((N : ℝ) - 1) * ((N : ℝ) * eta ^ 3) := by
      rw [hB]; ring
    have hexp2 : (3 : ℝ) * ((N : ℝ) * eta ^ 3) = 3 * ((N : ℝ) * eta ^ 3) := rfl
    rw [hexp]
    exact mul_le_mul_of_nonneg_right hsq3 (by positivity)
  linarith [hp3, h3n, hBle]

/-- **`‖e_N‖ ≤ η^N`** — the top entry `c_N = 1`, by AM–GM over the `N` factors. -/
theorem eN_bound (hN : 1 ≤ N) (D : Fin N → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hD : ∑ j, ‖D j‖ ^ 2 ≤ (N : ℝ) * eta ^ 2) :
    ‖esD D N‖ ≤ eta ^ N := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : ((N : ℕ) : ℝ) ≠ 0 := ne_of_gt hNR
  -- `e_N` is the full product
  have hpc : (univ : Finset (Fin N)).powersetCard N = {univ} := by
    ext s
    simp only [Finset.mem_powersetCard, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hcard⟩
      apply Finset.eq_univ_of_card
      simpa using hcard
    · rintro rfl
      exact ⟨subset_rfl, by simp⟩
  have hprod : esD D N = ∏ j, D j := by
    unfold esD
    rw [hpc, Finset.sum_singleton]
  -- AM–GM on the squared norms
  have hz : ∀ j ∈ (univ : Finset (Fin N)), (0 : ℝ) ≤ ‖D j‖ ^ 2 := fun j _ => by positivity
  have hw : ∀ j ∈ (univ : Finset (Fin N)), (0 : ℝ) ≤ 1 / (N : ℝ) := fun j _ => by positivity
  have hw1 : ∑ _j : Fin N, (1 / (N : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hamgm := Real.geom_mean_le_arith_mean_weighted univ (fun _ => 1 / (N : ℝ))
    (fun j => ‖D j‖ ^ 2) hw hw1 hz
  -- LHS: `∏ (‖Dⱼ‖²)^(1/N) = (∏‖Dⱼ‖²)^(1/N)`
  set X : ℝ := ∏ j, ‖D j‖ ^ 2 with hX
  have hX0 : 0 ≤ X := Finset.prod_nonneg fun j _ => by positivity
  have hlhs : ∏ j, (‖D j‖ ^ 2) ^ (1 / (N : ℝ) : ℝ) = X ^ (1 / (N : ℝ) : ℝ) := by
    rw [hX, ← Real.finset_prod_rpow univ _ (fun j _ => by positivity) _]
  -- RHS: `∑ (1/N)·‖Dⱼ‖² ≤ η²`
  have hrhs : ∑ j, (1 / (N : ℝ)) * ‖D j‖ ^ 2 ≤ eta ^ 2 := by
    rw [← Finset.mul_sum]
    calc (1 / (N : ℝ)) * ∑ j, ‖D j‖ ^ 2
        ≤ (1 / (N : ℝ)) * ((N : ℝ) * eta ^ 2) :=
          mul_le_mul_of_nonneg_left hD (by positivity)
      _ = eta ^ 2 := by field_simp
  have h1 : X ^ (1 / (N : ℝ) : ℝ) ≤ eta ^ 2 := by
    rw [← hlhs]
    exact le_trans hamgm hrhs
  -- raise to the `N`-th power
  have h2 : X ≤ (eta ^ 2) ^ N := by
    have h3 : (X ^ (1 / (N : ℝ) : ℝ)) ^ N ≤ (eta ^ 2) ^ N :=
      pow_le_pow_left₀ (Real.rpow_nonneg hX0 _) h1 N
    rwa [← Real.rpow_natCast (X ^ (1 / (N : ℝ) : ℝ)) N, ← Real.rpow_mul hX0,
      one_div, inv_mul_cancel₀ hNne, Real.rpow_one] at h3
  -- conclude on the un-squared product
  have hprodsq : (∏ j, ‖D j‖) ^ 2 = X := by
    rw [hX, ← Finset.prod_pow]
  have hfin : ∏ j, ‖D j‖ ≤ eta ^ N := by
    have h4 : (∏ j, ‖D j‖) ^ 2 ≤ (eta ^ N) ^ 2 := by
      rw [hprodsq]
      calc X ≤ (eta ^ 2) ^ N := h2
        _ = (eta ^ N) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have h5 := Real.sqrt_le_sqrt h4
    rwa [Real.sqrt_sq (Finset.prod_nonneg fun j _ => norm_nonneg _),
      Real.sqrt_sq (by positivity)] at h5
  calc ‖esD D N‖ = ∏ j, ‖D j‖ := by rw [hprod, Complex.norm_prod]
    _ ≤ eta ^ N := hfin

end SendovN.EspEasy

#print axioms SendovN.Newton.newton
#print axioms SendovN.Newton.e_two_centred
#print axioms SendovN.Newton.newton_three_centred
#print axioms SendovN.Newton.newton_four_centred
#print axioms SendovN.EspEasy.e2_bound
#print axioms SendovN.EspEasy.max_coord_sq_le
#print axioms SendovN.EspEasy.e3_bound
#print axioms SendovN.EspEasy.eN_bound
