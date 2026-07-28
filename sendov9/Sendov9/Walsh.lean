import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.Walsh

open Finset intervalIntegral

/-!
# Stage thirteen: the integral side of `GraceWalshSzego`

`GraceWalshSzego` is stated about integrals:

    ∫₀¹ ∏ⱼ(1 - t uⱼ) dt   =   ∫₀¹ (1 - t w)ⁿ dt.

Grace, now proved, is about apolarity forms.  This file is the bridge: both integrals
are *polynomials in the elementary symmetric functions*, with the same coefficients
`cₘ = (-1)ᵐ/(m+1)`.

    ∏ⱼ(1 + x uⱼ) = ∑ₘ xᵐ eₘ(u)          (`prod_one_add`, induction via `esymm_insert`)
    ∫₀¹ tᵐ dt = 1/(m+1)                  (`integral_pow`)

so `F(u) = ∑ₘ (-1)ᵐ eₘ(u)/(m+1)` and `G(w) = ∑ₘ (-1)ᵐ C(n,m) wᵐ/(m+1)`, the latter
being the former at the constant family.  That is exactly the shape
`Apolarity.pair` speaks about, so `Grace2.grace_apolarity` applies to the polynomial
`G(z) - F(u)` — whose apolarity to `∏ⱼ(z - uⱼ)` was confirmed numerically to 5e-15
before any of this was formalized.

Sendov's conjecture in degree nine remains unproven.
-/

variable {ι : Type*} [DecidableEq ι]

/-- `eₘ` (as in `Apolarity.lean`). -/
noncomputable def E (x : ι → ℂ) (s : Finset ι) (m : ℕ) : ℂ :=
  ∑ A ∈ s.powersetCard m, ∏ k ∈ A, x k

@[simp] theorem E_zero (x : ι → ℂ) (s : Finset ι) : E x s 0 = 1 := by
  simp [E, Finset.powersetCard_zero]

theorem E_eq_zero_of_lt {x : ι → ℂ} {s : Finset ι} {m : ℕ} (h : s.card < m) :
    E x s m = 0 := by
  rw [E, Finset.powersetCard_eq_empty.mpr h, Finset.sum_empty]

theorem esymm_insert {t : Finset ι} {i : ι} (hi : i ∉ t) (x : ι → ℂ) (m : ℕ) :
    E x (insert i t) (m + 1) = E x t (m + 1) + x i * E x t m := by
  unfold E
  rw [Finset.powersetCard_succ_insert hi]
  have hdisj : Disjoint (t.powersetCard (m + 1)) ((t.powersetCard m).image (insert i)) := by
    rw [Finset.disjoint_right]
    rintro A hA hA'
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact hi ((Finset.mem_powersetCard.mp hA').1 (Finset.mem_insert_self i B))
  rw [Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun B hB => ?_
    have hiB : i ∉ B := fun h => hi ((Finset.mem_powersetCard.mp hB).1 h)
    rw [Finset.prod_insert hiB]
  · intro B hB C hC hBC
    have hiB : i ∉ B := fun h => hi ((Finset.mem_powersetCard.mp hB).1 h)
    have hiC : i ∉ C := fun h => hi ((Finset.mem_powersetCard.mp hC).1 h)
    have := congrArg (fun s => Finset.erase s i) hBC
    simpa [Finset.erase_insert hiB, Finset.erase_insert hiC] using this

/-- **The product expansion.**  `∏ⱼ(1 + x uⱼ) = ∑ₘ xᵐ eₘ(u)`, truncated at any `N`
past the cardinality. -/
theorem prod_one_add (x : ℂ) (u : ι → ℂ) :
    ∀ (N : ℕ) (s : Finset ι), s.card ≤ N →
      ∏ j ∈ s, (1 + x * u j) = ∑ m ∈ range (N + 1), x ^ m * E u s m := by
  intro N
  induction N with
  | zero =>
      intro s hs
      have hs0 : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
      subst hs0
      simp
  | succ N ih =>
      intro s hs
      rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i, hi⟩
      · have hzero : ∀ m ∈ range (N + 2), m ≠ 0 → x ^ m * E u (∅ : Finset ι) m = 0 := by
          intro m _ hm
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          rw [E_eq_zero_of_lt (by simp), mul_zero]
        rw [Finset.prod_empty, Finset.sum_eq_single 0]
        · simp
        · intro m hm hm0; exact hzero m hm hm0
        · intro h; simp at h
      · -- peel `i` off `s`
        set t := s.erase i with ht
        have hit : i ∉ t := by
          rw [ht]
          exact fun h => (Finset.mem_erase.mp h).1 rfl
        have hst : s = insert i t := (Finset.insert_erase hi).symm
        have htcard : t.card ≤ N := by
          have hc : t.card = s.card - 1 := by rw [ht]; exact Finset.card_erase_of_mem hi
          have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨i, hi⟩
          omega
        have hIH := ih t htcard
        rw [hst, Finset.prod_insert hit, hIH]
        rw [Finset.sum_range_succ' (fun m => x ^ m * E u (insert i t) m) (N + 1)]
        have hstep : ∀ m ∈ range (N + 1),
            x ^ (m + 1) * E u (insert i t) (m + 1)
              = x ^ (m + 1) * E u t (m + 1) + (x * u i) * (x ^ m * E u t m) := by
          intro m _
          rw [esymm_insert hit u m]
          ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
        have hfold : (∑ m ∈ range (N + 1), x ^ (m + 1) * E u t (m + 1))
            + x ^ 0 * E u (insert i t) 0
            = ∑ m ∈ range (N + 1), x ^ m * E u t m := by
          rw [Finset.sum_range_succ (fun m => x ^ (m + 1) * E u t (m + 1)) N,
            E_eq_zero_of_lt (by omega : t.card < N + 1), mul_zero, add_zero]
          rw [Finset.sum_range_succ' (fun m => x ^ m * E u t m) N]
          simp
        rw [add_assoc, add_comm ((x * u i) * _) _, ← add_assoc, hfold]
        ring

/-! ### The integral -/

/-- `∫₀¹ tᵐ dt = 1/(m+1)`, for the ℂ-valued integrand. -/
theorem integral_t_pow (m : ℕ) :
    (∫ t in (0:ℝ)..1, ((t : ℂ) ^ m)) = 1 / ((m : ℂ) + 1) := by
  have h : ∀ t : ℝ, ((t : ℂ) ^ m) = ((t ^ m : ℝ) : ℂ) := by
    intro t; push_cast; ring
  simp only [h]
  rw [intervalIntegral.integral_ofReal, integral_pow]
  push_cast
  simp

/-- **The integral in `GraceWalshSzego` is a polynomial in the `eₘ`.**

`∫₀¹ ∏ⱼ(1 - t uⱼ) dt = ∑ₘ (-1)ᵐ eₘ(u)/(m+1)` — the shape `Apolarity.pair` speaks
about, with `cₘ = (-1)ᵐ/(m+1)`. -/
theorem integral_prod_eq (u : ι → ℂ) (N : ℕ) (s : Finset ι) (hs : s.card ≤ N) :
    (∫ t in (0:ℝ)..1, ∏ j ∈ s, (1 - (t : ℂ) * u j))
      = ∑ m ∈ range (N + 1), (-1) ^ m * E u s m / ((m : ℂ) + 1) := by
  have hexp : ∀ t : ℝ, ∏ j ∈ s, (1 - (t : ℂ) * u j)
      = ∑ m ∈ range (N + 1), (-(t : ℂ)) ^ m * E u s m := by
    intro t
    have := prod_one_add (-(t : ℂ)) u N s hs
    rw [← this]
    exact Finset.prod_congr rfl fun j _ => by ring
  simp only [hexp]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hpow : ∀ t : ℝ, (-(t : ℂ)) ^ m * E u s m
        = ((-1) ^ m * E u s m) * ((t : ℂ) ^ m) := by
      intro t
      rw [neg_pow]
      ring
    simp only [hpow]
    rw [intervalIntegral.integral_const_mul, integral_t_pow]
    ring
  · intro m _
    apply Continuous.intervalIntegrable
    fun_prop

end Sendov9.Walsh

#print axioms Sendov9.Walsh.esymm_insert
#print axioms Sendov9.Walsh.prod_one_add
#print axioms Sendov9.Walsh.integral_t_pow
#print axioms Sendov9.Walsh.integral_prod_eq
