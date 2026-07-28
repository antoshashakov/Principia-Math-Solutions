import Mathlib
import Sendov9.Sigma22

set_option maxHeartbeats 4000000

namespace Sendov9.SigmaGen

open Finset Sendov9.Sigma

/-!
# Lemma 2.2, in general form

`Sigma22.of_base` already reduces the σ bound to configurations with at most one
strictly interior coordinate, **parametrically** in `(m, M, C, Bound)`.  What was
missing was the base case: `BaseNumerics.lean` proves it by hand for the single
instance `m = 681/1000`, `M = 29/20`, `C = 9`.

The middle range needs eighteen more instances (`M = 1 + β`, one per row of Table 1)
and the boundary range needs `M = 2`.  Writing nineteen bespoke numeric packages would
be the wrong move; this file proves the base case **once**, parametric in `ν`.

## The argument

Write `h`, `l`, `i` for the number of coordinates at `M`, at `m`, and strictly
interior, so `h + l + i = 8` and `i ≤ 1`.  Then

    ∑ₖ rₖ⁻² = h/M² + l/m² + ∑_{interior}      (`Sigma.sum_split`)
    ∏ₖ rₖ   = M^h · m^l · ∏_{interior}        (`Sigma.prod_split`)

and `ν`'s minimality does all the work through **one** contrapositive: `M^j m^{8-j} < C`
for every `j < ν`, so any configuration whose product clears `C` must have `h` large.

* `i = 0`: `∏ = M^h m^{8-h} ≥ C` forces `h ≥ ν`, and `descent` slides `h` down to `ν`.
  The leftover `1/M² ≤ (K/C)²` is `Sigma.inv_M_sq_le`, whose hypothesis `C ≤ M·K` is
  exactly `C ≤ M^ν m^{8-ν}` — the *other* half of `ν`'s definition.
* `i = 1`, `h ≥ ν`: same, with the interior coordinate absorbed by `1/s² ≤ 1/m²`.
* `i = 1`, `h = ν-1`: **the tight case.**  `M^{ν-1} m^{8-ν} s ≥ C` pins `s ≥ C/K`, so
  `1/s² ≤ (K/C)²` — the third term of the bound, attained.
* `i = 1`, `h ≤ ν-2`: infeasible.  `s < M` gives `∏ < M^{h+1} m^{8-(h+1)}`, and
  `h + 1 < ν` makes that `< C`.

No monotonicity of `j ↦ M^j m^{8-j}` is needed anywhere — `hnu_min` is applied
directly at the `j` in hand, which is what keeps the proof short.

Sendov's conjecture in degree nine remains unproven.
-/

/-- Moving weight from the lower endpoint to the upper one decreases `∑ r⁻²`.

The real-valued form of `Sigma.step_down`: no induction, since the difference is
`(y - x)(1/M² - 1/m²)` outright. -/
theorem descent {m M : ℝ} (hm : 0 < m) (hmM : m < M) (x y N : ℝ) (hxy : x ≤ y) :
    y / M ^ 2 + (N - y) / m ^ 2 ≤ x / M ^ 2 + (N - x) / m ^ 2 := by
  have hM0 : (0:ℝ) < M := lt_trans hm hmM
  have hm2 : (0:ℝ) < m ^ 2 := by positivity
  have hM2 : (0:ℝ) < M ^ 2 := by positivity
  have hinv : 1 / M ^ 2 ≤ 1 / m ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) hm2
    nlinarith
  have hdiff : y / M ^ 2 + (N - y) / m ^ 2 - (x / M ^ 2 + (N - x) / m ^ 2)
      = (y - x) * (1 / M ^ 2 - 1 / m ^ 2) := by
    field_simp
    ring
  nlinarith [hdiff, hinv, hxy]

/-- **The base case of Lemma 2.2, parametric in `ν`.**

`ν` is pinned by the two hypotheses `hnu_ge` (`M^ν m^{8-ν} ≥ C`) and `hnu_min`
(`M^j m^{8-j} < C` for `j < ν`) — exactly the paper's "least integer such that". -/
theorem base_general {m M C : ℝ} {nu : ℕ} (hm : 0 < m) (hmM : m < M) (hC : 0 < C)
    (hnu1 : 1 ≤ nu) (hnu8 : nu ≤ 8)
    (hnu_ge : C ≤ M ^ nu * m ^ (8 - nu))
    (hnu_min : ∀ j : ℕ, j < nu → M ^ j * m ^ (8 - j) < C)
    (r : Fin 8 → ℝ) (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M)
    (hprod : C ≤ ∏ k, r k) (hcard : (interior m M r).card ≤ 1) :
    ∑ k, 1 / (r k) ^ 2
      ≤ ((8 - nu : ℕ) : ℝ) / m ^ 2 + ((nu - 1 : ℕ) : ℝ) / M ^ 2
        + (M ^ (nu - 1) * m ^ (8 - nu) / C) ^ 2 := by
  have hM0 : (0:ℝ) < M := lt_trans hm hmM
  set K : ℝ := M ^ (nu - 1) * m ^ (8 - nu) with hK
  have hK0 : 0 < K := by positivity
  -- `M · K = M^ν m^{8-ν}`, since `1 ≤ ν`
  have hMK : M * K = M ^ nu * m ^ (8 - nu) := by
    rw [hK, ← mul_assoc, ← pow_succ']
    congr 2
    omega
  have hinvM : 1 / M ^ 2 ≤ (K / C) ^ 2 :=
    Sigma.inv_M_sq_le hM0 hC hK0 (by rw [hMK]; exact hnu_ge)
  -- `linarith` sees `ν/M²` as a product of two atoms, so peel the `1/M²` by hand
  have hpeel : ((nu : ℝ) - 1) / M ^ 2 + 1 / M ^ 2 = (nu : ℝ) / M ^ 2 := by
    rw [← add_div]
    congr 1
    ring
  have hpeel' : (7 - (nu : ℝ)) / m ^ 2 + 1 / m ^ 2 = (8 - (nu : ℝ)) / m ^ 2 := by
    rw [← add_div]
    congr 1
    ring
  -- cast the natural-subtraction constants once
  have c8 : ((8 - nu : ℕ) : ℝ) = 8 - (nu : ℝ) := by
    have : (nu : ℝ) ≤ 8 := by exact_mod_cast hnu8
    push_cast [Nat.cast_sub hnu8]
    ring
  have c1 : ((nu - 1 : ℕ) : ℝ) = (nu : ℝ) - 1 := by
    push_cast [Nat.cast_sub hnu1]
    ring
  rw [c8, c1]
  -- the split.  `set` comes AFTER the three `have`s so it abstracts the cardinalities
  -- inside them; abstracting first would leave the later terms unfolded, and `rw`ing
  -- them back fails on `hsum` (which mentions `interior` but not its card).
  have hsum := Sigma.sum_split hmM r hlo hhi
  have hpr := Sigma.prod_split hmM r hlo hhi
  have hcs := Sigma.card_split hmM r hlo hhi
  set h := (atHi m M r).card with hh
  set l := (atLo m M r).card with hl
  set i := (interior m M r).card with hi
  -- the interior contributes at most one coordinate
  rcases Nat.lt_or_ge i 1 with hi0 | hi1
  · -- ### `i = 0`: no interior coordinate
    have hzero : i = 0 := by omega
    have hcard0 : (interior m M r).card = 0 := by rw [← hi]; exact hzero
    have hempty : interior m M r = ∅ := Finset.card_eq_zero.mp hcard0
    have hl8 : l = 8 - h := by omega
    have hh8 : h ≤ 8 := by omega
    have hprodv : ∏ k, r k = M ^ h * m ^ l := by
      rw [hpr, hempty, Finset.prod_empty, mul_one]
    have hsumv : ∑ k, 1 / (r k) ^ 2 = (h : ℝ) / M ^ 2 + (l : ℝ) / m ^ 2 := by
      rw [hsum, hempty, Finset.sum_empty, add_zero]
      ring
    -- `ν`'s minimality forces `h ≥ ν`
    have hhnu : nu ≤ h := by
      by_contra hcon
      push_neg at hcon
      have := hnu_min h hcon
      rw [hl8] at hprodv
      rw [hprodv] at hprod
      linarith
    have hlR : (l : ℝ) = 8 - (h : ℝ) := by
      have : (l : ℕ) = 8 - h := hl8
      have h8 : h ≤ 8 := hh8
      push_cast [this, Nat.cast_sub h8]
      ring
    have hnuR : (nu : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhnu
    have hdes := descent hm hmM (nu : ℝ) (h : ℝ) 8 hnuR
    rw [hsumv, hlR]
    linarith [hdes, hinvM, hpeel]
  · -- ### `i = 1`: exactly one interior coordinate
    have hone : i = 1 := by omega
    have hcard1 : (interior m M r).card = 1 := by rw [← hi]; exact hone
    obtain ⟨k0, hk0⟩ := Finset.card_eq_one.mp hcard1
    have hk0mem : k0 ∈ interior m M r := by rw [hk0]; exact Finset.mem_singleton_self k0
    -- `interior` alone is ambiguous (Mathlib's topological `interior` is also in scope)
    simp only [Sigma.interior, mem_filter, mem_univ, true_and] at hk0mem
    obtain ⟨hs_lo, hs_hi⟩ := hk0mem
    set s := r k0 with hs
    have hs0 : 0 < s := lt_trans hm hs_lo
    have hl7 : l = 7 - h := by omega
    have hh7 : h ≤ 7 := by omega
    have hprodv : ∏ k, r k = M ^ h * m ^ l * s := by
      rw [hpr, hk0, Finset.prod_singleton]
    have hsumv : ∑ k, 1 / (r k) ^ 2
        = (h : ℝ) / M ^ 2 + (l : ℝ) / m ^ 2 + 1 / s ^ 2 := by
      rw [hsum, hk0, Finset.sum_singleton]
      ring
    have hlR : (l : ℝ) = 7 - (h : ℝ) := by
      have hle : h ≤ 7 := hh7
      push_cast [hl7, Nat.cast_sub hle]
      ring
    rcases Nat.lt_or_ge (h + 1) nu with hlt | hge
    · -- `h ≤ ν - 2` is infeasible: even `s = M` does not reach `C`
      have hkey := hnu_min (h + 1) hlt
      have hexp : M ^ (h + 1) * m ^ (8 - (h + 1)) = M ^ h * m ^ l * M := by
        rw [pow_succ]
        have : 8 - (h + 1) = l := by omega
        rw [this]
        ring
      rw [hexp] at hkey
      have hpos : (0:ℝ) < M ^ h * m ^ l := by positivity
      have : ∏ k, r k < M ^ h * m ^ l * M := by
        rw [hprodv]
        exact mul_lt_mul_of_pos_left hs_hi hpos
      linarith
    · -- `h ≥ ν - 1`
      rcases Nat.lt_or_ge h nu with hlt' | hge'
      · -- `h = ν - 1`: **the tight case**, where the product constraint pins `s`
        have hhv : h = nu - 1 := by omega
        have hlv : l = 8 - nu := by omega
        have hKs : K * s = M ^ h * m ^ l * s := by rw [hK, hhv, hlv]
        have hsge : C ≤ K * s := by rw [hKs, ← hprodv]; exact hprod
        have hsC : C / K ≤ s := by
          rw [div_le_iff₀ hK0]
          linarith [hsge]
        have hCK0 : (0:ℝ) < C / K := by positivity
        have hinvs : 1 / s ^ 2 ≤ (K / C) ^ 2 := by
          have hsq : (C / K) ^ 2 ≤ s ^ 2 := by
            exact pow_le_pow_left₀ (le_of_lt hCK0) hsC 2
          have h1 : 1 / s ^ 2 ≤ 1 / (C / K) ^ 2 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
          have h2 : 1 / (C / K) ^ 2 = (K / C) ^ 2 := by
            rw [div_pow, div_pow]
            field_simp
          linarith [h1, h2.le, h2.ge]
        have hhR : (h : ℝ) = (nu : ℝ) - 1 := by
          have : (h : ℕ) = nu - 1 := hhv
          push_cast [this, Nat.cast_sub hnu1]
          ring
        have hlR' : (l : ℝ) = 8 - (nu : ℝ) := by
          have : (l : ℕ) = 8 - nu := hlv
          push_cast [this, Nat.cast_sub hnu8]
          ring
        rw [hsumv, hhR, hlR']
        linarith [hinvs]
      · -- `h ≥ ν`: slide `h` down to `ν`, and absorb the interior coordinate at `m`
        have hnuR : (nu : ℝ) ≤ (h : ℝ) := by exact_mod_cast hge'
        have hdes := descent hm hmM (nu : ℝ) (h : ℝ) 7 hnuR
        have hsm : 1 / s ^ 2 ≤ 1 / m ^ 2 := by
          have hsq : m ^ 2 ≤ s ^ 2 := by nlinarith [hs_lo, hm]
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
        rw [hsumv, hlR]
        linarith [hdes, hinvM, hsm, hpeel, hpeel']

/-- **Lemma 2.2 in general form.**  The base case above fed through
`Sigma.of_base`'s spreading induction. -/
theorem sigma_bound {m M C : ℝ} {nu : ℕ} (hm : 0 < m) (hmM : m < M) (hC : 0 < C)
    (hnu1 : 1 ≤ nu) (hnu8 : nu ≤ 8)
    (hnu_ge : C ≤ M ^ nu * m ^ (8 - nu))
    (hnu_min : ∀ j : ℕ, j < nu → M ^ j * m ^ (8 - j) < C)
    (r : Fin 8 → ℝ) (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M)
    (hprod : C ≤ ∏ k, r k) :
    ∑ k, 1 / (r k) ^ 2
      ≤ ((8 - nu : ℕ) : ℝ) / m ^ 2 + ((nu - 1 : ℕ) : ℝ) / M ^ 2
        + (M ^ (nu - 1) * m ^ (8 - nu) / C) ^ 2 :=
  Sigma.of_base m M C _ hm
    (fun r' hlo' hhi' hprod' hcard' =>
      base_general hm hmM hC hnu1 hnu8 hnu_ge hnu_min r' hlo' hhi' hprod' hcard')
    8 r (by
      have : (interior m M r).card ≤ (univ : Finset (Fin 8)).card := Finset.card_le_card (by simp)
      simpa using this)
    hlo hhi hprod

/-- The bound in the form the range assembly consumes: a rational `S` dominating it. -/
theorem sigma_le_of {m M C S : ℝ} {nu : ℕ} (hm : 0 < m) (hmM : m < M) (hC : 0 < C)
    (hnu1 : 1 ≤ nu) (hnu8 : nu ≤ 8)
    (hnu_ge : C ≤ M ^ nu * m ^ (8 - nu))
    (hnu_min : ∀ j : ℕ, j < nu → M ^ j * m ^ (8 - j) < C)
    (hS : ((8 - nu : ℕ) : ℝ) / m ^ 2 + ((nu - 1 : ℕ) : ℝ) / M ^ 2
        + (M ^ (nu - 1) * m ^ (8 - nu) / C) ^ 2 ≤ S)
    (r : Fin 8 → ℝ) (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M)
    (hprod : C ≤ ∏ k, r k) :
    ∑ k, 1 / (r k) ^ 2 ≤ S :=
  le_trans (sigma_bound hm hmM hC hnu1 hnu8 hnu_ge hnu_min r hlo hhi hprod) hS

/-! ## The two instances the paper names explicitly

These reproduce `Stage2Probe.sigma_small_bound` and `sigma_boundary_bound` — which were
previously *arithmetic assertions* about the closed form — as consequences of the
general lemma applied to an actual family `r`.  The eighteen middle-range instances are
the same three lines with `M = 1 + β` and the row's `ν`. -/

/-- The small range: `m₀ = 681/1000`, `M = 29/20`, `C = 9`, `ν = 7` ⟹ `σ ≤ 1101/200`.

This is `Master.SigmaBoundSmall`, now derived rather than assumed. -/
theorem sigma_small (r : Fin 8 → ℝ)
    (hlo : ∀ k, (681/1000 : ℝ) ≤ r k) (hhi : ∀ k, r k ≤ (29/20 : ℝ))
    (hprod : (9:ℝ) ≤ ∏ k, r k) :
    ∑ k, 1 / (r k) ^ 2 ≤ 1101/200 := by
  refine sigma_le_of (nu := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) r hlo hhi hprod
  intro j hj
  interval_cases j <;> norm_num

/-- The boundary range: `M = 2`, `ν = 5` ⟹ `σ ≤ 39/5`. -/
theorem sigma_boundary (r : Fin 8 → ℝ)
    (hlo : ∀ k, (681/1000 : ℝ) ≤ r k) (hhi : ∀ k, r k ≤ (2 : ℝ))
    (hprod : (9:ℝ) ≤ ∏ k, r k) :
    ∑ k, 1 / (r k) ^ 2 ≤ 39/5 := by
  refine sigma_le_of (nu := 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) r hlo hhi hprod
  intro j hj
  interval_cases j <;> norm_num

end Sendov9.SigmaGen

#print axioms Sendov9.SigmaGen.descent
#print axioms Sendov9.SigmaGen.base_general
#print axioms Sendov9.SigmaGen.sigma_bound
#print axioms Sendov9.SigmaGen.sigma_le_of
#print axioms Sendov9.SigmaGen.sigma_small
#print axioms Sendov9.SigmaGen.sigma_boundary
