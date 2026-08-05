import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.Sigma

open Finset

/-!
# Lemma 2.2 — the induction, reducing to ≤ 1 interior coordinate

`Stage2bc.lean` banked the algebraic core: spreading two interior coordinates by
`c = min (rᵢ/m) (M/rⱼ)` preserves their product, keeps both in `[m,M]`, lands at
least one on an endpoint, and does not decrease `∑ r⁻²`.

This file runs the induction on the number of interior coordinates, reducing the
general statement to the `≤ 1 interior coordinate` case (`base`), which is a finite
case analysis and is supplied as a hypothesis here so the induction can be verified
independently of it.
-/

/-- The strictly-interior coordinates. -/
noncomputable def interior (m M : ℝ) (r : Fin 8 → ℝ) : Finset (Fin 8) :=
  univ.filter (fun k => m < r k ∧ r k < M)

/-- Spreading `(rᵢ, rⱼ) → (rᵢ/c, rⱼ·c)`. -/
noncomputable def spread (r : Fin 8 → ℝ) (i j : Fin 8) (c : ℝ) : Fin 8 → ℝ :=
  Function.update (Function.update r i (r i / c)) j (r j * c)

@[simp] theorem spread_at_j (r : Fin 8 → ℝ) (i j : Fin 8) (c : ℝ) :
    spread r i j c j = r j * c := by
  simp [spread]

theorem spread_at_i (r : Fin 8 → ℝ) {i j : Fin 8} (hij : i ≠ j) (c : ℝ) :
    spread r i j c i = r i / c := by
  simp [spread, Function.update_of_ne hij]

theorem spread_at_other (r : Fin 8 → ℝ) {i j k : Fin 8} (hki : k ≠ i) (hkj : k ≠ j) (c : ℝ) :
    spread r i j c k = r k := by
  simp [spread, Function.update_of_ne hkj, Function.update_of_ne hki]

/-- The product is preserved. -/
theorem spread_prod_eq (r : Fin 8 → ℝ) {i j : Fin 8} (hij : i ≠ j) {c : ℝ} (hc : c ≠ 0) :
    ∏ k, spread r i j c k = ∏ k, r k := by
  have hj : j ∈ (univ : Finset (Fin 8)) := mem_univ j
  have hi' : i ∈ (univ : Finset (Fin 8)).erase j := by
    simp [Finset.mem_erase, hij]
  set Q := ∏ x ∈ ((univ : Finset (Fin 8)).erase j).erase i, r x with hQ
  have e1 : ∏ k, spread r i j c k
      = (r j * c) * ∏ x ∈ (univ : Finset (Fin 8)).erase j,
          Function.update r i (r i / c) x := by
    simp only [spread]
    rw [Finset.prod_update_of_mem hj, Finset.sdiff_singleton_eq_erase]
  have e2 : ∏ x ∈ (univ : Finset (Fin 8)).erase j, Function.update r i (r i / c) x
      = (r i / c) * Q := by
    rw [Finset.prod_update_of_mem hi', Finset.sdiff_singleton_eq_erase, hQ]
  have e3 : ∏ k, r k = r j * ∏ x ∈ (univ : Finset (Fin 8)).erase j, r x :=
    (Finset.mul_prod_erase _ r hj).symm
  have e4 : ∏ x ∈ (univ : Finset (Fin 8)).erase j, r x = r i * Q :=
    (Finset.mul_prod_erase _ r hi').symm
  rw [e1, e2, e3, e4]
  rw [show (r j * c) * ((r i / c) * Q) = (r j * (r i * Q)) * (c / c) from by ring,
    div_self hc, mul_one]

/-- Spreading does not decrease `∑ r⁻²`, given `rᵢ ≤ rⱼ` and `c ≥ 1`. -/
theorem spread_sum_ge (r : Fin 8 → ℝ) {i j : Fin 8} (hij : i ≠ j)
    (hri : 0 < r i) (hrj : 0 < r j) (hle : r i ≤ r j) {c : ℝ} (hc : 1 ≤ c) :
    ∑ k, 1 / (r k) ^ 2 ≤ ∑ k, 1 / (spread r i j c k) ^ 2 := by
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le one_pos hc
  -- the two-coordinate inequality, banked in Stage2bc
  have hpair : 1 / (r i) ^ 2 + 1 / (r j) ^ 2
      ≤ 1 / (r i / c) ^ 2 + 1 / (r j * c) ^ 2 := by
    have hri2 : (0:ℝ) < (r i) ^ 2 := by positivity
    have hrj2 : (0:ℝ) < (r j) ^ 2 := by positivity
    have hkey : (r i) ^ 2 ≤ c ^ 2 * (r j) ^ 2 := by
      have s1 : (r i) ^ 2 ≤ (r j) ^ 2 := by nlinarith
      have s2 : (1:ℝ) ≤ c ^ 2 := by nlinarith
      have s3 : (r j) ^ 2 ≤ c ^ 2 * (r j) ^ 2 := by nlinarith
      linarith
    have hid : 1 / (r i / c) ^ 2 + 1 / (r j * c) ^ 2 - (1 / (r i) ^ 2 + 1 / (r j) ^ 2)
        = (c ^ 2 - 1) * (1 / (r i) ^ 2 - 1 / (c ^ 2 * (r j) ^ 2)) := by
      field_simp
      ring
    have h1 : (0:ℝ) ≤ c ^ 2 - 1 := by nlinarith
    have h2 : (0:ℝ) ≤ 1 / (r i) ^ 2 - 1 / (c ^ 2 * (r j) ^ 2) := by
      rw [sub_nonneg]
      exact div_le_div_of_nonneg_left (by norm_num) hri2 hkey
    linarith [mul_nonneg h1 h2, hid]
  -- split both sums over {i, j} and the rest
  have hsub : ({i, j} : Finset (Fin 8)) ⊆ univ := subset_univ _
  rw [← Finset.sum_sdiff hsub, ← Finset.sum_sdiff hsub]
  have hrest : ∀ k ∈ (univ : Finset (Fin 8)) \ {i, j},
      1 / (spread r i j c k) ^ 2 = 1 / (r k) ^ 2 := by
    intro k hk
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hk
    rw [spread_at_other r hk.2.1 hk.2.2]
  rw [Finset.sum_congr rfl hrest]
  have hpairsum : ∑ k ∈ ({i, j} : Finset (Fin 8)), 1 / (r k) ^ 2
      ≤ ∑ k ∈ ({i, j} : Finset (Fin 8)), 1 / (spread r i j c k) ^ 2 := by
    rw [Finset.sum_pair hij, Finset.sum_pair hij, spread_at_i r hij, spread_at_j]
    exact hpair
  linarith

/-- The scaling factor `c = min (rᵢ/m) (M/rⱼ)` for interior `i`, `j`. -/
noncomputable def fac (m M : ℝ) (r : Fin 8 → ℝ) (i j : Fin 8) : ℝ :=
  min (r i / m) (M / r j)

theorem fac_le_left (m M : ℝ) (r : Fin 8 → ℝ) (i j : Fin 8) :
    fac m M r i j ≤ r i / m := min_le_left _ _

theorem fac_le_right (m M : ℝ) (r : Fin 8 → ℝ) (i j : Fin 8) :
    fac m M r i j ≤ M / r j := min_le_right _ _

theorem one_le_fac {m M : ℝ} {r : Fin 8 → ℝ} {i j : Fin 8} (hm : 0 < m)
    (hrj : 0 < r j) (hi : m < r i) (hj : r j < M) : 1 ≤ fac m M r i j := by
  refine le_of_lt (lt_min ?_ ?_)
  · rw [lt_div_iff₀ hm]; linarith
  · rw [lt_div_iff₀ hrj]; linarith

/-- At least one of the two scaled coordinates lands on an endpoint, since
`fac = min (rᵢ/m) (M/rⱼ)` attains one of its two arguments. -/
theorem fac_hits_endpoint {m M : ℝ} {r : Fin 8 → ℝ} {i j : Fin 8} (hm : 0 < m)
    (hri : 0 < r i) (hrj : 0 < r j) :
    r i / fac m M r i j = m ∨ r j * fac m M r i j = M := by
  have hm' : m ≠ 0 := ne_of_gt hm
  have hri' : r i ≠ 0 := ne_of_gt hri
  have hrj' : r j ≠ 0 := ne_of_gt hrj
  rcases min_cases (r i / m) (M / r j) with ⟨h, _⟩ | ⟨h, _⟩
  · left; simp only [fac]; rw [h]; field_simp
  · right; simp only [fac]; rw [h]; field_simp

/-- Spreading keeps every coordinate inside `[m,M]`. -/
theorem spread_mem {m M : ℝ} {r : Fin 8 → ℝ} {i j : Fin 8} (hij : i ≠ j) (hm : 0 < m)
    (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M) (hi : m < r i) (hj : r j < M) :
    ∀ k, m ≤ spread r i j (fac m M r i j) k ∧ spread r i j (fac m M r i j) k ≤ M := by
  have hrj : 0 < r j := lt_of_lt_of_le hm (hlo j)
  have hri : 0 < r i := lt_of_lt_of_le hm (hlo i)
  have hc1 : 1 ≤ fac m M r i j := one_le_fac hm hrj hi hj
  have hc0 : 0 < fac m M r i j := lt_of_lt_of_le one_pos hc1
  intro k
  by_cases hki : k = i
  · rw [hki, spread_at_i r hij]
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hc0]
      calc m * fac m M r i j ≤ m * (r i / m) :=
            mul_le_mul_of_nonneg_left (fac_le_left m M r i j) (le_of_lt hm)
        _ = r i := by field_simp
    · calc r i / fac m M r i j ≤ r i / 1 :=
            div_le_div_of_nonneg_left (le_of_lt hri) one_pos hc1
        _ = r i := by ring
        _ ≤ M := hhi i
  · by_cases hkj : k = j
    · rw [hkj, spread_at_j]
      refine ⟨?_, ?_⟩
      · calc m ≤ r j := hlo j
          _ = r j * 1 := by ring
          _ ≤ r j * fac m M r i j := mul_le_mul_of_nonneg_left hc1 (le_of_lt hrj)
      · have h2 : fac m M r i j ≤ M / r j := fac_le_right m M r i j
        rw [le_div_iff₀ hrj] at h2
        linarith
    · rw [spread_at_other r hki hkj]
      exact ⟨hlo k, hhi k⟩

/-- Spreading never creates a new interior coordinate. -/
theorem spread_interior_subset {m M : ℝ} {r : Fin 8 → ℝ} {i j : Fin 8} (hij : i ≠ j)
    (hi : i ∈ interior m M r) (hj : j ∈ interior m M r) (c : ℝ) :
    interior m M (spread r i j c) ⊆ interior m M r := by
  intro k hk
  by_cases hki : k = i
  · subst hki; exact hi
  · by_cases hkj : k = j
    · subst hkj; exact hj
    · simp only [interior, mem_filter, mem_univ, true_and] at hk ⊢
      rwa [spread_at_other r hki hkj] at hk

/-- One spreading step, feeding the induction hypothesis. -/
theorem spread_step (m M C Bound : ℝ) (hm : 0 < m) {n : ℕ}
    (ih : ∀ r : Fin 8 → ℝ, (interior m M r).card ≤ n → (∀ k, m ≤ r k) → (∀ k, r k ≤ M) →
      C ≤ ∏ k, r k → ∑ k, 1 / (r k) ^ 2 ≤ Bound)
    (r : Fin 8 → ℝ) (hcard : (interior m M r).card ≤ n + 1)
    (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M) (hprod : C ≤ ∏ k, r k)
    (i : Fin 8) (hi : i ∈ interior m M r) (j : Fin 8) (hj : j ∈ interior m M r)
    (hij : i ≠ j) (hord : r i ≤ r j) :
    ∑ k, 1 / (r k) ^ 2 ≤ Bound := by
  simp only [interior, mem_filter, mem_univ, true_and] at hi hj
  have hri : 0 < r i := lt_of_lt_of_le hm (hlo i)
  have hrj : 0 < r j := lt_of_lt_of_le hm (hlo j)
  set c := fac m M r i j with hcdef
  have hc1 : 1 ≤ c := one_le_fac hm hrj hi.1 hj.2
  have hc0 : c ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hc1)
  set r' := spread r i j c with hr'
  have hmem := spread_mem hij hm hlo hhi hi.1 hj.2
  have hlo' : ∀ k, m ≤ r' k := fun k => (hmem k).1
  have hhi' : ∀ k, r' k ≤ M := fun k => (hmem k).2
  have hprod' : C ≤ ∏ k, r' k := by
    rw [hr', spread_prod_eq r hij hc0]; exact hprod
  -- one of the two coordinates lands on an endpoint, so the interior count drops
  have hsub : interior m M r' ⊆ interior m M r := by
    refine spread_interior_subset hij ?_ ?_ c
    · simp only [interior, mem_filter, mem_univ, true_and]; exact hi
    · simp only [interior, mem_filter, mem_univ, true_and]; exact hj
  have hdrop : ∃ k ∈ interior m M r, k ∉ interior m M r' := by
    rcases fac_hits_endpoint (m := m) (M := M) (r := r) (i := i) (j := j) hm hri hrj with
      hend | hend
    · refine ⟨i, ?_, ?_⟩
      · simp only [interior, mem_filter, mem_univ, true_and]; exact hi
      · simp only [interior, mem_filter, mem_univ, true_and]
        intro hcon
        have hval : r' i = m := by rw [hr', spread_at_i r hij, hcdef]; exact hend
        rw [hval] at hcon
        exact absurd hcon.1 (lt_irrefl m)
    · refine ⟨j, ?_, ?_⟩
      · simp only [interior, mem_filter, mem_univ, true_and]; exact hj
      · simp only [interior, mem_filter, mem_univ, true_and]
        intro hcon
        have hval : r' j = M := by rw [hr', spread_at_j, hcdef]; exact hend
        rw [hval] at hcon
        exact absurd hcon.2 (lt_irrefl M)
  obtain ⟨k0, hk0r, hk0r'⟩ := hdrop
  have hssub : interior m M r' ⊂ interior m M r :=
    Finset.ssubset_iff_of_subset hsub |>.mpr ⟨k0, hk0r, hk0r'⟩
  have hlt : (interior m M r').card < (interior m M r).card := Finset.card_lt_card hssub
  have hle' : (interior m M r').card ≤ n := by omega
  calc ∑ k, 1 / (r k) ^ 2 ≤ ∑ k, 1 / (r' k) ^ 2 := by
        rw [hr']; exact spread_sum_ge r hij hri hrj hord hc1
    _ ≤ Bound := ih r' hle' hlo' hhi' hprod'

/-- **The induction.**  Given the `≤ 1 interior coordinate` case, the bound holds in
general: each spreading step strictly reduces the interior count while preserving the
product constraint and not decreasing the objective. -/
theorem of_base (m M C Bound : ℝ) (hm : 0 < m)
    (base : ∀ r : Fin 8 → ℝ, (∀ k, m ≤ r k) → (∀ k, r k ≤ M) → C ≤ ∏ k, r k →
      (interior m M r).card ≤ 1 → ∑ k, 1 / (r k) ^ 2 ≤ Bound) :
    ∀ (n : ℕ) (r : Fin 8 → ℝ), (interior m M r).card ≤ n →
      (∀ k, m ≤ r k) → (∀ k, r k ≤ M) → C ≤ ∏ k, r k →
      ∑ k, 1 / (r k) ^ 2 ≤ Bound := by
  intro n
  induction n with
  | zero => intro r hc hlo hhi hprod; exact base r hlo hhi hprod (by omega)
  | succ n ih =>
    intro r hc hlo hhi hprod
    by_cases hle : (interior m M r).card ≤ 1
    · exact base r hlo hhi hprod hle
    · push_neg at hle
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hle
      -- order the pair so the smaller coordinate is scaled down
      rcases le_total (r a) (r b) with hord | hord
      · exact spread_step m M C Bound hm ih r hc hlo hhi hprod a ha b hb hab hord
      · exact spread_step m M C Bound hm ih r hc hlo hhi hprod b hb a ha (Ne.symm hab) hord

/-! ## The base case's arithmetic

With `j` coordinates at `M`, `l` at `m` and at most one interior, the constraint
`∏ rₖ ≥ C` forces `j ≥ ν - 1`, and:

* `j ≥ ν`  — the interior coordinate (if any) is pinned below by `m` rather than by
  the product constraint, so the sum is `j/M² + (8-j)/m²`, decreasing in `j`, hence
  at most its value at `j = ν`, which is `≤ Bound` (`base_case_high`);
* `j = ν - 1` — the product constraint binds and the sum equals `Bound` exactly.

These two facts are the whole content; the rest of the base case is bookkeeping. -/

/-- Moving a coordinate from `m` up to `M` decreases `∑ r⁻²`. -/
theorem step_down {m M : ℝ} (hm : 0 < m) (hmM : m < M) (j : ℝ) :
    (j + 1) / M ^ 2 + (8 - (j + 1)) / m ^ 2 ≤ j / M ^ 2 + (8 - j) / m ^ 2 := by
  have hM0 : (0:ℝ) < M := lt_trans hm hmM
  have h1 : (0:ℝ) < m ^ 2 := by positivity
  have h2 : (0:ℝ) < M ^ 2 := by positivity
  have h3 : 1 / M ^ 2 ≤ 1 / m ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) h1
    nlinarith
  have e : (j + 1) / M ^ 2 + (8 - (j + 1)) / m ^ 2 - (j / M ^ 2 + (8 - j) / m ^ 2)
      = 1 / M ^ 2 - 1 / m ^ 2 := by field_simp; ring
  linarith

/-- **The `j ≥ ν` step.** With `K = M^{ν-1} m^{8-ν} > 0`, the defining property of `ν`
(`C ≤ M^ν m^{8-ν} = M·K`) is exactly what upgrades `ν/M² + (8-ν)/m²` to `Bound`. -/
theorem inv_M_sq_le {M C K : ℝ} (hM : 0 < M) (hC : 0 < C) (hK : 0 < K)
    (h : C ≤ M * K) : 1 / M ^ 2 ≤ (K / C) ^ 2 := by
  have h1 : 1 / M ≤ K / C := by
    rw [div_le_div_iff₀ hM hC]
    linarith
  have h2 : (0:ℝ) < 1 / M := by positivity
  calc 1 / M ^ 2 = (1 / M) ^ 2 := by rw [div_pow]; norm_num
    _ ≤ (K / C) ^ 2 := by
        exact pow_le_pow_left₀ (le_of_lt h2) h1 2



/-!
# Lemma 2.2 — the base case: `≤ 1` interior coordinate

`Sigma22.lean` reduced the σ bound to configurations with at most one strictly
interior coordinate.  Here every other coordinate sits on an endpoint, so the whole
statement is controlled by **one number**: `h`, the count of coordinates equal to `M`.

The partition `univ = H ⊍ L ⊍ I` (at `M`, at `m`, interior) gives

    ∑ₖ rₖ⁻² = h/M² + l/m² + ∑_{k ∈ I} rₖ⁻²        (`sum_split`)
    ∏ₖ rₖ   = M^h · m^l · ∏_{k ∈ I} rₖ            (`prod_split`)

after which each concrete instance is a handful of numeric cases in `h`.
-/


/-- Coordinates sitting at the upper endpoint. -/
noncomputable def atHi (m M : ℝ) (r : Fin 8 → ℝ) : Finset (Fin 8) :=
  univ.filter (fun k => r k = M)

/-- Coordinates sitting at the lower endpoint. -/
noncomputable def atLo (m M : ℝ) (r : Fin 8 → ℝ) : Finset (Fin 8) :=
  univ.filter (fun k => r k = m)

/-- Every coordinate is at `M`, at `m`, or strictly interior — exactly one of the three. -/
theorem mem_trichotomy (hmM : m < M) (r : Fin 8 → ℝ)
    (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M) (k : Fin 8) :
    (k ∈ atHi m M r ∧ k ∉ atLo m M r ∧ k ∉ interior m M r) ∨
    (k ∉ atHi m M r ∧ k ∈ atLo m M r ∧ k ∉ interior m M r) ∨
    (k ∉ atHi m M r ∧ k ∉ atLo m M r ∧ k ∈ interior m M r) := by
  simp only [atHi, atLo, interior, mem_filter, mem_univ, true_and]
  rcases eq_or_lt_of_le (hhi k) with hH | hH
  · exact Or.inl ⟨hH, by intro hc; rw [hH] at hc; linarith,
      by rintro ⟨_, h2⟩; rw [hH] at h2; exact absurd h2 (lt_irrefl M)⟩
  · rcases eq_or_lt_of_le (hlo k) with hL | hL
    · exact Or.inr (Or.inl ⟨by intro hc; rw [← hL] at hc; linarith, hL.symm,
        by rintro ⟨h1, _⟩; rw [← hL] at h1; exact absurd h1 (lt_irrefl m)⟩)
    · exact Or.inr (Or.inr ⟨by intro hc; rw [hc] at hH; exact absurd hH (lt_irrefl M),
        by intro hc; rw [hc] at hL; exact absurd hL (lt_irrefl m), ⟨hL, hH⟩⟩)

/-- The three parts cover everything. -/
theorem union_eq_univ (hmM : m < M) (r : Fin 8 → ℝ)
    (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M) :
    atHi m M r ∪ atLo m M r ∪ interior m M r = univ := by
  ext k
  simp only [mem_union, mem_univ, iff_true]
  rcases mem_trichotomy hmM r hlo hhi k with ⟨h, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem hi_disj_lo (hmM : m < M) (r : Fin 8 → ℝ) :
    Disjoint (atHi m M r) (atLo m M r) := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  simp only [atHi, atLo, mem_filter, mem_univ, true_and] at hk hk'
  rw [hk] at hk'; exact absurd hk'.symm (ne_of_lt hmM)

theorem hi_disj_int (r : Fin 8 → ℝ) : Disjoint (atHi m M r) (interior m M r) := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  simp only [atHi, interior, mem_filter, mem_univ, true_and] at hk hk'
  rw [hk] at hk'; exact absurd hk'.2 (lt_irrefl M)

theorem lo_disj_int (r : Fin 8 → ℝ) : Disjoint (atLo m M r) (interior m M r) := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  simp only [atLo, interior, mem_filter, mem_univ, true_and] at hk hk'
  rw [hk] at hk'; exact absurd hk'.1 (lt_irrefl m)

/-- **The sum splits.** -/
theorem sum_split (hmM : m < M) (r : Fin 8 → ℝ)
    (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M) :
    ∑ k, 1 / (r k) ^ 2
      = (atHi m M r).card * (1 / M ^ 2) + (atLo m M r).card * (1 / m ^ 2)
        + ∑ k ∈ interior m M r, 1 / (r k) ^ 2 := by
  have hcover := union_eq_univ hmM r hlo hhi
  have hd1 : Disjoint (atHi m M r ∪ atLo m M r) (interior m M r) :=
    Finset.disjoint_union_left.mpr ⟨hi_disj_int r, lo_disj_int r⟩
  calc ∑ k, 1 / (r k) ^ 2
      = ∑ k ∈ atHi m M r ∪ atLo m M r ∪ interior m M r, 1 / (r k) ^ 2 := by rw [hcover]
    _ = ∑ k ∈ atHi m M r ∪ atLo m M r, 1 / (r k) ^ 2
          + ∑ k ∈ interior m M r, 1 / (r k) ^ 2 := Finset.sum_union hd1
    _ = (∑ k ∈ atHi m M r, 1 / (r k) ^ 2 + ∑ k ∈ atLo m M r, 1 / (r k) ^ 2)
          + ∑ k ∈ interior m M r, 1 / (r k) ^ 2 := by
        rw [Finset.sum_union (hi_disj_lo hmM r)]
    _ = _ := by
        congr 2
        · rw [Finset.sum_congr rfl (fun k hk => by
            simp only [atHi, mem_filter, mem_univ, true_and] at hk; rw [hk]),
            Finset.sum_const, nsmul_eq_mul]
        · rw [Finset.sum_congr rfl (fun k hk => by
            simp only [atLo, mem_filter, mem_univ, true_and] at hk; rw [hk]),
            Finset.sum_const, nsmul_eq_mul]

/-- **The product splits.** -/
theorem prod_split (hmM : m < M) (r : Fin 8 → ℝ)
    (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M) :
    ∏ k, r k
      = M ^ (atHi m M r).card * m ^ (atLo m M r).card
        * ∏ k ∈ interior m M r, r k := by
  have hcover := union_eq_univ hmM r hlo hhi
  have hd1 : Disjoint (atHi m M r ∪ atLo m M r) (interior m M r) :=
    Finset.disjoint_union_left.mpr ⟨hi_disj_int r, lo_disj_int r⟩
  calc ∏ k, r k
      = ∏ k ∈ atHi m M r ∪ atLo m M r ∪ interior m M r, r k := by rw [hcover]
    _ = (∏ k ∈ atHi m M r ∪ atLo m M r, r k) * ∏ k ∈ interior m M r, r k :=
        Finset.prod_union hd1
    _ = ((∏ k ∈ atHi m M r, r k) * ∏ k ∈ atLo m M r, r k)
          * ∏ k ∈ interior m M r, r k := by
        rw [Finset.prod_union (hi_disj_lo hmM r)]
    _ = _ := by
        congr 2
        · rw [Finset.prod_congr rfl (fun k hk => by
            simp only [atHi, mem_filter, mem_univ, true_and] at hk; exact hk),
            Finset.prod_const]
        · rw [Finset.prod_congr rfl (fun k hk => by
            simp only [atLo, mem_filter, mem_univ, true_and] at hk; exact hk),
            Finset.prod_const]

/-- The three cardinalities add to `8`. -/
theorem card_split (hmM : m < M) (r : Fin 8 → ℝ)
    (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M) :
    (atHi m M r).card + (atLo m M r).card + (interior m M r).card = 8 := by
  have hcover := union_eq_univ hmM r hlo hhi
  have hd1 : Disjoint (atHi m M r ∪ atLo m M r) (interior m M r) :=
    Finset.disjoint_union_left.mpr ⟨hi_disj_int r, lo_disj_int r⟩
  have h1 : (atHi m M r ∪ atLo m M r ∪ interior m M r).card
      = (atHi m M r ∪ atLo m M r).card + (interior m M r).card :=
    Finset.card_union_of_disjoint hd1
  have h2 : (atHi m M r ∪ atLo m M r).card
      = (atHi m M r).card + (atLo m M r).card :=
    Finset.card_union_of_disjoint (hi_disj_lo hmM r)
  rw [hcover] at h1
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

end Sendov9.Sigma

namespace Sendov9

open Finset

/-!
# The centred expansion (equation 3.9)

The paper writes `G(t) = ∏ⱼ (1 - t Yⱼ)` with `Yⱼ = μ + Dⱼ`, so with `w = 1 - tμ`

    G(t) = ∏ⱼ (w - t Dⱼ) = ∑_{m=0}^{8} (-t)^m w^{8-m} eₘ(D),

and since `∑ⱼ Dⱼ = 0` the `m = 1` term drops, leaving `w⁸` plus a tail that the
`eₘ` bounds control.

Rather than writing out the elementary symmetric functions of eight variables by
hand (70 terms at `m = 4` alone), this is derived from `Finset.prod_add` — which
expands a product of sums over all subsets — regrouped by subset size with
`Finset.sum_powerset`.
-/

/-- The `m`-th elementary symmetric function of a family indexed by `Fin 8`. -/
noncomputable def esD (D : Fin 8 → ℂ) (m : ℕ) : ℂ :=
  ∑ s ∈ (univ : Finset (Fin 8)).powersetCard m, ∏ j ∈ s, D j

@[simp] theorem esD_zero (D : Fin 8 → ℂ) : esD D 0 = 1 := by
  simp [esD, Finset.powersetCard_zero]

theorem esD_one (D : Fin 8 → ℂ) : esD D 1 = ∑ j, D j := by
  simp [esD, Finset.powersetCard_one, Finset.sum_map]

/-- **The centred expansion.**  `∏ⱼ (w - t Dⱼ) = ∑ₘ (-t)^m w^{8-m} eₘ(D)`. -/
theorem prod_sub_eq_sum_esD (w t : ℂ) (D : Fin 8 → ℂ) :
    ∏ j, (w - t * D j) = ∑ m ∈ range 9, (-t) ^ m * w ^ (8 - m) * esD D m := by
  have hrw : ∀ j : Fin 8, w - t * D j = (-t * D j) + w := by intro j; ring
  calc ∏ j, (w - t * D j) = ∏ j, ((-t * D j) + w) := by
        exact Finset.prod_congr rfl fun j _ => hrw j
    _ = ∑ s ∈ (univ : Finset (Fin 8)).powerset,
          (∏ j ∈ s, (-t * D j)) * ∏ _j ∈ univ \ s, w := Finset.prod_add _ _ _
    _ = ∑ m ∈ range 9, ∑ s ∈ (univ : Finset (Fin 8)).powersetCard m,
          (∏ j ∈ s, (-t * D j)) * ∏ _j ∈ univ \ s, w := by
        rw [Finset.sum_powerset]
        simp
    _ = ∑ m ∈ range 9, (-t) ^ m * w ^ (8 - m) * esD D m := by
        refine Finset.sum_congr rfl fun m hm => ?_
        simp only [mem_range] at hm
        rw [esD, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hcard : s.card = m := (Finset.mem_powersetCard.mp hs).2
        have hsub : s ⊆ univ := (Finset.mem_powersetCard.mp hs).1
        have h1 : ∏ j ∈ s, (-t * D j) = (-t) ^ m * ∏ j ∈ s, D j := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
        have h2 : ∏ _j ∈ (univ : Finset (Fin 8)) \ s, w = w ^ (8 - m) := by
          have hcompl : (univ : Finset (Fin 8)) \ s = sᶜ := (Finset.compl_eq_univ_sdiff s).symm
          rw [Finset.prod_const, hcompl, Finset.card_compl]
          simp [hcard]
        rw [h1, h2]
        ring

/-- With the deviations centred, the `m = 1` term vanishes and the expansion is
`w⁸` plus a tail supported on `2 ≤ m ≤ 8`. -/
theorem prod_sub_eq_head_add_tail (w t : ℂ) (D : Fin 8 → ℂ) (hD : ∑ j, D j = 0) :
    ∏ j, (w - t * D j)
      = w ^ 8 + ∑ m ∈ Finset.Icc 2 8, (-t) ^ m * w ^ (8 - m) * esD D m := by
  rw [prod_sub_eq_sum_esD]
  have h1 : esD D 1 = 0 := by rw [esD_one]; exact hD
  have hsplit : range 9 = {0, 1} ∪ Finset.Icc 2 8 := by decide
  rw [hsplit, Finset.sum_union (by decide)]
  have hpair : ∑ m ∈ ({0, 1} : Finset ℕ), (-t) ^ m * w ^ (8 - m) * esD D m = w ^ 8 := by
    rw [Finset.sum_pair (by norm_num)]
    rw [h1, esD_zero]
    ring
  rw [hpair]

/-- The tail is bounded termwise by the `eₘ` bounds. -/
theorem norm_tail_le (w t : ℂ) (D : Fin 8 → ℂ) (c : ℕ → ℝ) (eta : ℝ)
    (hc : ∀ m ∈ Finset.Icc 2 8, ‖esD D m‖ ≤ c m * eta ^ m) :
    ‖∑ m ∈ Finset.Icc 2 8, (-t) ^ m * w ^ (8 - m) * esD D m‖
      ≤ ∑ m ∈ Finset.Icc 2 8, ‖t‖ ^ m * ‖w‖ ^ (8 - m) * (c m * eta ^ m) := by
  calc ‖∑ m ∈ Finset.Icc 2 8, (-t) ^ m * w ^ (8 - m) * esD D m‖
      ≤ ∑ m ∈ Finset.Icc 2 8, ‖(-t) ^ m * w ^ (8 - m) * esD D m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 2 8, ‖t‖ ^ m * ‖w‖ ^ (8 - m) * (c m * eta ^ m) := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg]
        exact mul_le_mul_of_nonneg_left (hc m hm) (by positivity)

end Sendov9

namespace Sendov9

open intervalIntegral

/-!
# The comparison integral `J` (equation 4.6)

`J = ∫₀ᵃ (1 - tμ)⁸ dt`.  Since `t ↦ -(1-tμ)⁹/(9μ)` is an antiderivative,

    J = (1 - (1-aμ)⁹) / (9μ),

and hence, writing `R = |1 - aμ|`,

    |J| ≥ (1 - R⁹)/(9|μ|) ≥ 1/9 + η²/18 - R⁹/(9|μ|),

using `1/√(1-η²) ≥ 1 + η²/2`.  This file banks the closed form and the two bounds;
they are the only places in the whole development that need calculus rather than
algebra.
-/

/-!
### `J` by termwise integration

ℂ-valued calculus over a real interval runs into instance diamonds: `HasDerivAt.pow`
lands on `instCommCStarAlgebraComplex.toAddCommGroup` where the goal wants
`Complex.addCommGroup`, and `convert` then surfaces the diamond as a proof
obligation.  Four attempts down that road all failed the same way.

The integrand is a *polynomial* in `t`, so no calculus is needed: expand
binomially, integrate `∫₀ᵃ tᵏ` termwise through `Complex.ofReal`, and resum.  This
also builds the termwise-integration step that `|I - J|` needs later.
-/

/-- `∫₀ᵃ tᵏ dt` for a ℂ-valued integrand that is really a real one in disguise. -/
theorem integral_cpow_ofReal (a : ℝ) (k : ℕ) :
    (∫ t in (0:ℝ)..a, ((t : ℂ) ^ k)) = ((a ^ (k + 1) / (k + 1) : ℝ) : ℂ) := by
  have h : ∀ t : ℝ, ((t : ℂ) ^ k) = ((t ^ k : ℝ) : ℂ) := by
    intro t; push_cast; ring
  simp only [h]
  rw [intervalIntegral.integral_ofReal, integral_pow]
  push_cast
  simp

/-- Binomial expansion of the integrand. -/
theorem integrand_expand (mu : ℂ) (t : ℝ) :
    (1 - (t : ℂ) * mu) ^ 8
      = ∑ k ∈ Finset.range 9, ((Nat.choose 8 k : ℂ) * (-mu) ^ k) * (t : ℂ) ^ k := by
  have h := add_pow (-((t : ℂ) * mu)) 1 8
  simp only [one_pow, mul_one] at h
  rw [show (1 : ℂ) - (t : ℂ) * mu = -((t : ℂ) * mu) + 1 from by ring, h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (-((t : ℂ) * mu)) = (t : ℂ) * (-mu) from by ring, mul_pow]
  ring

/-- `J` as an explicit finite sum. -/
theorem J_sum (mu : ℂ) (a : ℝ) :
    (∫ t in (0:ℝ)..a, (1 - (t : ℂ) * mu) ^ 8)
      = ∑ k ∈ Finset.range 9,
          ((Nat.choose 8 k : ℂ) * (-mu) ^ k) * ((a ^ (k + 1) / (k + 1) : ℝ) : ℂ) := by
  simp only [integrand_expand mu]
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl fun k _ => by
      rw [intervalIntegral.integral_const_mul, integral_cpow_ofReal]
  · intro k _
    apply Continuous.intervalIntegrable
    continuity

/-- **The closed form.**  `J = (1 - (1-aμ)⁹)/(9μ)`.

With the sum expanded to nine explicit terms this is a rational-function identity,
resting on `C(8,k)/(k+1) = C(9,k+1)/9`. -/
theorem J_closed_form {mu : ℂ} (hmu : mu ≠ 0) (a : ℝ) :
    (∫ t in (0:ℝ)..a, (1 - (t : ℂ) * mu) ^ 8)
      = (1 - (1 - (a : ℂ) * mu) ^ 9) / (9 * mu) := by
  rw [J_sum]
  have hne : (9 : ℂ) * mu ≠ 0 := by
    simp only [ne_eq, mul_eq_zero]
    push_neg
    exact ⟨by norm_num, hmu⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    show Nat.choose 8 0 = 1 from by decide, show Nat.choose 8 1 = 8 from by decide,
    show Nat.choose 8 2 = 28 from by decide, show Nat.choose 8 3 = 56 from by decide,
    show Nat.choose 8 4 = 70 from by decide, show Nat.choose 8 5 = 56 from by decide,
    show Nat.choose 8 6 = 28 from by decide, show Nat.choose 8 7 = 8 from by decide,
    show Nat.choose 8 8 = 1 from by decide]
  push_cast
  rw [eq_div_iff hne]
  ring

/-- `1/√(1-η²) ≥ 1 + η²/2` for `0 ≤ η² < 1` — the step giving `1/9 + η²/18`. -/
theorem inv_sqrt_ge {e : ℝ} (h0 : 0 ≤ e) (h1 : e < 1) :
    1 + e / 2 ≤ 1 / Real.sqrt (1 - e) := by
  have hpos : 0 < 1 - e := by linarith
  have hs : 0 < Real.sqrt (1 - e) := Real.sqrt_pos.mpr hpos
  rw [le_div_iff₀ hs]
  have hsq : Real.sqrt (1 - e) ^ 2 = 1 - e := Real.sq_sqrt (le_of_lt hpos)
  nlinarith [Real.sqrt_nonneg (1 - e), hsq, sq_nonneg (Real.sqrt (1 - e) - 1), sq_nonneg e]

/-- **The `|J|` lower bound.**  With `R = |1 - aμ|` and `|μ| = √(1-η²)`. -/
theorem norm_J_ge {mu : ℂ} (hmu : mu ≠ 0) (a eta : ℝ)
    (heta : ‖mu‖ ^ 2 = 1 - eta ^ 2) (he0 : 0 ≤ eta) (he1 : eta < 1) :
    1 / 9 + eta ^ 2 / 18 - ‖1 - (a : ℂ) * mu‖ ^ 9 / (9 * ‖mu‖)
      ≤ ‖(1 - (1 - (a : ℂ) * mu) ^ 9) / (9 * mu)‖ := by
  have hmn : 0 < ‖mu‖ := norm_pos_iff.mpr hmu
  set R := ‖1 - (a : ℂ) * mu‖ with hR
  have hnum : 1 - R ^ 9 ≤ ‖1 - (1 - (a : ℂ) * mu) ^ 9‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((1 - (a : ℂ) * mu) ^ 9)
    simpa [norm_pow, hR] using this
  have hden : ‖(9 : ℂ) * mu‖ = 9 * ‖mu‖ := by
    rw [norm_mul]; norm_num
  rw [norm_div, hden]
  have hstep : (1 - R ^ 9) / (9 * ‖mu‖) ≤ ‖1 - (1 - (a : ℂ) * mu) ^ 9‖ / (9 * ‖mu‖) := by
    apply div_le_div_of_nonneg_right hnum
    positivity
  refine le_trans ?_ hstep
  have hmnorm : ‖mu‖ = Real.sqrt (1 - eta ^ 2) := by
    rw [← heta, Real.sqrt_sq (norm_nonneg mu)]
  have hkey : 1 + eta ^ 2 / 2 ≤ 1 / ‖mu‖ := by
    rw [hmnorm]
    exact inv_sqrt_ge (by positivity) (by nlinarith)
  have h9 : (0:ℝ) < 9 * ‖mu‖ := by positivity
  have hsplit : (1 - R ^ 9) / (9 * ‖mu‖) = 1 / (9 * ‖mu‖) - R ^ 9 / (9 * ‖mu‖) := by
    ring
  rw [hsplit]
  have hhead : 1 / 9 + eta ^ 2 / 18 ≤ 1 / (9 * ‖mu‖) := by
    rw [le_div_iff₀ h9]
    have hexp : (1 / 9 + eta ^ 2 / 18) * (9 * ‖mu‖) = (1 + eta ^ 2 / 2) * ‖mu‖ := by ring
    rw [hexp]
    calc (1 + eta ^ 2 / 2) * ‖mu‖ ≤ (1 / ‖mu‖) * ‖mu‖ :=
          mul_le_mul_of_nonneg_right hkey (norm_nonneg mu)
      _ = 1 := by field_simp
  linarith

end Sendov9

#print axioms Sendov9.Sigma.spread_at_i
#print axioms Sendov9.Sigma.spread_at_j
#print axioms Sendov9.Sigma.spread_at_other
#print axioms Sendov9.Sigma.spread_prod_eq
#print axioms Sendov9.Sigma.spread_sum_ge
#print axioms Sendov9.Sigma.fac_le_left
#print axioms Sendov9.Sigma.fac_le_right
#print axioms Sendov9.Sigma.fac_hits_endpoint
#print axioms Sendov9.Sigma.one_le_fac
#print axioms Sendov9.Sigma.spread_mem
#print axioms Sendov9.Sigma.spread_interior_subset
#print axioms Sendov9.Sigma.spread_step
#print axioms Sendov9.Sigma.of_base
#print axioms Sendov9.Sigma.step_down
#print axioms Sendov9.Sigma.inv_M_sq_le
#print axioms Sendov9.Sigma.mem_trichotomy
#print axioms Sendov9.Sigma.union_eq_univ
#print axioms Sendov9.Sigma.hi_disj_lo
#print axioms Sendov9.Sigma.hi_disj_int
#print axioms Sendov9.Sigma.lo_disj_int
#print axioms Sendov9.Sigma.sum_split
#print axioms Sendov9.Sigma.prod_split
#print axioms Sendov9.Sigma.card_split
#print axioms Sendov9.esD_zero
#print axioms Sendov9.esD_one
#print axioms Sendov9.prod_sub_eq_sum_esD
#print axioms Sendov9.prod_sub_eq_head_add_tail
#print axioms Sendov9.norm_tail_le
#print axioms Sendov9.integral_cpow_ofReal
#print axioms Sendov9.integrand_expand
#print axioms Sendov9.J_sum
#print axioms Sendov9.J_closed_form
#print axioms Sendov9.inv_sqrt_ge
#print axioms Sendov9.norm_J_ge
