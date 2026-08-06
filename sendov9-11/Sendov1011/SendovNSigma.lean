import Mathlib

set_option maxHeartbeats 4000000

/-!
# P4: `SigmaN` — Lemma 2.2 (the σ bound) parametric in `N`, plus the centred expansion

Port of `Sendov9/Sigma22.lean` (the `Sigma` spreading machinery and the `esD` centred
expansion; the `J` material moves to P5) and `Sendov9/Sigma22Gen.lean` (`descent`,
`base_general`, `sigma_bound`, `sigma_le_of`), all over `Fin N` for general `N`.

Degree-specific `8`s become `N`; every card goal closes by `omega`;
`range 9 = {0,1} ∪ Icc 2 8` (a `decide` at degree 9) becomes an `ext`/`omega` argument.
A smoke instance at `N = 9` checks the `interval_cases`/`norm_num` consumption pattern.
-/

namespace SendovN.Sigma

open Finset

variable {N : ℕ}

/-- The strictly-interior coordinates. -/
noncomputable def interior (m M : ℝ) (r : Fin N → ℝ) : Finset (Fin N) :=
  univ.filter (fun k => m < r k ∧ r k < M)

/-- Spreading `(rᵢ, rⱼ) → (rᵢ/c, rⱼ·c)`. -/
noncomputable def spread (r : Fin N → ℝ) (i j : Fin N) (c : ℝ) : Fin N → ℝ :=
  Function.update (Function.update r i (r i / c)) j (r j * c)

@[simp] theorem spread_at_j (r : Fin N → ℝ) (i j : Fin N) (c : ℝ) :
    spread r i j c j = r j * c := by
  simp [spread]

theorem spread_at_i (r : Fin N → ℝ) {i j : Fin N} (hij : i ≠ j) (c : ℝ) :
    spread r i j c i = r i / c := by
  simp [spread, Function.update_of_ne hij]

theorem spread_at_other (r : Fin N → ℝ) {i j k : Fin N} (hki : k ≠ i) (hkj : k ≠ j)
    (c : ℝ) : spread r i j c k = r k := by
  simp [spread, Function.update_of_ne hkj, Function.update_of_ne hki]

/-- The product is preserved. -/
theorem spread_prod_eq (r : Fin N → ℝ) {i j : Fin N} (hij : i ≠ j) {c : ℝ} (hc : c ≠ 0) :
    ∏ k, spread r i j c k = ∏ k, r k := by
  have hj : j ∈ (univ : Finset (Fin N)) := mem_univ j
  have hi' : i ∈ (univ : Finset (Fin N)).erase j := by
    simp [Finset.mem_erase, hij]
  set Q := ∏ x ∈ ((univ : Finset (Fin N)).erase j).erase i, r x with hQ
  have e1 : ∏ k, spread r i j c k
      = (r j * c) * ∏ x ∈ (univ : Finset (Fin N)).erase j,
          Function.update r i (r i / c) x := by
    simp only [spread]
    rw [Finset.prod_update_of_mem hj, Finset.sdiff_singleton_eq_erase]
  have e2 : ∏ x ∈ (univ : Finset (Fin N)).erase j, Function.update r i (r i / c) x
      = (r i / c) * Q := by
    rw [Finset.prod_update_of_mem hi', Finset.sdiff_singleton_eq_erase, hQ]
  have e3 : ∏ k, r k = r j * ∏ x ∈ (univ : Finset (Fin N)).erase j, r x :=
    (Finset.mul_prod_erase _ r hj).symm
  have e4 : ∏ x ∈ (univ : Finset (Fin N)).erase j, r x = r i * Q :=
    (Finset.mul_prod_erase _ r hi').symm
  rw [e1, e2, e3, e4]
  rw [show (r j * c) * ((r i / c) * Q) = (r j * (r i * Q)) * (c / c) from by ring,
    div_self hc, mul_one]

/-- Spreading does not decrease `∑ r⁻²`, given `rᵢ ≤ rⱼ` and `c ≥ 1`. -/
theorem spread_sum_ge (r : Fin N → ℝ) {i j : Fin N} (hij : i ≠ j)
    (hri : 0 < r i) (hrj : 0 < r j) (hle : r i ≤ r j) {c : ℝ} (hc : 1 ≤ c) :
    ∑ k, 1 / (r k) ^ 2 ≤ ∑ k, 1 / (spread r i j c k) ^ 2 := by
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le one_pos hc
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
  have hsub : ({i, j} : Finset (Fin N)) ⊆ univ := subset_univ _
  rw [← Finset.sum_sdiff hsub, ← Finset.sum_sdiff hsub]
  have hrest : ∀ k ∈ (univ : Finset (Fin N)) \ {i, j},
      1 / (spread r i j c k) ^ 2 = 1 / (r k) ^ 2 := by
    intro k hk
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hk
    rw [spread_at_other r hk.2.1 hk.2.2]
  rw [Finset.sum_congr rfl hrest]
  have hpairsum : ∑ k ∈ ({i, j} : Finset (Fin N)), 1 / (r k) ^ 2
      ≤ ∑ k ∈ ({i, j} : Finset (Fin N)), 1 / (spread r i j c k) ^ 2 := by
    rw [Finset.sum_pair hij, Finset.sum_pair hij, spread_at_i r hij, spread_at_j]
    exact hpair
  linarith

/-- The scaling factor `c = min (rᵢ/m) (M/rⱼ)` for interior `i`, `j`. -/
noncomputable def fac (m M : ℝ) (r : Fin N → ℝ) (i j : Fin N) : ℝ :=
  min (r i / m) (M / r j)

theorem fac_le_left (m M : ℝ) (r : Fin N → ℝ) (i j : Fin N) :
    fac m M r i j ≤ r i / m := min_le_left _ _

theorem fac_le_right (m M : ℝ) (r : Fin N → ℝ) (i j : Fin N) :
    fac m M r i j ≤ M / r j := min_le_right _ _

theorem one_le_fac {m M : ℝ} {r : Fin N → ℝ} {i j : Fin N} (hm : 0 < m)
    (hrj : 0 < r j) (hi : m < r i) (hj : r j < M) : 1 ≤ fac m M r i j := by
  refine le_of_lt (lt_min ?_ ?_)
  · rw [lt_div_iff₀ hm]; linarith
  · rw [lt_div_iff₀ hrj]; linarith

/-- At least one of the two scaled coordinates lands on an endpoint. -/
theorem fac_hits_endpoint {m M : ℝ} {r : Fin N → ℝ} {i j : Fin N} (hm : 0 < m)
    (hri : 0 < r i) (hrj : 0 < r j) :
    r i / fac m M r i j = m ∨ r j * fac m M r i j = M := by
  have hm' : m ≠ 0 := ne_of_gt hm
  have hri' : r i ≠ 0 := ne_of_gt hri
  have hrj' : r j ≠ 0 := ne_of_gt hrj
  rcases min_cases (r i / m) (M / r j) with ⟨h, _⟩ | ⟨h, _⟩
  · left; simp only [fac]; rw [h]; field_simp
  · right; simp only [fac]; rw [h]; field_simp

/-- Spreading keeps every coordinate inside `[m,M]`. -/
theorem spread_mem {m M : ℝ} {r : Fin N → ℝ} {i j : Fin N} (hij : i ≠ j) (hm : 0 < m)
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
theorem spread_interior_subset {m M : ℝ} {r : Fin N → ℝ} {i j : Fin N} (hij : i ≠ j)
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
    (ih : ∀ r : Fin N → ℝ, (interior m M r).card ≤ n → (∀ k, m ≤ r k) → (∀ k, r k ≤ M) →
      C ≤ ∏ k, r k → ∑ k, 1 / (r k) ^ 2 ≤ Bound)
    (r : Fin N → ℝ) (hcard : (interior m M r).card ≤ n + 1)
    (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M) (hprod : C ≤ ∏ k, r k)
    (i : Fin N) (hi : i ∈ interior m M r) (j : Fin N) (hj : j ∈ interior m M r)
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

/-- **The induction.**  Given the `≤ 1 interior coordinate` case, the bound holds. -/
theorem of_base (m M C Bound : ℝ) (hm : 0 < m)
    (base : ∀ r : Fin N → ℝ, (∀ k, m ≤ r k) → (∀ k, r k ≤ M) → C ≤ ∏ k, r k →
      (interior m M r).card ≤ 1 → ∑ k, 1 / (r k) ^ 2 ≤ Bound) :
    ∀ (n : ℕ) (r : Fin N → ℝ), (interior m M r).card ≤ n →
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
      rcases le_total (r a) (r b) with hord | hord
      · exact spread_step m M C Bound hm ih r hc hlo hhi hprod a ha b hb hab hord
      · exact spread_step m M C Bound hm ih r hc hlo hhi hprod b hb a ha (Ne.symm hab) hord

/-- The `1/M² ≤ (K/C)²` upgrade. -/
theorem inv_M_sq_le {M C K : ℝ} (hM : 0 < M) (hC : 0 < C) (hK : 0 < K)
    (h : C ≤ M * K) : 1 / M ^ 2 ≤ (K / C) ^ 2 := by
  have h1 : 1 / M ≤ K / C := by
    rw [div_le_div_iff₀ hM hC]
    linarith
  have h2 : (0:ℝ) < 1 / M := by positivity
  calc 1 / M ^ 2 = (1 / M) ^ 2 := by rw [div_pow]; norm_num
    _ ≤ (K / C) ^ 2 := pow_le_pow_left₀ (le_of_lt h2) h1 2

/-! ### The base case's splitting bookkeeping -/

/-- Coordinates sitting at the upper endpoint. -/
noncomputable def atHi (m M : ℝ) (r : Fin N → ℝ) : Finset (Fin N) :=
  univ.filter (fun k => r k = M)

/-- Coordinates sitting at the lower endpoint. -/
noncomputable def atLo (m M : ℝ) (r : Fin N → ℝ) : Finset (Fin N) :=
  univ.filter (fun k => r k = m)

variable {m M : ℝ}

/-- Every coordinate is at `M`, at `m`, or strictly interior — exactly one. -/
theorem mem_trichotomy (hmM : m < M) (r : Fin N → ℝ)
    (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M) (k : Fin N) :
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
theorem union_eq_univ (hmM : m < M) (r : Fin N → ℝ)
    (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M) :
    atHi m M r ∪ atLo m M r ∪ interior m M r = univ := by
  ext k
  simp only [mem_union, mem_univ, iff_true]
  rcases mem_trichotomy hmM r hlo hhi k with ⟨h, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem hi_disj_lo (hmM : m < M) (r : Fin N → ℝ) :
    Disjoint (atHi m M r) (atLo m M r) := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  simp only [atHi, atLo, mem_filter, mem_univ, true_and] at hk hk'
  rw [hk] at hk'; exact absurd hk'.symm (ne_of_lt hmM)

theorem hi_disj_int (r : Fin N → ℝ) : Disjoint (atHi m M r) (interior m M r) := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  simp only [atHi, interior, mem_filter, mem_univ, true_and] at hk hk'
  rw [hk] at hk'; exact absurd hk'.2 (lt_irrefl M)

theorem lo_disj_int (r : Fin N → ℝ) : Disjoint (atLo m M r) (interior m M r) := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  simp only [atLo, interior, mem_filter, mem_univ, true_and] at hk hk'
  rw [hk] at hk'; exact absurd hk'.1 (lt_irrefl m)

/-- **The sum splits.** -/
theorem sum_split (hmM : m < M) (r : Fin N → ℝ)
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
theorem prod_split (hmM : m < M) (r : Fin N → ℝ)
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

/-- The three cardinalities add to `N`. -/
theorem card_split (hmM : m < M) (r : Fin N → ℝ)
    (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M) :
    (atHi m M r).card + (atLo m M r).card + (interior m M r).card = N := by
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

end SendovN.Sigma

namespace SendovN.SigmaGen

open Finset SendovN.Sigma

/-- Moving weight from the lower endpoint to the upper one decreases `∑ r⁻²`. -/
theorem descent {m M : ℝ} (hm : 0 < m) (hmM : m < M) (x y T : ℝ) (hxy : x ≤ y) :
    y / M ^ 2 + (T - y) / m ^ 2 ≤ x / M ^ 2 + (T - x) / m ^ 2 := by
  have hM0 : (0:ℝ) < M := lt_trans hm hmM
  have hm2 : (0:ℝ) < m ^ 2 := by positivity
  have hM2 : (0:ℝ) < M ^ 2 := by positivity
  have hinv : 1 / M ^ 2 ≤ 1 / m ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) hm2
    nlinarith
  have hdiff : y / M ^ 2 + (T - y) / m ^ 2 - (x / M ^ 2 + (T - x) / m ^ 2)
      = (y - x) * (1 / M ^ 2 - 1 / m ^ 2) := by
    field_simp
    ring
  nlinarith [hdiff, hinv, hxy]

/-- **The base case of Lemma 2.2, parametric in `N` and `ν`.** -/
theorem base_general {N : ℕ} {m M C : ℝ} {nu : ℕ} (hm : 0 < m) (hmM : m < M)
    (hC : 0 < C) (hnu1 : 1 ≤ nu) (hnuN : nu ≤ N)
    (hnu_ge : C ≤ M ^ nu * m ^ (N - nu))
    (hnu_min : ∀ j : ℕ, j < nu → M ^ j * m ^ (N - j) < C)
    (r : Fin N → ℝ) (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M)
    (hprod : C ≤ ∏ k, r k) (hcard : (Sigma.interior m M r).card ≤ 1) :
    ∑ k, 1 / (r k) ^ 2
      ≤ ((N - nu : ℕ) : ℝ) / m ^ 2 + ((nu - 1 : ℕ) : ℝ) / M ^ 2
        + (M ^ (nu - 1) * m ^ (N - nu) / C) ^ 2 := by
  have hM0 : (0:ℝ) < M := lt_trans hm hmM
  set K : ℝ := M ^ (nu - 1) * m ^ (N - nu) with hK
  have hK0 : 0 < K := by positivity
  have hMK : M * K = M ^ nu * m ^ (N - nu) := by
    rw [hK, ← mul_assoc, ← pow_succ']
    congr 2
    omega
  have hinvM : 1 / M ^ 2 ≤ (K / C) ^ 2 :=
    Sigma.inv_M_sq_le hM0 hC hK0 (by rw [hMK]; exact hnu_ge)
  have hpeel : ((nu : ℝ) - 1) / M ^ 2 + 1 / M ^ 2 = (nu : ℝ) / M ^ 2 := by
    rw [← add_div]
    congr 1
    ring
  have hpeel' : ((N : ℝ) - 1 - (nu : ℝ)) / m ^ 2 + 1 / m ^ 2
      = ((N : ℝ) - (nu : ℝ)) / m ^ 2 := by
    rw [← add_div]
    congr 1
    ring
  have cN : ((N - nu : ℕ) : ℝ) = (N : ℝ) - (nu : ℝ) := by
    push_cast [Nat.cast_sub hnuN]
    ring
  have c1 : ((nu - 1 : ℕ) : ℝ) = (nu : ℝ) - 1 := by
    push_cast [Nat.cast_sub hnu1]
    ring
  rw [cN, c1]
  have hsum := Sigma.sum_split hmM r hlo hhi
  have hpr := Sigma.prod_split hmM r hlo hhi
  have hcs := Sigma.card_split hmM r hlo hhi
  set h := (Sigma.atHi m M r).card with hh
  set l := (Sigma.atLo m M r).card with hl
  set i := (Sigma.interior m M r).card with hi
  rcases Nat.lt_or_ge i 1 with hi0 | hi1
  · -- `i = 0`: no interior coordinate
    have hzero : i = 0 := by omega
    have hcard0 : (Sigma.interior m M r).card = 0 := by rw [← hi]; exact hzero
    have hempty : Sigma.interior m M r = ∅ := Finset.card_eq_zero.mp hcard0
    have hlN : l = N - h := by omega
    have hhN : h ≤ N := by omega
    have hprodv : ∏ k, r k = M ^ h * m ^ l := by
      rw [hpr, hempty, Finset.prod_empty, mul_one]
    have hsumv : ∑ k, 1 / (r k) ^ 2 = (h : ℝ) / M ^ 2 + (l : ℝ) / m ^ 2 := by
      rw [hsum, hempty, Finset.sum_empty, add_zero]
      ring
    have hhnu : nu ≤ h := by
      by_contra hcon
      push_neg at hcon
      have := hnu_min h hcon
      rw [hlN] at hprodv
      rw [hprodv] at hprod
      linarith
    have hlR : (l : ℝ) = (N : ℝ) - (h : ℝ) := by
      push_cast [hlN, Nat.cast_sub hhN]
      ring
    have hnuR : (nu : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhnu
    have hdes := descent hm hmM (nu : ℝ) (h : ℝ) (N : ℝ) hnuR
    rw [hsumv, hlR]
    linarith [hdes, hinvM, hpeel]
  · -- `i = 1`: exactly one interior coordinate
    have hone : i = 1 := by omega
    have hcard1 : (Sigma.interior m M r).card = 1 := by rw [← hi]; exact hone
    obtain ⟨k0, hk0⟩ := Finset.card_eq_one.mp hcard1
    have hk0mem : k0 ∈ Sigma.interior m M r := by
      rw [hk0]; exact Finset.mem_singleton_self k0
    simp only [Sigma.interior, mem_filter, mem_univ, true_and] at hk0mem
    obtain ⟨hs_lo, hs_hi⟩ := hk0mem
    set s := r k0 with hs
    have hs0 : 0 < s := lt_trans hm hs_lo
    have h1N : 1 ≤ N := by omega
    have hlN1 : l = N - 1 - h := by omega
    have hhN1 : h ≤ N - 1 := by omega
    have hprodv : ∏ k, r k = M ^ h * m ^ l * s := by
      rw [hpr, hk0, Finset.prod_singleton]
    have hsumv : ∑ k, 1 / (r k) ^ 2
        = (h : ℝ) / M ^ 2 + (l : ℝ) / m ^ 2 + 1 / s ^ 2 := by
      rw [hsum, hk0, Finset.sum_singleton]
      ring
    have hlR : (l : ℝ) = (N : ℝ) - 1 - (h : ℝ) := by
      push_cast [hlN1, Nat.cast_sub hhN1, Nat.cast_sub h1N]
      ring
    rcases Nat.lt_or_ge (h + 1) nu with hlt | hge
    · -- `h ≤ ν - 2` is infeasible
      have hkey := hnu_min (h + 1) hlt
      have hexp : M ^ (h + 1) * m ^ (N - (h + 1)) = M ^ h * m ^ l * M := by
        rw [pow_succ]
        have hll : N - (h + 1) = l := by omega
        rw [hll]
        ring
      rw [hexp] at hkey
      have hpos : (0:ℝ) < M ^ h * m ^ l := by positivity
      have : ∏ k, r k < M ^ h * m ^ l * M := by
        rw [hprodv]
        exact mul_lt_mul_of_pos_left hs_hi hpos
      linarith
    · rcases Nat.lt_or_ge h nu with hlt' | hge'
      · -- `h = ν - 1`: the tight case
        have hhv : h = nu - 1 := by omega
        have hlv : l = N - nu := by omega
        have hKs : K * s = M ^ h * m ^ l * s := by rw [hK, hhv, hlv]
        have hsge : C ≤ K * s := by rw [hKs, ← hprodv]; exact hprod
        have hsC : C / K ≤ s := by
          rw [div_le_iff₀ hK0]
          linarith [hsge]
        have hCK0 : (0:ℝ) < C / K := by positivity
        have hinvs : 1 / s ^ 2 ≤ (K / C) ^ 2 := by
          have hsq : (C / K) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (le_of_lt hCK0) hsC 2
          have hd1 : 1 / s ^ 2 ≤ 1 / (C / K) ^ 2 :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
          have hd2 : 1 / (C / K) ^ 2 = (K / C) ^ 2 := by
            rw [div_pow, div_pow]
            field_simp
          linarith [hd1, hd2.le, hd2.ge]
        have hhR : (h : ℝ) = (nu : ℝ) - 1 := by
          push_cast [hhv, Nat.cast_sub hnu1]
          ring
        have hlR' : (l : ℝ) = (N : ℝ) - (nu : ℝ) := by
          push_cast [hlv, Nat.cast_sub hnuN]
          ring
        rw [hsumv, hhR, hlR']
        linarith [hinvs]
      · -- `h ≥ ν`: slide `h` down to `ν`, absorb the interior coordinate at `m`
        have hnuR : (nu : ℝ) ≤ (h : ℝ) := by exact_mod_cast hge'
        have hdes := descent hm hmM (nu : ℝ) (h : ℝ) ((N : ℝ) - 1) hnuR
        have hsm : 1 / s ^ 2 ≤ 1 / m ^ 2 := by
          have hsq : m ^ 2 ≤ s ^ 2 := by nlinarith [hs_lo, hm]
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
        rw [hsumv, hlR]
        linarith [hdes, hinvM, hsm, hpeel, hpeel']

/-- **Lemma 2.2 in general `(N, m, M, C, ν)` form.** -/
theorem sigma_bound {N : ℕ} {m M C : ℝ} {nu : ℕ} (hm : 0 < m) (hmM : m < M)
    (hC : 0 < C) (hnu1 : 1 ≤ nu) (hnuN : nu ≤ N)
    (hnu_ge : C ≤ M ^ nu * m ^ (N - nu))
    (hnu_min : ∀ j : ℕ, j < nu → M ^ j * m ^ (N - j) < C)
    (r : Fin N → ℝ) (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M)
    (hprod : C ≤ ∏ k, r k) :
    ∑ k, 1 / (r k) ^ 2
      ≤ ((N - nu : ℕ) : ℝ) / m ^ 2 + ((nu - 1 : ℕ) : ℝ) / M ^ 2
        + (M ^ (nu - 1) * m ^ (N - nu) / C) ^ 2 :=
  Sigma.of_base m M C _ hm
    (fun r' hlo' hhi' hprod' hcard' =>
      base_general hm hmM hC hnu1 hnuN hnu_ge hnu_min r' hlo' hhi' hprod' hcard')
    N r (by
      have h := Finset.card_le_card (Finset.subset_univ (Sigma.interior m M r))
      simpa using h)
    hlo hhi hprod

/-- The bound in the form the range assembly consumes: a rational `S` dominating it. -/
theorem sigma_le_of {N : ℕ} {m M C S : ℝ} {nu : ℕ} (hm : 0 < m) (hmM : m < M)
    (hC : 0 < C) (hnu1 : 1 ≤ nu) (hnuN : nu ≤ N)
    (hnu_ge : C ≤ M ^ nu * m ^ (N - nu))
    (hnu_min : ∀ j : ℕ, j < nu → M ^ j * m ^ (N - j) < C)
    (hS : ((N - nu : ℕ) : ℝ) / m ^ 2 + ((nu - 1 : ℕ) : ℝ) / M ^ 2
        + (M ^ (nu - 1) * m ^ (N - nu) / C) ^ 2 ≤ S)
    (r : Fin N → ℝ) (hlo : ∀ k, m ≤ r k) (hhi : ∀ k, r k ≤ M)
    (hprod : C ≤ ∏ k, r k) :
    ∑ k, 1 / (r k) ^ 2 ≤ S :=
  le_trans (sigma_bound hm hmM hC hnu1 hnuN hnu_ge hnu_min r hlo hhi hprod) hS

/-- Smoke instance at `N = 9` (the degree-10 shape): confirms the
`interval_cases`/`norm_num` consumption pattern goes through at a general `N`. -/
example (r : Fin 9 → ℝ) (hlo : ∀ k, (1/2 : ℝ) ≤ r k) (hhi : ∀ k, r k ≤ 2)
    (hprod : (4:ℝ) ≤ ∏ k, r k) :
    ∑ k, 1 / (r k) ^ 2 ≤ 15 := by
  refine sigma_le_of (nu := 6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ r hlo hhi hprod
  · intro j hj
    interval_cases j <;> norm_num
  · norm_num

end SendovN.SigmaGen

namespace SendovN

open Finset

/-!
### The centred expansion (equation 3.9), parametric in `N`
-/

variable {N : ℕ}

/-- The `m`-th elementary symmetric function of a family indexed by `Fin N`. -/
noncomputable def esD (D : Fin N → ℂ) (m : ℕ) : ℂ :=
  ∑ s ∈ (univ : Finset (Fin N)).powersetCard m, ∏ j ∈ s, D j

@[simp] theorem esD_zero (D : Fin N → ℂ) : esD D 0 = 1 := by
  simp [esD, Finset.powersetCard_zero]

theorem esD_one (D : Fin N → ℂ) : esD D 1 = ∑ j, D j := by
  simp [esD, Finset.powersetCard_one, Finset.sum_map]

/-- **The centred expansion.**  `∏ⱼ (w - t Dⱼ) = ∑ₘ (-t)^m w^(N-m) eₘ(D)`. -/
theorem prod_sub_eq_sum_esD (w t : ℂ) (D : Fin N → ℂ) :
    ∏ j, (w - t * D j)
      = ∑ m ∈ range (N + 1), (-t) ^ m * w ^ (N - m) * esD D m := by
  have hrw : ∀ j : Fin N, w - t * D j = (-t * D j) + w := by intro j; ring
  calc ∏ j, (w - t * D j) = ∏ j, ((-t * D j) + w) := by
        exact Finset.prod_congr rfl fun j _ => hrw j
    _ = ∑ s ∈ (univ : Finset (Fin N)).powerset,
          (∏ j ∈ s, (-t * D j)) * ∏ _j ∈ univ \ s, w := Finset.prod_add _ _ _
    _ = ∑ m ∈ range (N + 1), ∑ s ∈ (univ : Finset (Fin N)).powersetCard m,
          (∏ j ∈ s, (-t * D j)) * ∏ _j ∈ univ \ s, w := by
        rw [Finset.sum_powerset]
        simp
    _ = ∑ m ∈ range (N + 1), (-t) ^ m * w ^ (N - m) * esD D m := by
        refine Finset.sum_congr rfl fun m hm => ?_
        simp only [mem_range] at hm
        rw [esD, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hcard : s.card = m := (Finset.mem_powersetCard.mp hs).2
        have hsub : s ⊆ univ := (Finset.mem_powersetCard.mp hs).1
        have h1 : ∏ j ∈ s, (-t * D j) = (-t) ^ m * ∏ j ∈ s, D j := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
        have h2 : ∏ _j ∈ (univ : Finset (Fin N)) \ s, w = w ^ (N - m) := by
          have hcompl : (univ : Finset (Fin N)) \ s = sᶜ :=
            (Finset.compl_eq_univ_sdiff s).symm
          rw [Finset.prod_const, hcompl, Finset.card_compl]
          simp [hcard]
        rw [h1, h2]
        ring

/-- With the deviations centred, the `m = 1` term vanishes: `w^N` plus a tail
supported on `2 ≤ m ≤ N`. -/
theorem prod_sub_eq_head_add_tail (hN : 1 ≤ N) (w t : ℂ) (D : Fin N → ℂ)
    (hD : ∑ j, D j = 0) :
    ∏ j, (w - t * D j)
      = w ^ N + ∑ m ∈ Finset.Icc 2 N, (-t) ^ m * w ^ (N - m) * esD D m := by
  rw [prod_sub_eq_sum_esD]
  have h1 : esD D 1 = 0 := by rw [esD_one]; exact hD
  have hsplit : range (N + 1) = {0, 1} ∪ Finset.Icc 2 N := by
    ext x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hdisj : Disjoint ({0, 1} : Finset ℕ) (Finset.Icc 2 N) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc] at hy
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hpair : ∑ m ∈ ({0, 1} : Finset ℕ), (-t) ^ m * w ^ (N - m) * esD D m
      = w ^ N := by
    rw [Finset.sum_pair (by norm_num)]
    rw [h1, esD_zero]
    simp
  rw [hpair]

/-- The tail is bounded termwise by the `eₘ` bounds. -/
theorem norm_tail_le (w t : ℂ) (D : Fin N → ℂ) (c : ℕ → ℝ) (eta : ℝ)
    (hc : ∀ m ∈ Finset.Icc 2 N, ‖esD D m‖ ≤ c m * eta ^ m) :
    ‖∑ m ∈ Finset.Icc 2 N, (-t) ^ m * w ^ (N - m) * esD D m‖
      ≤ ∑ m ∈ Finset.Icc 2 N, ‖t‖ ^ m * ‖w‖ ^ (N - m) * (c m * eta ^ m) := by
  calc ‖∑ m ∈ Finset.Icc 2 N, (-t) ^ m * w ^ (N - m) * esD D m‖
      ≤ ∑ m ∈ Finset.Icc 2 N, ‖(-t) ^ m * w ^ (N - m) * esD D m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 2 N, ‖t‖ ^ m * ‖w‖ ^ (N - m) * (c m * eta ^ m) := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg]
        exact mul_le_mul_of_nonneg_left (hc m hm) (by positivity)

end SendovN

#print axioms SendovN.Sigma.spread_prod_eq
#print axioms SendovN.Sigma.spread_sum_ge
#print axioms SendovN.Sigma.spread_mem
#print axioms SendovN.Sigma.spread_step
#print axioms SendovN.Sigma.of_base
#print axioms SendovN.Sigma.inv_M_sq_le
#print axioms SendovN.Sigma.sum_split
#print axioms SendovN.Sigma.prod_split
#print axioms SendovN.Sigma.card_split
#print axioms SendovN.SigmaGen.descent
#print axioms SendovN.SigmaGen.base_general
#print axioms SendovN.SigmaGen.sigma_bound
#print axioms SendovN.SigmaGen.sigma_le_of
#print axioms SendovN.esD_zero
#print axioms SendovN.esD_one
#print axioms SendovN.prod_sub_eq_sum_esD
#print axioms SendovN.prod_sub_eq_head_add_tail
#print axioms SendovN.norm_tail_le
