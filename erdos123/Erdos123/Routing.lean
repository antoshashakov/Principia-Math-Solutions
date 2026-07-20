/-
M2 — Chains in the triangular grid (the formalization-friendly form of paper Lemma 4.1).

Instead of general trees we use a single explicit T-shape: a middle row
`rowV q i = (i, q−i, n−q)`, `0 ≤ i ≤ q`, together with a descending path
`pathV q j s = (q−j+s, j, n−q−s)`, `0 ≤ s ≤ n−q`, hanging off the row at `i = q−j`.
Its three extreme vertices lie exactly on the three faces `i = 0`, `j = 0`, `r = 0`.

This file contains:
  * membership of rows/paths in `Tri n` and their adjacency structure;
  * the pigeonhole selection of a row and a path with few marked vertices
    (`exists_sparse_row_and_path`), which for `8·H < n` gives completely clean ones;
  * the propagation algebra along a chain (`seq_propagation`);
  * the three-term Bézout divisibility (`dvd_of_cross`);
  * gcd 1 for the three face weights (`corner_gcd_eq_one`).
-/
import Erdos123.Grid

set_option maxHeartbeats 1000000

namespace Erdos123Band

/-! ## Row and path vertices -/

/-- Row vertex `(i, q−i, n−q)`. -/
def rowV (n q i : ℕ) : ℕ × ℕ × ℕ := (i, q - i, n - q)

/-- Path vertex `(q−j+s, j, n−q−s)`. -/
def pathV (n q j s : ℕ) : ℕ × ℕ × ℕ := (q - j + s, j, n - q - s)

/-- The middle-row parameter window. -/
def midQ (n : ℕ) : Finset ℕ := Finset.Icc ((n + 2) / 3) ((2 * n) / 3)

/-- The central-path parameter window inside row `q`. -/
def midJ (q : ℕ) : Finset ℕ := Finset.Icc ((q + 3) / 4) ((3 * q) / 4)

lemma midQ_card {n : ℕ} (hn : 48 ≤ n) : n ≤ 4 * (midQ n).card := by
  rw [midQ, Nat.card_Icc]
  omega

lemma midJ_card {n q : ℕ} (hn : 48 ≤ n) (hq : q ∈ midQ n) : n ≤ 7 * (midJ q).card := by
  rw [midQ, Finset.mem_Icc] at hq
  rw [midJ, Nat.card_Icc]
  omega

lemma midQ_bounds {n q : ℕ} (hq : q ∈ midQ n) : (n + 2) / 3 ≤ q ∧ q ≤ (2 * n) / 3 := by
  rwa [midQ, Finset.mem_Icc] at hq

lemma midJ_bounds {q j : ℕ} (hj : j ∈ midJ q) : (q + 3) / 4 ≤ j ∧ j ≤ (3 * q) / 4 := by
  rwa [midJ, Finset.mem_Icc] at hj

/-- Rows through the middle window lie in `Tri n`. -/
lemma rowV_mem_Tri {n q i : ℕ} (hn : 48 ≤ n) (hq : q ∈ midQ n) (hi : i ≤ q) :
    rowV n q i ∈ Tri n := by
  obtain ⟨hq1, hq2⟩ := midQ_bounds hq
  refine ⟨by show i + (q - i) + (n - q) = n; omega, ?_, ?_, ?_⟩
  all_goals
    simp only [rowV, ne_eq, Prod.mk.injEq, not_and]
    omega

/-- Paths through the central window lie in `Tri n`. -/
lemma pathV_mem_Tri {n q j s : ℕ} (hn : 48 ≤ n) (hq : q ∈ midQ n) (hj : j ∈ midJ q)
    (hs : s ≤ n - q) :
    pathV n q j s ∈ Tri n := by
  obtain ⟨hq1, hq2⟩ := midQ_bounds hq
  obtain ⟨hj1, hj2⟩ := midJ_bounds hj
  refine ⟨by show q - j + s + j + (n - q - s) = n; omega, ?_, ?_, ?_⟩
  all_goals
    simp only [pathV, ne_eq, Prod.mk.injEq, not_and]
    omega

/-- The path starts on the row: `pathV n q j 0 = rowV n q (q − j)`. -/
lemma pathV_zero {n q j : ℕ} (hj : j ≤ q) : pathV n q j 0 = rowV n q (q - j) := by
  simp only [pathV, rowV, Prod.mk.injEq]
  omega

/-- Consecutive row vertices are within `1` in every coordinate. -/
lemma rowV_adjacent {n q i : ℕ} (hi : i + 1 ≤ q) :
    (rowV n q i).1 ≤ (rowV n q (i + 1)).1 + 1 ∧
    (rowV n q (i + 1)).1 ≤ (rowV n q i).1 + 1 ∧
    (rowV n q i).2.1 ≤ (rowV n q (i + 1)).2.1 + 1 ∧
    (rowV n q (i + 1)).2.1 ≤ (rowV n q i).2.1 + 1 ∧
    (rowV n q i).2.2 ≤ (rowV n q (i + 1)).2.2 + 1 ∧
    (rowV n q (i + 1)).2.2 ≤ (rowV n q i).2.2 + 1 := by
  simp only [rowV]
  omega

/-- Consecutive path vertices are within `1` in every coordinate. -/
lemma pathV_adjacent {n q j s : ℕ} (hj : j ≤ q) (hs : s + 1 ≤ n - q) :
    (pathV n q j s).1 ≤ (pathV n q j (s + 1)).1 + 1 ∧
    (pathV n q j (s + 1)).1 ≤ (pathV n q j s).1 + 1 ∧
    (pathV n q j s).2.1 ≤ (pathV n q j (s + 1)).2.1 + 1 ∧
    (pathV n q j (s + 1)).2.1 ≤ (pathV n q j s).2.1 + 1 ∧
    (pathV n q j s).2.2 ≤ (pathV n q j (s + 1)).2.2 + 1 ∧
    (pathV n q j (s + 1)).2.2 ≤ (pathV n q j s).2.2 + 1 := by
  simp only [pathV]
  omega

/-! ## Pigeonhole selection of a sparse row and path -/

section Selection

variable {n : ℕ}

/-- Marked vertices along row `q`. -/
noncomputable def rowBad (Bad : ℕ × ℕ × ℕ → Prop) (n q : ℕ) : Finset ℕ :=
  letI := Classical.decPred Bad
  (Finset.range (q + 1)).filter (fun i => Bad (rowV n q i))

/-- Marked vertices along path `(q, j)`. -/
noncomputable def pathBad (Bad : ℕ × ℕ × ℕ → Prop) (n q j : ℕ) : Finset ℕ :=
  letI := Classical.decPred Bad
  (Finset.range (n - q + 1)).filter (fun s => Bad (pathV n q j s))

/-- **Sparse row and path.**  If at most `H` vertices of `Tri n` are marked, then some
middle row has at most `4H/n` marked vertices and, within it, some central path has at
most `7H/n` marked vertices (stated in cross-multiplied form).  In particular `8H < n`
forces both to be completely clean. -/
theorem exists_sparse_row_and_path (hn : 48 ≤ n)
    (Bad : ℕ × ℕ × ℕ → Prop) (H : ℕ)
    (hH : ∀ F : Finset (ℕ × ℕ × ℕ), (∀ v ∈ F, v ∈ Tri n ∧ Bad v) → F.card ≤ H) :
    ∃ q ∈ midQ n, ∃ j ∈ midJ q,
      n * (rowBad Bad n q).card ≤ 4 * H ∧
      n * (pathBad Bad n q j).card ≤ 7 * H := by
  classical
  -- row selection
  have hrow_sum : ∑ q ∈ midQ n, (rowBad Bad n q).card ≤ H := by
    -- the images of the rowBad sets under (q, i) ↦ rowV n q i are disjoint marked sets
    set F : Finset (ℕ × ℕ × ℕ) := (midQ n).biUnion (fun q => (rowBad Bad n q).image (rowV n q))
      with hFdef
    have hFsub : ∀ v ∈ F, v ∈ Tri n ∧ Bad v := by
      intro v hv
      simp only [hFdef, Finset.mem_biUnion, Finset.mem_image] at hv
      obtain ⟨q, hq, i, hi, rfl⟩ := hv
      rw [rowBad, Finset.mem_filter, Finset.mem_range] at hi
      exact ⟨rowV_mem_Tri hn hq (by omega), hi.2⟩
    have hFcard : F.card = ∑ q ∈ midQ n, (rowBad Bad n q).card := by
      rw [hFdef, Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro q hq
        apply Finset.card_image_of_injOn
        intro i _ i' _ hii
        have h1 := congrArg (fun v : ℕ × ℕ × ℕ => v.1) hii
        simpa only [rowV] using h1
      · intro q hq q' hq' hqq
        apply Finset.disjoint_left.mpr
        intro v hv hv'
        simp only [Finset.mem_image] at hv hv'
        obtain ⟨i, hi, rfl⟩ := hv
        obtain ⟨i', hi', heq⟩ := hv'
        rw [rowBad, Finset.mem_filter, Finset.mem_range] at hi hi'
        obtain ⟨hq1, hq2⟩ := midQ_bounds hq
        obtain ⟨hq1', hq2'⟩ := midQ_bounds hq'
        -- third coordinates n−q' = n−q force q = q'
        have h3 : n - q' = n - q := by
          have h := congrArg (fun v : ℕ × ℕ × ℕ => v.2.2) heq
          simpa only [rowV] using h
        have h4 : q = q' := by omega
        exact hqq h4
    rw [← hFcard]
    exact hH F hFsub
  have hrow_min : ∃ q ∈ midQ n, (midQ n).card * (rowBad Bad n q).card ≤ H := by
    have hne : (midQ n).Nonempty := by
      rw [← Finset.card_pos]
      have := midQ_card hn
      omega
    obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image (midQ n)
      (fun q => (rowBad Bad n q).card) hne
    refine ⟨q, hq, ?_⟩
    calc (midQ n).card * (rowBad Bad n q).card
        = ∑ _q' ∈ midQ n, (rowBad Bad n q).card := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ q' ∈ midQ n, (rowBad Bad n q').card :=
          Finset.sum_le_sum (fun q' hq' => hmin q' hq')
      _ ≤ H := hrow_sum
  obtain ⟨q, hq, hrowq⟩ := hrow_min
  -- path selection within row q
  have hpath_sum : ∑ j ∈ midJ q, (pathBad Bad n q j).card ≤ H := by
    set F : Finset (ℕ × ℕ × ℕ) :=
      (midJ q).biUnion (fun j => (pathBad Bad n q j).image (pathV n q j)) with hFdef
    have hFsub : ∀ v ∈ F, v ∈ Tri n ∧ Bad v := by
      intro v hv
      simp only [hFdef, Finset.mem_biUnion, Finset.mem_image] at hv
      obtain ⟨j, hj, s, hs, rfl⟩ := hv
      rw [pathBad, Finset.mem_filter, Finset.mem_range] at hs
      exact ⟨pathV_mem_Tri hn hq hj (by omega), hs.2⟩
    have hFcard : F.card = ∑ j ∈ midJ q, (pathBad Bad n q j).card := by
      rw [hFdef, Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro j hj
        apply Finset.card_image_of_injOn
        intro s hs s' hs' hss
        rw [Finset.mem_coe, pathBad, Finset.mem_filter, Finset.mem_range] at hs hs'
        have h3 := congrArg (fun v : ℕ × ℕ × ℕ => v.2.2) hss
        simp only [pathV] at h3
        obtain ⟨hq1, hq2⟩ := midQ_bounds hq
        omega
      · intro j hj j' hj' hjj
        apply Finset.disjoint_left.mpr
        intro v hv hv'
        simp only [Finset.mem_image] at hv hv'
        obtain ⟨s, hs, rfl⟩ := hv
        obtain ⟨s', hs', heq⟩ := hv'
        have h2 := congrArg (fun v : ℕ × ℕ × ℕ => v.2.1) heq
        simp only [pathV] at h2
        exact hjj h2.symm
    rw [← hFcard]
    exact hH F hFsub
  have hpath_min : ∃ j ∈ midJ q, (midJ q).card * (pathBad Bad n q j).card ≤ H := by
    have hne : (midJ q).Nonempty := by
      rw [← Finset.card_pos]
      have := midJ_card hn hq
      omega
    obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (midJ q)
      (fun j => (pathBad Bad n q j).card) hne
    refine ⟨j, hj, ?_⟩
    calc (midJ q).card * (pathBad Bad n q j).card
        = ∑ _j' ∈ midJ q, (pathBad Bad n q j).card := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ j' ∈ midJ q, (pathBad Bad n q j').card :=
          Finset.sum_le_sum (fun j' hj' => hmin j' hj')
      _ ≤ H := hpath_sum
  obtain ⟨j, hj, hpathj⟩ := hpath_min
  refine ⟨q, hq, j, hj, ?_, ?_⟩
  · calc n * (rowBad Bad n q).card ≤ 4 * (midQ n).card * (rowBad Bad n q).card := by
          have := midQ_card hn
          exact Nat.mul_le_mul_right _ this
      _ = 4 * ((midQ n).card * (rowBad Bad n q).card) := by ring
      _ ≤ 4 * H := Nat.mul_le_mul_left _ hrowq
  · calc n * (pathBad Bad n q j).card ≤ 7 * (midJ q).card * (pathBad Bad n q j).card := by
          have := midJ_card hn hq
          exact Nat.mul_le_mul_right _ this
      _ = 7 * ((midJ q).card * (pathBad Bad n q j).card) := by ring
      _ ≤ 7 * H := Nat.mul_le_mul_left _ hpathj

end Selection

/-! ## Propagation algebra along a chain -/

/-- **Cross-ratio propagation.**  Along a finite sequence of positive weights `s` with
edge relations `A i * s i = B i * s (i+1)` (`A, B` positive) and integer values `d`
satisfying the same-shaped relations `B i * d (i+1) = A i * d i`, all cross-ratios agree:
`d i * s j = d j * s i`. -/
theorem seq_propagation {M : ℕ} (s : ℕ → ℕ) (d : ℕ → ℤ) (A B : ℕ → ℕ)
    (hs : ∀ i, i ≤ M → 0 < s i)
    (hB : ∀ i, i < M → 0 < B i)
    (hrel : ∀ i, i < M → A i * s i = B i * s (i + 1))
    (hd : ∀ i, i < M → (B i : ℤ) * d (i + 1) = (A i : ℤ) * d i) :
    ∀ i, i ≤ M → ∀ j, j ≤ M → d i * (s j : ℤ) = d j * (s i : ℤ) := by
  -- consecutive cross-ratios
  have hstep : ∀ i, i < M → d i * (s (i + 1) : ℤ) = d (i + 1) * (s i : ℤ) := by
    intro i hi
    have h1 : (A i : ℤ) * (s i : ℤ) = (B i : ℤ) * (s (i + 1) : ℤ) := by
      exact_mod_cast hrel i hi
    have h2 := hd i hi
    have hBpos : (0 : ℤ) < (B i : ℤ) := by exact_mod_cast hB i hi
    -- B i * (d i * s (i+1)) = d i * (B i * s (i+1)) = d i * A i * s i
    -- B i * (d (i+1) * s i) = (B i * d (i+1)) * s i = A i * d i * s i
    have h3 : (B i : ℤ) * (d i * (s (i + 1) : ℤ)) = (B i : ℤ) * (d (i + 1) * (s i : ℤ)) := by
      calc (B i : ℤ) * (d i * (s (i + 1) : ℤ))
          = d i * ((B i : ℤ) * (s (i + 1) : ℤ)) := by ring
        _ = d i * ((A i : ℤ) * (s i : ℤ)) := by rw [← h1]
        _ = ((B i : ℤ) * d (i + 1)) * (s i : ℤ) := by rw [h2]; ring
        _ = (B i : ℤ) * (d (i + 1) * (s i : ℤ)) := by ring
    exact mul_left_cancel₀ hBpos.ne' h3
  -- from index 0
  have hzero : ∀ i, i ≤ M → d 0 * (s i : ℤ) = d i * (s 0 : ℤ) := by
    intro i
    induction i with
    | zero => intro _; ring
    | succ k ih =>
      intro hk
      have hk' : k ≤ M := by omega
      have hkM : k < M := by omega
      have h1 := ih hk'
      have h2 := hstep k hkM
      have hskpos : (0 : ℤ) < (s k : ℤ) := by exact_mod_cast hs k hk'
      -- d0 * s(k+1) * s k = d0 * s k * s (k+1) = d k * s 0 * s (k+1)
      --   = s 0 * (d k * s (k+1)) = s 0 * (d (k+1) * s k) = d (k+1) * s 0 * s k
      have h3 : (d 0 * (s (k + 1) : ℤ)) * (s k : ℤ) = (d (k + 1) * (s 0 : ℤ)) * (s k : ℤ) := by
        calc (d 0 * (s (k + 1) : ℤ)) * (s k : ℤ)
            = (d 0 * (s k : ℤ)) * (s (k + 1) : ℤ) := by ring
          _ = (d k * (s 0 : ℤ)) * (s (k + 1) : ℤ) := by rw [h1]
          _ = (s 0 : ℤ) * (d k * (s (k + 1) : ℤ)) := by ring
          _ = (s 0 : ℤ) * (d (k + 1) * (s k : ℤ)) := by rw [h2]
          _ = (d (k + 1) * (s 0 : ℤ)) * (s k : ℤ) := by ring
      exact mul_right_cancel₀ hskpos.ne' h3
  intro i hi j hj
  have h1 := hzero i hi
  have h2 := hzero j hj
  have hs0pos : (0 : ℤ) < (s 0 : ℤ) := by exact_mod_cast hs 0 (by omega)
  have h3 : (d i * (s j : ℤ)) * (s 0 : ℤ) = (d j * (s i : ℤ)) * (s 0 : ℤ) := by
    calc (d i * (s j : ℤ)) * (s 0 : ℤ)
        = (d i * (s 0 : ℤ)) * (s j : ℤ) := by ring
      _ = (d 0 * (s i : ℤ)) * (s j : ℤ) := by rw [← h1]
      _ = (d 0 * (s j : ℤ)) * (s i : ℤ) := by ring
      _ = (d j * (s 0 : ℤ)) * (s i : ℤ) := by rw [h2]
      _ = (d j * (s i : ℤ)) * (s 0 : ℤ) := by ring
  exact mul_right_cancel₀ hs0pos.ne' h3

/-- **Three-term Bézout divisibility.**  If `gcd (gcd s₁ s₂) s₃ = 1` and the cross-ratio
relations `d₀ sᵢ = dᵢ s₀` hold, then `s₀ ∣ d₀`. -/
theorem dvd_of_cross {s₀ s₁ s₂ s₃ : ℕ} {d₀ d₁ d₂ d₃ : ℤ}
    (hgcd : Nat.gcd (Nat.gcd s₁ s₂) s₃ = 1)
    (h1 : d₀ * (s₁ : ℤ) = d₁ * (s₀ : ℤ))
    (h2 : d₀ * (s₂ : ℤ) = d₂ * (s₀ : ℤ))
    (h3 : d₀ * (s₃ : ℤ) = d₃ * (s₀ : ℤ)) :
    (s₀ : ℤ) ∣ d₀ := by
  -- Bézout for gcd s₁ s₂
  have hb1 : (Nat.gcd s₁ s₂ : ℤ) = s₁ * Nat.gcdA s₁ s₂ + s₂ * Nat.gcdB s₁ s₂ :=
    Nat.gcd_eq_gcd_ab s₁ s₂
  have hb2 : (Nat.gcd (Nat.gcd s₁ s₂) s₃ : ℤ)
      = (Nat.gcd s₁ s₂ : ℤ) * Nat.gcdA (Nat.gcd s₁ s₂) s₃
        + s₃ * Nat.gcdB (Nat.gcd s₁ s₂) s₃ :=
    Nat.gcd_eq_gcd_ab (Nat.gcd s₁ s₂) s₃
  set u : ℤ := Nat.gcdA s₁ s₂ * Nat.gcdA (Nat.gcd s₁ s₂) s₃ with hu
  set v : ℤ := Nat.gcdB s₁ s₂ * Nat.gcdA (Nat.gcd s₁ s₂) s₃ with hv
  set w : ℤ := Nat.gcdB (Nat.gcd s₁ s₂) s₃ with hw
  have hone : (1 : ℤ) = (s₁ : ℤ) * u + (s₂ : ℤ) * v + (s₃ : ℤ) * w := by
    have hcast : ((Nat.gcd (Nat.gcd s₁ s₂) s₃ : ℕ) : ℤ) = 1 := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hgcd
    calc (1 : ℤ) = (Nat.gcd (Nat.gcd s₁ s₂) s₃ : ℤ) := hcast.symm
      _ = (Nat.gcd s₁ s₂ : ℤ) * Nat.gcdA (Nat.gcd s₁ s₂) s₃
            + s₃ * Nat.gcdB (Nat.gcd s₁ s₂) s₃ := hb2
      _ = (s₁ * Nat.gcdA s₁ s₂ + s₂ * Nat.gcdB s₁ s₂) * Nat.gcdA (Nat.gcd s₁ s₂) s₃
            + s₃ * Nat.gcdB (Nat.gcd s₁ s₂) s₃ := by rw [← hb1]
      _ = (s₁ : ℤ) * u + (s₂ : ℤ) * v + (s₃ : ℤ) * w := by
          simp only [hu, hv, hw]; ring
  refine ⟨d₁ * u + d₂ * v + d₃ * w, ?_⟩
  calc d₀ = d₀ * 1 := (mul_one d₀).symm
    _ = d₀ * ((s₁ : ℤ) * u + (s₂ : ℤ) * v + (s₃ : ℤ) * w) := by rw [← hone]
    _ = (d₀ * (s₁ : ℤ)) * u + (d₀ * (s₂ : ℤ)) * v + (d₀ * (s₃ : ℤ)) * w := by ring
    _ = (d₁ * (s₀ : ℤ)) * u + (d₂ * (s₀ : ℤ)) * v + (d₃ * (s₀ : ℤ)) * w := by
        rw [h1, h2, h3]
    _ = (s₀ : ℤ) * (d₁ * u + d₂ * v + d₃ * w) := by ring

/-- **Chain divisibility.**  A row sequence `rS` (indices `0..q`) and a path sequence
`pS` (indices `0..P`) with matching edge relations for weights and values, joined at
`pS 0 = rS j`, whose three extreme weights `rS 0, rS q, pS P` have gcd `1`, force
`rS 0 ∣ rd 0`. -/
theorem chain_dvd {q P : ℕ} (rS pS : ℕ → ℕ) (rd pd : ℕ → ℤ)
    (rA rB pA pB : ℕ → ℕ)
    (hrs : ∀ i, i ≤ q → 0 < rS i) (hps : ∀ s, s ≤ P → 0 < pS s)
    (hrB : ∀ i, i < q → 0 < rB i) (hpB : ∀ s, s < P → 0 < pB s)
    (hrrel : ∀ i, i < q → rA i * rS i = rB i * rS (i + 1))
    (hprel : ∀ s, s < P → pA s * pS s = pB s * pS (s + 1))
    (hrd : ∀ i, i < q → (rB i : ℤ) * rd (i + 1) = (rA i : ℤ) * rd i)
    (hpd : ∀ s, s < P → (pB s : ℤ) * pd (s + 1) = (pA s : ℤ) * pd s)
    (j : ℕ) (hj : j ≤ q)
    (hjunc_s : pS 0 = rS j) (hjunc_d : pd 0 = rd j)
    (hgcd : Nat.gcd (Nat.gcd (rS 0) (rS q)) (pS P) = 1) :
    (rS 0 : ℤ) ∣ rd 0 := by
  have hrow := seq_propagation rS rd rA rB hrs hrB hrrel hrd
  have hpath := seq_propagation pS pd pA pB hps hpB hprel hpd
  -- cross-ratio to the row end
  have hcross2 : rd 0 * (rS q : ℤ) = rd q * (rS 0 : ℤ) :=
    hrow 0 (by omega) q (by omega)
  -- cross-ratio to the path end, through the junction
  have hpj : pd 0 * (pS P : ℤ) = pd P * (pS 0 : ℤ) :=
    hpath 0 (by omega) P (by omega)
  have hrj : rd 0 * (rS j : ℤ) = rd j * (rS 0 : ℤ) :=
    hrow 0 (by omega) j hj
  have hsjpos : (0 : ℤ) < (rS j : ℤ) := by exact_mod_cast hrs j hj
  have hcross3 : rd 0 * (pS P : ℤ) = pd P * (rS 0 : ℤ) := by
    have h1 : (rd 0 * (pS P : ℤ)) * (rS j : ℤ) = (pd P * (rS 0 : ℤ)) * (rS j : ℤ) := by
      calc (rd 0 * (pS P : ℤ)) * (rS j : ℤ)
          = (rd 0 * (rS j : ℤ)) * (pS P : ℤ) := by ring
        _ = (rd j * (rS 0 : ℤ)) * (pS P : ℤ) := by rw [hrj]
        _ = (rS 0 : ℤ) * (rd j * (pS P : ℤ)) := by ring
        _ = (rS 0 : ℤ) * (pd 0 * (pS P : ℤ)) := by rw [hjunc_d]
        _ = (rS 0 : ℤ) * (pd P * (pS 0 : ℤ)) := by rw [hpj]
        _ = (rS 0 : ℤ) * (pd P * (rS j : ℤ)) := by rw [hjunc_s]
        _ = (pd P * (rS 0 : ℤ)) * (rS j : ℤ) := by ring
    exact mul_right_cancel₀ hsjpos.ne' h1
  exact dvd_of_cross hgcd (by ring) hcross2 hcross3

/-! ## The face-weight gcd -/

section CornerGcd

variable {a b c : ℕ}

/-- The three face weights `b^ℓ₁ c^m₁`, `a^k₂ c^m₂`, `a^k₃ b^ℓ₃` have gcd `1`. -/
theorem corner_gcd_eq_one (hco : PairwiseCoprime3 a b c)
    (l₁ m₁ k₂ m₂ k₃ l₃ : ℕ) :
    Nat.gcd (Nat.gcd (b ^ l₁ * c ^ m₁) (a ^ k₂ * c ^ m₂)) (a ^ k₃ * b ^ l₃) = 1 := by
  obtain ⟨hab, hac, hbc⟩ := hco
  have hcop : Nat.Coprime (Nat.gcd (b ^ l₁ * c ^ m₁) (a ^ k₂ * c ^ m₂)) (a ^ k₃ * b ^ l₃) := by
    apply Nat.Coprime.mul_right
    · -- coprime to a^k₃ via the first component
      apply Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _)
      exact Nat.Coprime.mul (hab.symm.pow l₁ k₃) (hac.symm.pow m₁ k₃)
    · -- coprime to b^l₃ via the second component
      apply Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _)
      exact Nat.Coprime.mul (hab.pow k₂ l₃) (hbc.symm.pow m₂ l₃)
  exact hcop

end CornerGcd

/-! ## Edge coefficients from bounded exponent jumps -/

section EdgeCoeffs

variable {a b c : ℕ}

/-- The positive-part edge coefficient: for exponent triples `e, e'`,
`edgeA e e' * wt e = edgeB e e' * wt e'` where `edgeB e e' = edgeA e' e`. -/
def edgeA (a b c : ℕ) (e e' : ℕ × ℕ × ℕ) : ℕ :=
  a ^ (e'.1 - e.1) * b ^ (e'.2.1 - e.2.1) * c ^ (e'.2.2 - e.2.2)

lemma edgeA_pos (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (e e' : ℕ × ℕ × ℕ) :
    0 < edgeA a b c e e' := by
  unfold edgeA
  positivity

/-- The fundamental edge relation `edgeA e e' * wt e = edgeA e' e * wt e'`. -/
lemma edgeA_mul_wt (a b c : ℕ) (e e' : ℕ × ℕ × ℕ) :
    edgeA a b c e e' * wt a b c e = edgeA a b c e' e * wt a b c e' := by
  unfold edgeA wt
  have h1 : e'.1 - e.1 + e.1 = e.1 - e'.1 + e'.1 := by omega
  have h2 : e'.2.1 - e.2.1 + e.2.1 = e.2.1 - e'.2.1 + e'.2.1 := by omega
  have h3 : e'.2.2 - e.2.2 + e.2.2 = e.2.2 - e'.2.2 + e'.2.2 := by omega
  calc a ^ (e'.1 - e.1) * b ^ (e'.2.1 - e.2.1) * c ^ (e'.2.2 - e.2.2)
        * (a ^ e.1 * b ^ e.2.1 * c ^ e.2.2)
      = a ^ (e'.1 - e.1 + e.1) * b ^ (e'.2.1 - e.2.1 + e.2.1)
          * c ^ (e'.2.2 - e.2.2 + e.2.2) := by
        rw [pow_add, pow_add, pow_add]; ring
    _ = a ^ (e.1 - e'.1 + e'.1) * b ^ (e.2.1 - e'.2.1 + e'.2.1)
          * c ^ (e.2.2 - e'.2.2 + e'.2.2) := by rw [h1, h2, h3]
    _ = a ^ (e.1 - e'.1) * b ^ (e.2.1 - e'.2.1) * c ^ (e.2.2 - e'.2.2)
          * (a ^ e'.1 * b ^ e'.2.1 * c ^ e'.2.2) := by
        rw [pow_add, pow_add, pow_add]; ring

/-- If the exponent jumps are at most `D`, the edge coefficient is at most `(abc)^D`. -/
lemma edgeA_le (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) {D : ℕ} {e e' : ℕ × ℕ × ℕ}
    (h1 : e'.1 ≤ e.1 + D) (h2 : e'.2.1 ≤ e.2.1 + D) (h3 : e'.2.2 ≤ e.2.2 + D) :
    edgeA a b c e e' ≤ (a * b * c) ^ D := by
  unfold edgeA
  have e1 : a ^ (e'.1 - e.1) ≤ a ^ D := Nat.pow_le_pow_right ha (by omega)
  have e2 : b ^ (e'.2.1 - e.2.1) ≤ b ^ D := Nat.pow_le_pow_right hb (by omega)
  have e3 : c ^ (e'.2.2 - e.2.2) ≤ c ^ D := Nat.pow_le_pow_right hc (by omega)
  calc a ^ (e'.1 - e.1) * b ^ (e'.2.1 - e.2.1) * c ^ (e'.2.2 - e.2.2)
      ≤ a ^ D * b ^ D * c ^ D := by
        apply Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3
    _ = (a * b * c) ^ D := by rw [mul_pow, mul_pow]

end EdgeCoeffs

end Erdos123Band
