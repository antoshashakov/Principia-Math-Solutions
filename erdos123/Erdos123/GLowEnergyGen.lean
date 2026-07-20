/-
GM3b-gen — The low-energy measure bound for the general-ratio band `GBand a b c p q x`
at a GENERAL level `z` (paper FAITHFUL_LCLT.md §3, eq. "low-energy").

  `glow_energy_measure_general` :
      vol {t ∈ [0,1) : GQ_x(t) ≤ z} ≤ (1/x)·exp(C₄·(1 + z/log x)·log(log x + 2))

for all `0 ≤ z ≤ z₀·(log x)²`.

`Erdos123/GLowEnergy.lean` proves exactly this argument at the single level `z = log x`.
The place where the level enters is the bad-vertex count: energy `≤ z` gives `H·δ² ≤ z`
bad vertices, hence a sparse row/path with `≲ z/(δ²·n) ≍ z/(δ²·log x)` marked vertices,
hence a code budget `B ≍ 1 + z/log x` rather than the constant `B` of the fixed level.
The number of codes is then `≍ (n+1)^{2B+2}(2K+2)^{2B}(B+1)²`, whose logarithm is
`≍ (1 + z/log x)·log(log x + 2)`; at `z = log x` this collapses to `(log x)^{O(1)}`,
recovering `glow_energy_measure` up to constants.

STRUCTURE.  All the code apparatus (`rwS`, `pwS`, `rdef`, `pdef`, `CodeT`, `Codes`,
`DefCodes`, `Codes_card_le`, `SCode`, `SCode_defects_eq`, `arc3`, `arc3_volume`,
`mem_arc3`, `rdef_cast`, `pdef_cast`) is level-agnostic and is reused verbatim from
`Erdos123.LowEnergy`; `gchain_diff_dvd` and `gbadF_card_le` are reused from
`Erdos123.GLowEnergy` / `Erdos123.GRigidity`.  The covering argument itself is
isolated here as `gcover_measure_le`, stated for an ARBITRARY level `z` and an
arbitrary code budget `B` subject to the abstract sparsity hypothesis `hB`; the
headline theorem instantiates it and does the (new) counting arithmetic.
-/
import Erdos123.GLowEnergy

set_option maxHeartbeats 4000000

open scoped ENNReal

namespace Erdos123Band

section GCover

/-- **The covering estimate at an arbitrary level `z`.**

Given a grid embedding `Φ : Tri n → ℕ³` into the band `GBand a b c p q x` with
edge-jump constant `D`, a rounding scale `δ` with `2Kδ < 1` where `(abc)^D ≤ K`,
and a code budget `B` large enough to accommodate every sparse row/path admitted at
level `z` (hypothesis `hB`), the level set `{t ∈ [0,1) : GQenergy ≤ z}` is covered by
`(Codes n K B).card` arcs of measure `≤ 3/x` each.

This is the body of `Erdos123Band.glow_energy_measure` with the level `Real.log x`
replaced by the parameter `z`, and with the two numeric bounds on the sparse row/path
cardinalities abstracted into `hB`. -/
theorem gcover_measure_le (a b c p q : ℕ) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q)
    (x n K B D : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (δ z : ℝ)
    (hx1 : 1 ≤ x) (hn48 : 48 ≤ n) (hδ0 : 0 < δ) (h2Kδ : 2 * (K : ℝ) * δ < 1)
    (hKD : (a * b * c) ^ D ≤ K)
    (hband : ∀ v ∈ Tri n, wt a b c (Φ v) ∈ GBand a b c p q x)
    (hinj : ∀ v ∈ Tri n, ∀ w ∈ Tri n, wt a b c (Φ v) = wt a b c (Φ w) → v = w)
    (hface : ∀ v ∈ Tri n,
      (v.1 = 0 → (Φ v).1 = 0) ∧ (v.2.1 = 0 → (Φ v).2.1 = 0) ∧
      (v.2.2 = 0 → (Φ v).2.2 = 0))
    (hjump : ∀ v ∈ Tri n, ∀ w ∈ Tri n,
      (v.1 ≤ w.1 + 1 ∧ w.1 ≤ v.1 + 1 ∧ v.2.1 ≤ w.2.1 + 1 ∧ w.2.1 ≤ v.2.1 + 1 ∧
        v.2.2 ≤ w.2.2 + 1 ∧ w.2.2 ≤ v.2.2 + 1) →
      ((Φ v).1 ≤ (Φ w).1 + D ∧ (Φ w).1 ≤ (Φ v).1 + D ∧
        (Φ v).2.1 ≤ (Φ w).2.1 + D ∧ (Φ w).2.1 ≤ (Φ v).2.1 + D ∧
        (Φ v).2.2 ≤ (Φ w).2.2 + D ∧ (Φ w).2.2 ≤ (Φ v).2.2 + D))
    (hB : ∀ m₁ m₂ : ℕ, (n : ℝ) * m₁ * δ ^ 2 ≤ 4 * z → (n : ℝ) * m₂ * δ ^ 2 ≤ 7 * z →
      2 * (m₁ + m₂ + 2) ≤ B) :
    MeasureTheory.volume
        {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ z}
      ≤ ((Codes n K B).card : ℝ≥0∞) * ENNReal.ofReal (3 / (x : ℝ)) := by
  classical
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hc1 : 1 ≤ c := by omega
  have hwtpos : ∀ v ∈ Tri n, 0 < wt a b c (Φ v) := by
    intro v hv
    have h1 := ((mem_GBand hq).mp (hband v hv)).2.1
    omega
  set E : Set ℝ := {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ z}
    with hEdef
  -- the arc assignment
  set Amap : CodeT → Set ℝ := fun cd =>
    if h : (E ∩ SCode a b c n Φ cd).Nonempty then
      arc3 (rwS a b c n Φ cd.1 0) (rdv a b c n Φ cd.1 h.choose 0) x
    else ∅ with hAmapdef
  -- THE COVERING
  have hcover : ∀ t ∈ E, ∃ cd ∈ Codes n K B, t ∈ Amap cd := by
    intro t htE
    obtain ⟨ht01, htQ⟩ := htE
    obtain ⟨ht0, ht1⟩ := ht01
    -- bad vertices and their count
    set Bad : ℕ × ℕ × ℕ → Prop := fun v =>
      δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| with hBaddef
    set H : ℕ := ((TriF n).filter (fun v =>
      δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)|)).card with hHdef
    have hHQ : (H : ℝ) * δ ^ 2 ≤ GQenergy a b c p q x t :=
      gbadF_card_le a b c p q x n Φ t δ hδ0 hband hinj
    have hHδz : (H : ℝ) * δ ^ 2 ≤ z := le_trans hHQ htQ
    -- the sparse row and path
    have hHhyp : ∀ F : Finset (ℕ × ℕ × ℕ), (∀ v ∈ F, v ∈ Tri n ∧ Bad v) → F.card ≤ H := by
      intro F hF
      rw [hHdef]
      apply Finset.card_le_card
      intro v hv
      obtain ⟨hv1, hv2⟩ := hF v hv
      rw [Finset.mem_filter]
      exact ⟨mem_TriF.mpr hv1, hv2⟩
    obtain ⟨u, hu, j, hj, hrowH, hpathH⟩ := exists_sparse_row_and_path hn48 Bad H hHhyp
    obtain ⟨hu1, hu2⟩ := midQ_bounds hu
    obtain ⟨hj1, hj2⟩ := midJ_bounds hj
    -- the abstract budget hypothesis applies
    have hδ2 : (0 : ℝ) < δ ^ 2 := pow_pos hδ0 2
    have hbudget : 2 * ((rowBad Bad n u).card + (pathBad Bad n u j).card + 2) ≤ B := by
      apply hB
      · have h1 : ((n * (rowBad Bad n u).card : ℕ) : ℝ) ≤ ((4 * H : ℕ) : ℝ) := by
          exact_mod_cast hrowH
        push_cast at h1
        have h2 : (n : ℝ) * (rowBad Bad n u).card * δ ^ 2 ≤ 4 * ((H : ℝ) * δ ^ 2) := by
          nlinarith [h1, hδ2]
        nlinarith [hHδz, h2]
      · have h1 : ((n * (pathBad Bad n u j).card : ℕ) : ℝ) ≤ ((7 * H : ℕ) : ℝ) := by
          exact_mod_cast hpathH
        push_cast at h1
        have h2 : (n : ℝ) * (pathBad Bad n u j).card * δ ^ 2 ≤ 7 * ((H : ℝ) * δ ^ 2) := by
          nlinarith [h1, hδ2]
        nlinarith [hHδz, h2]
    -- edge-coefficient bounds along the chain
    have hrow_coeff : ∀ i, i < u → rwA a b c n Φ u i ≤ K ∧ rwB a b c n Φ u i ≤ K := by
      intro i hi
      have hv := rowV_mem_Tri (n := n) hn48 hu (by omega : i ≤ u)
      have hw := rowV_mem_Tri (n := n) hn48 hu (by omega : i + 1 ≤ u)
      have hadj := rowV_adjacent (n := n) (q := u) (i := i) (by omega)
      have hj6 := hjump _ hv _ hw hadj
      exact ⟨(edgeA_le ha1 hb1 hc1 hj6.2.1 hj6.2.2.2.1 hj6.2.2.2.2.2).trans hKD,
        (edgeA_le ha1 hb1 hc1 hj6.1 hj6.2.2.1 hj6.2.2.2.2.1).trans hKD⟩
    have hpath_coeff : ∀ s, s < n - u →
        pwA a b c n Φ u j s ≤ K ∧ pwB a b c n Φ u j s ≤ K := by
      intro s hs
      have hv := pathV_mem_Tri (n := n) hn48 hu hj (by omega : s ≤ n - u)
      have hw := pathV_mem_Tri (n := n) hn48 hu hj (by omega : s + 1 ≤ n - u)
      have hadj := pathV_adjacent (n := n) (q := u) (j := j) (s := s) (by omega) (by omega)
      have hj6 := hjump _ hv _ hw hadj
      exact ⟨(edgeA_le ha1 hb1 hc1 hj6.2.1 hj6.2.2.2.1 hj6.2.2.2.2.2).trans hKD,
        (edgeA_le ha1 hb1 hc1 hj6.1 hj6.2.2.1 hj6.2.2.2.2.1).trans hKD⟩
    -- defect size bound (always ≤ K)
    have hrdef_le : ∀ i, i < u → rdef a b c n Φ u t i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      intro i hi
      obtain ⟨hA, hB'⟩ := hrow_coeff i hi
      have hid := rdef_cast (a := a) (b := b) (c := c) (n := n) Φ u t i
      have h1 : |(rdv a b c n Φ u t (i + 1) : ℝ) - (rwS a b c n Φ u (i + 1) : ℝ) * t|
          ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have h2 : |(rdv a b c n Φ u t i : ℝ) - (rwS a b c n Φ u i : ℝ) * t| ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have hAR : (rwA a b c n Φ u i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (rwB a b c n Φ u i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB'
      have habs : |((rdef a b c n Φ u t i : ℤ) : ℝ)| ≤ (K : ℝ) := by
        rw [hid]
        have hA0 : (0 : ℝ) ≤ (rwA a b c n Φ u i : ℝ) := by positivity
        have hB0 : (0 : ℝ) ≤ (rwB a b c n Φ u i : ℝ) := by positivity
        calc |(rwB a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t (i + 1) : ℝ) - (rwS a b c n Φ u (i + 1) : ℝ) * t)
            - (rwA a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t i : ℝ) - (rwS a b c n Φ u i : ℝ) * t)|
            ≤ |(rwB a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t (i + 1) : ℝ) - (rwS a b c n Φ u (i + 1) : ℝ) * t)|
              + |(rwA a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t i : ℝ) - (rwS a b c n Φ u i : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (rwB a b c n Φ u i : ℝ) * (1 / 2) + (rwA a b c n Φ u i : ℝ) * (1 / 2) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1 hB0
              · exact mul_le_mul_of_nonneg_left h2 hA0
          _ ≤ (K : ℝ) * (1 / 2) + (K : ℝ) * (1 / 2) := by
              apply add_le_add
              · apply mul_le_mul_of_nonneg_right hBR (by norm_num)
              · apply mul_le_mul_of_nonneg_right hAR (by norm_num)
          _ = (K : ℝ) := by ring
      rw [Finset.mem_Icc]
      have := abs_le.mp habs
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2
    have hpdef_le : ∀ s, s < n - u →
        pdef a b c n Φ u j t s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      intro s hs
      obtain ⟨hA, hB'⟩ := hpath_coeff s hs
      have hid := pdef_cast (a := a) (b := b) (c := c) (n := n) Φ u j t s
      have h1 : |(pdv a b c n Φ u j t (s + 1) : ℝ) - (pwS a b c n Φ u j (s + 1) : ℝ) * t|
          ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have h2 : |(pdv a b c n Φ u j t s : ℝ) - (pwS a b c n Φ u j s : ℝ) * t| ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have hAR : (pwA a b c n Φ u j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (pwB a b c n Φ u j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB'
      have habs : |((pdef a b c n Φ u j t s : ℤ) : ℝ)| ≤ (K : ℝ) := by
        rw [hid]
        have hA0 : (0 : ℝ) ≤ (pwA a b c n Φ u j s : ℝ) := by positivity
        have hB0 : (0 : ℝ) ≤ (pwB a b c n Φ u j s : ℝ) := by positivity
        calc |(pwB a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t (s + 1) : ℝ) - (pwS a b c n Φ u j (s + 1) : ℝ) * t)
            - (pwA a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t s : ℝ) - (pwS a b c n Φ u j s : ℝ) * t)|
            ≤ |(pwB a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t (s + 1) : ℝ) - (pwS a b c n Φ u j (s + 1) : ℝ) * t)|
              + |(pwA a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t s : ℝ) - (pwS a b c n Φ u j s : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (pwB a b c n Φ u j s : ℝ) * (1 / 2) + (pwA a b c n Φ u j s : ℝ) * (1 / 2) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1 hB0
              · exact mul_le_mul_of_nonneg_left h2 hA0
          _ ≤ (K : ℝ) * (1 / 2) + (K : ℝ) * (1 / 2) := by
              apply add_le_add
              · apply mul_le_mul_of_nonneg_right hBR (by norm_num)
              · apply mul_le_mul_of_nonneg_right hAR (by norm_num)
          _ = (K : ℝ) := by ring
      rw [Finset.mem_Icc]
      have := abs_le.mp habs
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2
    -- nonzero defects only next to bad vertices
    have hgood_of_notbad : ∀ v, ¬Bad v →
        |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| ≤ δ := by
      intro v hv
      rw [hBaddef] at hv
      push_neg at hv
      exact hv
    have hrdef_zero : ∀ i, i < u → ¬Bad (rowV n u i) → ¬Bad (rowV n u (i + 1)) →
        rdef a b c n Φ u t i = 0 := by
      intro i hi hg1 hg2
      obtain ⟨hA, hB'⟩ := hrow_coeff i hi
      have hid := rdef_cast (a := a) (b := b) (c := c) (n := n) Φ u t i
      have h1 := hgood_of_notbad _ hg2
      have h2 := hgood_of_notbad _ hg1
      have h1' : |(rdv a b c n Φ u t (i + 1) : ℝ) - (rwS a b c n Φ u (i + 1) : ℝ) * t| ≤ δ := by
        rw [abs_sub_comm]
        exact h1
      have h2' : |(rdv a b c n Φ u t i : ℝ) - (rwS a b c n Φ u i : ℝ) * t| ≤ δ := by
        rw [abs_sub_comm]
        exact h2
      have hAR : (rwA a b c n Φ u i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (rwB a b c n Φ u i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB'
      have hA0 : (0 : ℝ) ≤ (rwA a b c n Φ u i : ℝ) := by positivity
      have hB0 : (0 : ℝ) ≤ (rwB a b c n Φ u i : ℝ) := by positivity
      have habs : |((rdef a b c n Φ u t i : ℤ) : ℝ)| < 1 := by
        rw [hid]
        calc |(rwB a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t (i + 1) : ℝ) - (rwS a b c n Φ u (i + 1) : ℝ) * t)
            - (rwA a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t i : ℝ) - (rwS a b c n Φ u i : ℝ) * t)|
            ≤ |(rwB a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t (i + 1) : ℝ) - (rwS a b c n Φ u (i + 1) : ℝ) * t)|
              + |(rwA a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t i : ℝ) - (rwS a b c n Φ u i : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (rwB a b c n Φ u i : ℝ) * δ + (rwA a b c n Φ u i : ℝ) * δ := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1' hB0
              · exact mul_le_mul_of_nonneg_left h2' hA0
          _ ≤ (K : ℝ) * δ + (K : ℝ) * δ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right hBR hδ0.le
              · exact mul_le_mul_of_nonneg_right hAR hδ0.le
          _ = 2 * (K : ℝ) * δ := by ring
          _ < 1 := h2Kδ
      have h3 : |rdef a b c n Φ u t i| < 1 := by exact_mod_cast habs
      rw [abs_lt] at h3
      omega
    have hpdef_zero : ∀ s, s < n - u → ¬Bad (pathV n u j s) → ¬Bad (pathV n u j (s + 1)) →
        pdef a b c n Φ u j t s = 0 := by
      intro s hs hg1 hg2
      obtain ⟨hA, hB'⟩ := hpath_coeff s hs
      have hid := pdef_cast (a := a) (b := b) (c := c) (n := n) Φ u j t s
      have h1 := hgood_of_notbad _ hg2
      have h2 := hgood_of_notbad _ hg1
      have h1' : |(pdv a b c n Φ u j t (s + 1) : ℝ) - (pwS a b c n Φ u j (s + 1) : ℝ) * t|
          ≤ δ := by
        rw [abs_sub_comm]
        exact h1
      have h2' : |(pdv a b c n Φ u j t s : ℝ) - (pwS a b c n Φ u j s : ℝ) * t| ≤ δ := by
        rw [abs_sub_comm]
        exact h2
      have hAR : (pwA a b c n Φ u j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (pwB a b c n Φ u j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB'
      have hA0 : (0 : ℝ) ≤ (pwA a b c n Φ u j s : ℝ) := by positivity
      have hB0 : (0 : ℝ) ≤ (pwB a b c n Φ u j s : ℝ) := by positivity
      have habs : |((pdef a b c n Φ u j t s : ℤ) : ℝ)| < 1 := by
        rw [hid]
        calc |(pwB a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t (s + 1) : ℝ) - (pwS a b c n Φ u j (s + 1) : ℝ) * t)
            - (pwA a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t s : ℝ) - (pwS a b c n Φ u j s : ℝ) * t)|
            ≤ |(pwB a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t (s + 1) : ℝ) - (pwS a b c n Φ u j (s + 1) : ℝ) * t)|
              + |(pwA a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t s : ℝ) - (pwS a b c n Φ u j s : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (pwB a b c n Φ u j s : ℝ) * δ + (pwA a b c n Φ u j s : ℝ) * δ := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1' hB0
              · exact mul_le_mul_of_nonneg_left h2' hA0
          _ ≤ (K : ℝ) * δ + (K : ℝ) * δ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right hBR hδ0.le
              · exact mul_le_mul_of_nonneg_right hAR hδ0.le
          _ = 2 * (K : ℝ) * δ := by ring
          _ < 1 := h2Kδ
      have h3 : |pdef a b c n Φ u j t s| < 1 := by exact_mod_cast habs
      rw [abs_lt] at h3
      omega
    -- the defect tables
    set rdfF : Finset ℕ := (Finset.range u).filter (fun i => rdef a b c n Φ u t i ≠ 0)
      with hrdfFdef
    set pdfF : Finset ℕ :=
      (Finset.range (n - u)).filter (fun s => pdef a b c n Φ u j t s ≠ 0) with hpdfFdef
    set rdf : Finset (ℕ × ℤ) := rdfF.image (fun i => (i, rdef a b c n Φ u t i)) with hrdfdef
    set pdf : Finset (ℕ × ℤ) := pdfF.image (fun s => (s, pdef a b c n Φ u j t s))
      with hpdfdef
    -- their sizes
    have hrdfF_sub : rdfF ⊆ (rowBad Bad n u) ∪ (rowBad Bad n u).image (fun i => i - 1) := by
      intro i hi
      rw [hrdfFdef, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hiq, hine⟩ := hi
      by_cases hbb1 : Bad (rowV n u i)
      · apply Finset.mem_union_left
        rw [rowBad, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hbb1⟩
      · by_cases hbb2 : Bad (rowV n u (i + 1))
        · apply Finset.mem_union_right
          rw [Finset.mem_image]
          refine ⟨i + 1, ?_, by omega⟩
          rw [rowBad, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hbb2⟩
        · exact absurd (hrdef_zero i hiq hbb1 hbb2) hine
    have hpdfF_sub :
        pdfF ⊆ (pathBad Bad n u j) ∪ (pathBad Bad n u j).image (fun s => s - 1) := by
      intro s hs
      rw [hpdfFdef, Finset.mem_filter, Finset.mem_range] at hs
      obtain ⟨hsq, hsne⟩ := hs
      by_cases hbb1 : Bad (pathV n u j s)
      · apply Finset.mem_union_left
        rw [pathBad, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hbb1⟩
      · by_cases hbb2 : Bad (pathV n u j (s + 1))
        · apply Finset.mem_union_right
          rw [Finset.mem_image]
          refine ⟨s + 1, ?_, by omega⟩
          rw [pathBad, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hbb2⟩
        · exact absurd (hpdef_zero s hsq hbb1 hbb2) hsne
    have hrdf_card : rdf.card ≤ B := by
      have him := Finset.card_image_le (s := rowBad Bad n u) (f := fun i => i - 1)
      calc rdf.card ≤ rdfF.card := Finset.card_image_le
        _ ≤ ((rowBad Bad n u) ∪ (rowBad Bad n u).image (fun i => i - 1)).card :=
            Finset.card_le_card hrdfF_sub
        _ ≤ (rowBad Bad n u).card + ((rowBad Bad n u).image (fun i => i - 1)).card :=
            Finset.card_union_le _ _
        _ ≤ B := by omega
    have hpdf_card : pdf.card ≤ B := by
      have him := Finset.card_image_le (s := pathBad Bad n u j) (f := fun s => s - 1)
      calc pdf.card ≤ pdfF.card := Finset.card_image_le
        _ ≤ ((pathBad Bad n u j) ∪ (pathBad Bad n u j).image (fun s => s - 1)).card :=
            Finset.card_le_card hpdfF_sub
        _ ≤ (pathBad Bad n u j).card + ((pathBad Bad n u j).image (fun s => s - 1)).card :=
            Finset.card_union_le _ _
        _ ≤ B := by omega
    -- the code and its membership
    have hcdmem : ((u, j, rdf, pdf) : CodeT) ∈ Codes n K B := by
      rw [Codes]
      simp only [Finset.mem_product, Finset.mem_range]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [DefCodes, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · intro pt hpt
          rw [hrdfdef, Finset.mem_image] at hpt
          obtain ⟨i, hi, rfl⟩ := hpt
          rw [hrdfFdef, Finset.mem_filter, Finset.mem_range] at hi
          simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨by omega, hrdef_le i hi.1⟩
        · exact hrdf_card
      · rw [DefCodes, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · intro pt hpt
          rw [hpdfdef, Finset.mem_image] at hpt
          obtain ⟨s, hs, rfl⟩ := hpt
          rw [hpdfFdef, Finset.mem_filter, Finset.mem_range] at hs
          simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨by omega, hpdef_le s hs.1⟩
        · exact hpdf_card
    -- t is compatible with its own code
    have hrdf_fst : rdf.image Prod.fst = rdfF := by
      rw [hrdfdef, Finset.image_image]
      exact Finset.image_id'
    have hpdf_fst : pdf.image Prod.fst = pdfF := by
      rw [hpdfdef, Finset.image_image]
      exact Finset.image_id'
    have htS : t ∈ SCode a b c n Φ (u, j, rdf, pdf) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro pt hpt
        rw [hrdfdef, Finset.mem_image] at hpt
        obtain ⟨i, _, rfl⟩ := hpt
        rfl
      · intro i hi hnot
        rw [show ((u, j, rdf, pdf) : CodeT).2.2.1 = rdf from rfl, hrdf_fst, hrdfFdef] at hnot
        by_contra hne
        exact hnot (by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hi, hne⟩)
      · intro pt hpt
        rw [hpdfdef, Finset.mem_image] at hpt
        obtain ⟨s, _, rfl⟩ := hpt
        rfl
      · intro s hs hnot
        rw [show ((u, j, rdf, pdf) : CodeT).2.2.2 = pdf from rfl, hpdf_fst, hpdfFdef] at hnot
        by_contra hne
        exact hnot (by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hs, hne⟩)
    -- the arc trap
    have hne : (E ∩ SCode a b c n Φ (u, j, rdf, pdf)).Nonempty :=
      ⟨t, ⟨⟨ht0, ht1⟩, htQ⟩, htS⟩
    refine ⟨(u, j, rdf, pdf), hcdmem, ?_⟩
    have hAeq : Amap (u, j, rdf, pdf)
        = arc3 (rwS a b c n Φ u 0) (rdv a b c n Φ u hne.choose 0) x := by
      rw [hAmapdef]
      exact dif_pos hne
    rw [hAeq]
    obtain ⟨ht'E, ht'S⟩ := hne.choose_spec
    obtain ⟨⟨ht'0, ht'1⟩, _⟩ := ht'E
    obtain ⟨hdefr, hdefp⟩ := SCode_defects_eq (a := a) (b := b) (c := c) htS ht'S
    have hdvd := gchain_diff_dvd ha2 hb2 hc2 hco Φ hwtpos hface hn48 hu hj
      t hne.choose hdefr hdefp
    obtain ⟨r, hr⟩ := hdvd
    have hs₀mem := hband _ (rowV_mem_Tri hn48 hu (by omega : 0 ≤ u))
    have hs₀x : x ≤ rwS a b c n Φ u 0 := ((mem_GBand hq).mp hs₀mem).2.1
    have hs₀0 : 0 < rwS a b c n Φ u 0 := by omega
    have hs₀R : (0 : ℝ) < (rwS a b c n Φ u 0 : ℝ) := by exact_mod_cast hs₀0
    have hbound : ∀ v : ℝ, 0 ≤ v → v < 1 →
        0 ≤ rdv a b c n Φ u v 0 ∧ rdv a b c n Φ u v 0 ≤ (rwS a b c n Φ u 0 : ℤ) := by
      intro v hv0 hv1
      constructor
      · apply round_nonneg_of_nonneg
        positivity
      · apply round_le_nat (by positivity)
        calc (rwS a b c n Φ u 0 : ℝ) * v < (rwS a b c n Φ u 0 : ℝ) * 1 :=
              mul_lt_mul_of_pos_left hv1 hs₀R
          _ = (rwS a b c n Φ u 0 : ℝ) := mul_one _
    obtain ⟨hbd1, hbd2⟩ := hbound t ht0 ht1
    obtain ⟨hbd1', hbd2'⟩ := hbound hne.choose ht'0 ht'1
    have hs₀Z : (0 : ℤ) < (rwS a b c n Φ u 0 : ℤ) := by exact_mod_cast hs₀0
    have hprodlo : -((rwS a b c n Φ u 0 : ℕ) : ℤ) ≤ ((rwS a b c n Φ u 0 : ℕ) : ℤ) * r := by
      rw [← hr]
      omega
    have hprodhi : ((rwS a b c n Φ u 0 : ℕ) : ℤ) * r ≤ ((rwS a b c n Φ u 0 : ℕ) : ℤ) := by
      rw [← hr]
      omega
    have hrlo : -1 ≤ r := by nlinarith [hprodlo, hs₀Z]
    have hrhi : r ≤ 1 := by nlinarith [hprodhi, hs₀Z]
    have hcong : rdv a b c n Φ u t 0 = rdv a b c n Φ u hne.choose 0 - rwS a b c n Φ u 0
        ∨ rdv a b c n Φ u t 0 = rdv a b c n Φ u hne.choose 0
        ∨ rdv a b c n Φ u t 0 = rdv a b c n Φ u hne.choose 0 + rwS a b c n Φ u 0 := by
      interval_cases r
      · left; omega
      · right; left; omega
      · right; right; omega
    have hnear : |(rwS a b c n Φ u 0 : ℝ) * t - (rdv a b c n Φ u t 0 : ℝ)| ≤ 1 / 2 :=
      abs_sub_round _
    exact mem_arc3 hs₀x hx1 hnear hcong
  -- FROM COVERING TO MEASURE
  have hsubset : E ⊆ ⋃ cd ∈ Codes n K B, Amap cd := by
    intro t ht
    obtain ⟨cd, hcd, hmem⟩ := hcover t ht
    exact Set.mem_biUnion hcd hmem
  have hvol_arc : ∀ cd ∈ Codes n K B,
      MeasureTheory.volume (Amap cd) ≤ ENNReal.ofReal (3 / (x : ℝ)) := by
    intro cd _
    by_cases h : (E ∩ SCode a b c n Φ cd).Nonempty
    · have hAeq : Amap cd
          = arc3 (rwS a b c n Φ cd.1 0) (rdv a b c n Φ cd.1 h.choose 0) x := by
        rw [hAmapdef]
        exact dif_pos h
      rw [hAeq]
      exact arc3_volume _ _ _
    · have hAeq : Amap cd = ∅ := by
        rw [hAmapdef]
        exact dif_neg h
      rw [hAeq]
      simp
  calc MeasureTheory.volume E
      ≤ MeasureTheory.volume (⋃ cd ∈ Codes n K B, Amap cd) :=
        MeasureTheory.measure_mono hsubset
    _ ≤ ∑ cd ∈ Codes n K B, MeasureTheory.volume (Amap cd) :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ Codes n K B, ENNReal.ofReal (3 / (x : ℝ)) :=
        Finset.sum_le_sum hvol_arc
    _ = ((Codes n K B).card : ℝ≥0∞) * ENNReal.ofReal (3 / (x : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end GCover

section GLowEnergyGeneral

/-- **Low-energy measure bound, general level `z`** (paper §3, eq. low-energy).

For every admissible level `0 ≤ z ≤ z₀·(log x)²`,

  `vol {t ∈ [0,1) : GQ_x(t) ≤ z} ≤ (1/x)·exp(C₄·(1 + z/log x)·log(log x + 2))`.

At `z = log x` the exponent is `2C₄·log(log x + 2)`, i.e. the bound is
`(log x + 2)^{2C₄}/x`, recovering `Erdos123Band.glow_energy_measure` up to constants. -/
theorem glow_energy_measure_general (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ z₀ C₄ : ℝ, ∃ X₂ : ℕ, 0 < z₀ ∧ 1 ≤ C₄ ∧ ∀ x : ℕ, X₂ ≤ x → ∀ z : ℝ,
      0 ≤ z → z ≤ z₀ * Real.log x ^ 2 →
        MeasureTheory.volume
            {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ z}
          ≤ ENNReal.ofReal ((1 / (x : ℝ)) *
              Real.exp (C₄ * (1 + z / Real.log x) * Real.log (Real.log x + 2))) := by
  classical
  have ha2 : 2 ≤ a := ha
  have hb2 : 2 ≤ b := hb
  have hc2 : 2 ≤ c := hc
  obtain ⟨c₀, C₀, D, hc₀, hC₀, hD1, X₀g, hX₀g2, hgrid⟩ :=
    ggrid_embedding (a := a) (b := b) (c := c) (p := p) (q := q) ha2 hb2 hc2 hco hq hqp hpd
  set K : ℕ := (a * b * c) ^ D with hKdef
  have habc8 : 8 ≤ a * b * c := by
    calc 8 = 2 * 2 * 2 := by norm_num
      _ ≤ a * b * c := Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  have hK8 : 8 ≤ K := by
    rw [hKdef]
    calc 8 ≤ a * b * c := habc8
      _ = (a * b * c) ^ 1 := (pow_one _).symm
      _ ≤ (a * b * c) ^ D := Nat.pow_le_pow_right (le_trans (by norm_num) habc8) hD1
  have hKR : (8 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK8
  have hK0R : (0 : ℝ) < (K : ℝ) := by linarith
  set δ : ℝ := 1 / (4 * (K : ℝ)) with hδdef
  have h4K : (4 * (K : ℝ)) ≠ 0 := ne_of_gt (by linarith)
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact div_pos one_pos (by linarith)
  have hprodδ : (4 * (K : ℝ)) * δ = 1 := by
    rw [hδdef, mul_one_div, div_self h4K]
  have h2Kδ : 2 * (K : ℝ) * δ < 1 := by linarith
  have hδsq0 : (0 : ℝ) < c₀ * δ ^ 2 := mul_pos hc₀ (pow_pos hδ0 2)
  -- the constants
  set A : ℝ := 22 / (c₀ * δ ^ 2) + 8 with hAdef
  have hA22 : (0 : ℝ) < 22 / (c₀ * δ ^ 2) := div_pos (by norm_num) hδsq0
  have hA0 : 0 < A := by rw [hAdef]; linarith
  set C₁ : ℝ := |Real.log (2 * C₀)| + 1 with hC₁def
  have hC₁1 : (1 : ℝ) ≤ C₁ := by
    rw [hC₁def]
    have := abs_nonneg (Real.log (2 * C₀))
    linarith
  have hlogP2 : (0 : ℝ) ≤ Real.log (2 * (K : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  set C₄ : ℝ := 2 + 2 * A + 2 * A * Real.log (2 * (K : ℝ) + 2) + (2 * A + 2) * C₁
    with hC₄def
  have hC₄1 : (1 : ℝ) ≤ C₄ := by
    rw [hC₄def]
    have e1 : (0 : ℝ) ≤ 2 * A * Real.log (2 * (K : ℝ) + 2) :=
      mul_nonneg (by linarith) hlogP2
    have e2 : (0 : ℝ) ≤ (2 * A + 2) * C₁ := mul_nonneg (by linarith) (by linarith)
    linarith
  set X₂ : ℕ := max X₀g (max 3 (max ⌈Real.exp (96 / c₀)⌉₊
    (max ⌈Real.exp (1 / C₀)⌉₊ ⌈Real.exp 1⌉₊))) with hX₂def
  refine ⟨1, C₄, X₂, one_pos, hC₄1, ?_⟩
  intro x hx z hz0 _hz
  simp only [hX₂def, max_le_iff] at hx
  obtain ⟨hxX₀g, hx3, hxc₀, hxC₀, hx1e⟩ := hx
  have hx1 : 1 ≤ x := by omega
  have hx0R : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  obtain ⟨n, Φ, ⟨hnlow, hnhigh⟩, hband, hinj, hface, hjump⟩ := hgrid x hxX₀g
  set L : ℝ := Real.log x with hLdef
  have hthresh : ∀ T : ℝ, ⌈Real.exp T⌉₊ ≤ x → T ≤ L := by
    intro T hT
    have h1 : Real.exp T ≤ (x : ℝ) := by
      calc Real.exp T ≤ (⌈Real.exp T⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (x : ℝ) := by exact_mod_cast hT
    calc T = Real.log (Real.exp T) := (Real.log_exp T).symm
      _ ≤ L := Real.log_le_log (Real.exp_pos T) h1
  have hL96 : 96 / c₀ ≤ L := hthresh _ hxc₀
  have hLC₀ : 1 / C₀ ≤ L := hthresh _ hxC₀
  have hL1 : (1 : ℝ) ≤ L := hthresh _ hx1e
  have hL0 : 0 < L := by linarith
  have hc₀L96 : (96 : ℝ) ≤ c₀ * L := by
    have h1 : c₀ * (96 / c₀) ≤ c₀ * L := mul_le_mul_of_nonneg_left hL96 hc₀.le
    rw [mul_div_cancel₀ _ hc₀.ne'] at h1
    linarith
  have hn96 : 96 ≤ n := by
    have h1 : (96 : ℝ) ≤ (n : ℝ) := le_trans hc₀L96 hnlow
    exact_mod_cast h1
  have hn48 : 48 ≤ n := by omega
  -- the code budget for this level
  have hden0 : (0 : ℝ) < c₀ * L * δ ^ 2 := mul_pos (mul_pos hc₀ hL0) (pow_pos hδ0 2)
  set B1 : ℕ := ⌈4 * z / (c₀ * L * δ ^ 2)⌉₊ with hB1def
  set B2 : ℕ := ⌈7 * z / (c₀ * L * δ ^ 2)⌉₊ with hB2def
  set B : ℕ := 2 * (B1 + B2 + 2) with hBdef
  set M : ℝ := 1 + z / L with hMdef
  set Λ : ℝ := Real.log (L + 2) with hΛdef
  have hzL0 : (0 : ℝ) ≤ z / L := div_nonneg hz0 hL0.le
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith
  have hΛ1 : (1 : ℝ) ≤ Λ := by
    rw [hΛdef]
    have he : Real.exp 1 ≤ L + 2 := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (L + 2) := Real.log_le_log (Real.exp_pos 1) he
  have hMΛ1 : (1 : ℝ) ≤ M * Λ := by nlinarith
  -- the abstract sparsity hypothesis at level z
  have hBhyp : ∀ m₁ m₂ : ℕ, (n : ℝ) * m₁ * δ ^ 2 ≤ 4 * z →
      (n : ℝ) * m₂ * δ ^ 2 ≤ 7 * z → 2 * (m₁ + m₂ + 2) ≤ B := by
    intro m₁ m₂ h1 h2
    have key : ∀ (m : ℕ) (k : ℝ), (n : ℝ) * m * δ ^ 2 ≤ k * z →
        (m : ℝ) ≤ k * z / (c₀ * L * δ ^ 2) := by
      intro m k hm
      rw [le_div_iff₀ hden0]
      have hgap : (0 : ℝ) ≤ ((n : ℝ) - c₀ * L) * ((m : ℝ) * δ ^ 2) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith [hm, hgap]
    have hm1 : m₁ ≤ B1 := by
      have hk := key m₁ 4 h1
      calc m₁ = ⌈(m₁ : ℝ)⌉₊ := (Nat.ceil_natCast _).symm
        _ ≤ ⌈4 * z / (c₀ * L * δ ^ 2)⌉₊ := Nat.ceil_mono hk
        _ = B1 := by rw [hB1def]
    have hm2 : m₂ ≤ B2 := by
      have hk := key m₂ 7 h2
      calc m₂ = ⌈(m₂ : ℝ)⌉₊ := (Nat.ceil_natCast _).symm
        _ ≤ ⌈7 * z / (c₀ * L * δ ^ 2)⌉₊ := Nat.ceil_mono hk
        _ = B2 := by rw [hB2def]
    rw [hBdef]
    omega
  -- the covering estimate at level z
  have hcov := gcover_measure_le a b c p q ha2 hb2 hc2 hco hq x n K B D Φ δ z
    hx1 hn48 hδ0 h2Kδ (le_of_eq hKdef.symm) hband hinj hface hjump hBhyp
  -- the budget is `≤ A·M`, expressed in the three atoms `Q`, `R`, `W`
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = z / (c₀ * L * δ ^ 2) := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 22 / (c₀ * δ ^ 2) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = z / L := ⟨_, rfl⟩
  have hQ0 : (0 : ℝ) ≤ Q := by rw [hQdef]; exact div_nonneg hz0 hden0.le
  have hR0 : (0 : ℝ) < R := by rw [hRdef]; exact hA22
  have hW0 : (0 : ℝ) ≤ W := by rw [hWdef]; exact hzL0
  have h4Q : 4 * z / (c₀ * L * δ ^ 2) = 4 * Q := by rw [hQdef]; ring
  have h7Q : 7 * z / (c₀ * L * δ ^ 2) = 7 * Q := by rw [hQdef]; ring
  have hRW : R * W = 22 * Q := by rw [hRdef, hWdef, hQdef]; ring
  have hAR : A = R + 8 := by rw [hAdef, hRdef]
  have hMW : M = 1 + W := by rw [hMdef, hWdef]
  have hB1R : (B1 : ℝ) ≤ 4 * Q + 1 := by
    rw [hB1def, h4Q]
    exact le_of_lt (Nat.ceil_lt_add_one (by linarith))
  have hB2R : (B2 : ℝ) ≤ 7 * Q + 1 := by
    rw [hB2def, h7Q]
    exact le_of_lt (Nat.ceil_lt_add_one (by linarith))
  have hBcast : (B : ℝ) = 2 * ((B1 : ℝ) + (B2 : ℝ) + 2) := by
    rw [hBdef]; push_cast; ring
  have hAMeq : A * M = R + 8 + 22 * Q + 8 * W := by
    rw [hAR, hMW, ← hRW]; ring
  have hBA : (B : ℝ) ≤ A * M := by linarith
  have hAM0 : (0 : ℝ) ≤ A * M := le_of_lt (mul_pos hA0 (by linarith))
  have hBAΛ : (B : ℝ) ≤ A * (M * Λ) := by
    nlinarith [mul_nonneg hAM0 (by linarith : (0:ℝ) ≤ Λ - 1), hBA]
  -- the counting estimate
  set N : ℝ := ((B : ℝ) + 1) ^ 2 * (2 * (K : ℝ) + 2) ^ (2 * B) * ((n : ℝ) + 1) ^ (2 * B + 2)
    with hNdef
  have hN0 : (0 : ℝ) < 3 * N := by rw [hNdef]; positivity
  have hcard : ((Codes n K B).card : ℝ) ≤ N := by
    have h1 := Codes_card_le n K B
    have h2 : ((Codes n K B).card : ℝ)
        ≤ (((B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) * (n + 1) ^ (2 * B + 2) : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [hNdef]
    push_cast at h2
    linarith
  have hlogN : Real.log (3 * N) = Real.log 3 + 2 * Real.log ((B : ℝ) + 1)
      + (2 * (B : ℝ)) * Real.log (2 * (K : ℝ) + 2)
      + (2 * (B : ℝ) + 2) * Real.log ((n : ℝ) + 1) := by
    rw [hNdef, Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  -- the three logarithmic ingredients
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    linarith
  have hlogB : Real.log ((B : ℝ) + 1) ≤ (B : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (B : ℝ) + 1 by positivity)
    linarith
  have hncast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlogn0 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hn1R : ((n : ℝ) + 1) ≤ 2 * C₀ * (L + 2) := by
    have h2 : (1 : ℝ) ≤ C₀ * L := by
      have h3 : C₀ * (1 / C₀) ≤ C₀ * L := mul_le_mul_of_nonneg_left hLC₀ hC₀.le
      rw [mul_div_cancel₀ _ hC₀.ne'] at h3
      linarith
    nlinarith [hnhigh, hC₀]
  have hlogn : Real.log ((n : ℝ) + 1) ≤ C₁ * Λ := by
    have hstep : Real.log ((n : ℝ) + 1) ≤ Real.log (2 * C₀ * (L + 2)) :=
      Real.log_le_log (by positivity) hn1R
    rw [Real.log_mul (ne_of_gt (show (0:ℝ) < 2 * C₀ by linarith))
      (ne_of_gt (show (0:ℝ) < L + 2 by linarith))] at hstep
    rw [← hΛdef] at hstep
    have habs : Real.log (2 * C₀) ≤ |Real.log (2 * C₀)| := le_abs_self _
    have hmul : |Real.log (2 * C₀)| ≤ |Real.log (2 * C₀)| * Λ := by
      nlinarith [abs_nonneg (Real.log (2 * C₀))]
    have hC₁Λ : C₁ * Λ = |Real.log (2 * C₀)| * Λ + Λ := by rw [hC₁def]; ring
    linarith
  -- assemble the logarithm bound
  have hlogbound : Real.log (3 * N) ≤ C₄ * M * Λ := by
    have e1 : Real.log 3 ≤ 2 * (M * Λ) := by linarith
    have e2 : 2 * Real.log ((B : ℝ) + 1) ≤ 2 * A * (M * Λ) := by linarith
    have e3 : (2 * (B : ℝ)) * Real.log (2 * (K : ℝ) + 2)
        ≤ 2 * A * Real.log (2 * (K : ℝ) + 2) * (M * Λ) := by
      nlinarith [mul_le_mul_of_nonneg_right hBAΛ hlogP2]
    have hcoefM : (2 * (B : ℝ) + 2) ≤ (2 * A + 2) * M := by nlinarith
    have hC₁Λ0 : (0 : ℝ) ≤ C₁ * Λ :=
      le_of_lt (mul_pos (by linarith) (by linarith))
    have e4 : (2 * (B : ℝ) + 2) * Real.log ((n : ℝ) + 1) ≤ (2 * A + 2) * C₁ * (M * Λ) := by
      calc (2 * (B : ℝ) + 2) * Real.log ((n : ℝ) + 1)
          ≤ (2 * (B : ℝ) + 2) * (C₁ * Λ) := by
            apply mul_le_mul_of_nonneg_left hlogn (by positivity)
        _ ≤ ((2 * A + 2) * M) * (C₁ * Λ) := mul_le_mul_of_nonneg_right hcoefM hC₁Λ0
        _ = (2 * A + 2) * C₁ * (M * Λ) := by ring
    have hexpand : C₄ * M * Λ = 2 * (M * Λ) + 2 * A * (M * Λ)
        + 2 * A * Real.log (2 * (K : ℝ) + 2) * (M * Λ) + (2 * A + 2) * C₁ * (M * Λ) := by
      rw [hC₄def]; ring
    rw [hlogN, hexpand]
    linarith
  have hexp : 3 * N ≤ Real.exp (C₄ * M * Λ) := by
    calc 3 * N = Real.exp (Real.log (3 * N)) := (Real.exp_log hN0).symm
      _ ≤ Real.exp (C₄ * M * Λ) := Real.exp_le_exp.mpr hlogbound
  have h3c : 3 * ((Codes n K B).card : ℝ) ≤ Real.exp (C₄ * M * Λ) := by linarith
  -- conclude
  refine le_trans hcov ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc ((Codes n K B).card : ℝ) * (3 / (x : ℝ))
      = (3 * ((Codes n K B).card : ℝ)) * (1 / (x : ℝ)) := by ring
    _ ≤ Real.exp (C₄ * M * Λ) * (1 / (x : ℝ)) :=
        mul_le_mul_of_nonneg_right h3c (by positivity)
    _ = 1 / (x : ℝ) * Real.exp (C₄ * M * Λ) := by ring

end GLowEnergyGeneral

end Erdos123Band

/-- Adversarial signature check: the frozen statement, restated verbatim. -/
example : ∀ (a b c p q : ℕ), 1 < a → 1 < b → 1 < c →
    Erdos123Band.PairwiseCoprime3 a b c → 0 < q → q < p →
    p < q * min a (min b c) →
    ∃ z₀ C₄ : ℝ, ∃ X₂ : ℕ, 0 < z₀ ∧ 1 ≤ C₄ ∧ ∀ x : ℕ, X₂ ≤ x → ∀ z : ℝ,
      0 ≤ z → z ≤ z₀ * Real.log x ^ 2 →
        MeasureTheory.volume
            {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ Erdos123Band.GQenergy a b c p q x t ≤ z}
          ≤ ENNReal.ofReal ((1 / (x : ℝ)) *
              Real.exp (C₄ * (1 + z / Real.log x) * Real.log (Real.log x + 2))) :=
  @Erdos123Band.glow_energy_measure_general

#print axioms Erdos123Band.glow_energy_measure_general
