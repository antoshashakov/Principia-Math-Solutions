/-
M3 — Minor-arc energy floor (paper Lemma 5.2), the gcd-rigidity argument.

`lemma_5_2'` : on the minor arc the band energy satisfies `Q_x(t) ≥ κ₀ log x`.

Proof by contradiction: if `Q < κ₀ log x` then (via `badF_card_le`) fewer than `n/8`
grid vertices are "bad" (phase further than `δ` from an integer), so the pigeonhole
of `Routing.lean` produces a completely clean row + path T-shape.  Along a clean
edge the integer relation `B·d' = A·d` holds EXACTLY (`edge_defect_zero`: the defect
is an integer of absolute value `≤ 2Kδ ≤ 1/2 < 1`).  Chaining (`chain_dvd`) with the
face-anchored corners (gcd `1` by `corner_gcd_eq_one`) forces `s₀ ∣ round (s₀ t)`,
i.e. `t` within `δ/x` of a rational integer — but `t` is on the minor arc, at
distance `> 1/(8x)` from `ℤ`.  Contradiction.
-/
import Erdos123.Routing

set_option maxHeartbeats 1000000

namespace Erdos123Band

/-! ## The grid as a finset -/

/-- Finset carrier of the corner-less triangular grid. -/
noncomputable def TriF (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  letI := Classical.decPred (fun v : ℕ × ℕ × ℕ => v ∈ Tri n)
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun v => v ∈ Tri n)

/-- `TriF` is the finset version of `Tri` (coordinates of a member are `≤ n`
automatically, since they sum to `n`). -/
lemma mem_TriF {n : ℕ} {v : ℕ × ℕ × ℕ} : v ∈ TriF n ↔ v ∈ Tri n := by
  unfold TriF
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    have hs := Tri_sum h
    exact ⟨⟨by omega, by omega, by omega⟩, h⟩

/-! ## Bad-vertex count vs. energy -/

/-- **Bad-vertex count is controlled by the energy.**  The vertices whose image phase
is further than `δ` from the nearest integer number at most `Q/δ²`: their weights are
distinct band elements each contributing `> δ²` to `Q`. -/
lemma badF_card_le (a b c x n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (t δ : ℝ) (hδ : 0 < δ)
    (hband : ∀ v ∈ Tri n, wt a b c (Φ v) ∈ Band a b c x)
    (hinj : ∀ v ∈ Tri n, ∀ w ∈ Tri n, wt a b c (Φ v) = wt a b c (Φ w) → v = w) :
    (((TriF n).filter (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|)).card : ℝ) * δ ^ 2 ≤ Qenergy a b c x t := by
  classical
  set F : Finset (ℕ × ℕ × ℕ) := (TriF n).filter (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
      - round ((wt a b c (Φ v) : ℝ) * t)|) with hFdef
  have hFT : ∀ v ∈ F, v ∈ Tri n := fun v hv => mem_TriF.mp (Finset.mem_filter.mp hv).1
  have hFbad : ∀ v ∈ F, δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| :=
    fun v hv => (Finset.mem_filter.mp hv).2
  set G : Finset ℕ := F.image (fun v => wt a b c (Φ v)) with hGdef
  have hGcard : G.card = F.card := by
    rw [hGdef]
    apply Finset.card_image_of_injOn
    intro v hv w hw hvw
    exact hinj v (hFT v hv) w (hFT w hw) hvw
  have hGsub : G ⊆ Band a b c x := by
    intro s hs
    rw [hGdef] at hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
    exact hband v (hFT v hv)
  have hGterm : ∀ s ∈ G, δ ^ 2 ≤ ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 := by
    intro s hs
    rw [hGdef] at hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
    have h1 := hFbad v hv
    calc δ ^ 2
        ≤ |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| ^ 2 :=
          pow_le_pow_left₀ hδ.le h1.le 2
      _ = ((wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)) ^ 2 := sq_abs _
  have h1 : (G.card : ℝ) * δ ^ 2 ≤ ∑ s ∈ G, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 := by
    have h := Finset.card_nsmul_le_sum G
      (fun s => ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2) (δ ^ 2) hGterm
    rwa [nsmul_eq_mul] at h
  have h2 : ∑ s ∈ G, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 ≤ Qenergy a b c x t := by
    unfold Qenergy
    exact Finset.sum_le_sum_of_subset_of_nonneg hGsub (fun s _ _ => sq_nonneg _)
  calc (F.card : ℝ) * δ ^ 2
      = (G.card : ℝ) * δ ^ 2 := by rw [hGcard]
    _ ≤ ∑ s ∈ G, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 := h1
    _ ≤ Qenergy a b c x t := h2

/-! ## Zero defect across a good edge -/

/-- **Zero defect across a good edge.**  If both endpoint phases are within `δ` of
integers, the edge coefficients are `≤ K` with `K·δ ≤ 1/4`, and the weights satisfy
the edge relation, then the integer cross-relation holds exactly: the defect
`B·d' − A·d` is an integer of absolute value `≤ 2Kδ ≤ 1/2 < 1`, hence zero. -/
lemma edge_defect_zero {K : ℕ} {t δ : ℝ} (hδ : 0 < δ) (hKδ : (K : ℝ) * δ ≤ 1 / 4)
    {A B S S' : ℕ} (hrel : A * S = B * S') (hAK : A ≤ K) (hBK : B ≤ K)
    (hS : |(S : ℝ) * t - round ((S : ℝ) * t)| ≤ δ)
    (hS' : |(S' : ℝ) * t - round ((S' : ℝ) * t)| ≤ δ) :
    (B : ℤ) * round ((S' : ℝ) * t) = (A : ℤ) * round ((S : ℝ) * t) := by
  set d : ℤ := round ((S : ℝ) * t) with hd
  set d' : ℤ := round ((S' : ℝ) * t) with hd'
  have hAR : (A : ℝ) ≤ (K : ℝ) := by exact_mod_cast hAK
  have hBR : (B : ℝ) ≤ (K : ℝ) := by exact_mod_cast hBK
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hrelR : (A : ℝ) * (S : ℝ) = (B : ℝ) * (S' : ℝ) := by exact_mod_cast hrel
  set E : ℤ := B * d' - A * d with hE
  have hid : (E : ℝ)
      = (B : ℝ) * ((d' : ℝ) - (S' : ℝ) * t) - (A : ℝ) * ((d : ℝ) - (S : ℝ) * t) := by
    have hexp : (E : ℝ) = (B : ℝ) * (d' : ℝ) - (A : ℝ) * (d : ℝ) := by
      rw [hE]; push_cast; ring
    have h2 : (B : ℝ) * ((S' : ℝ) * t) = (A : ℝ) * ((S : ℝ) * t) := by
      rw [← mul_assoc, ← mul_assoc, ← hrelR]
    rw [hexp]; linarith [h2]
  have hSd : |(d : ℝ) - (S : ℝ) * t| ≤ δ := by rw [abs_sub_comm]; exact hS
  have hSd' : |(d' : ℝ) - (S' : ℝ) * t| ≤ δ := by rw [abs_sub_comm]; exact hS'
  have hu := abs_le.mp hSd
  have hu' := abs_le.mp hSd'
  have hB1 : (B : ℝ) * ((d' : ℝ) - (S' : ℝ) * t) ≤ (B : ℝ) * δ :=
    mul_le_mul_of_nonneg_left hu'.2 hB0
  have hB2 : (B : ℝ) * (-δ) ≤ (B : ℝ) * ((d' : ℝ) - (S' : ℝ) * t) :=
    mul_le_mul_of_nonneg_left hu'.1 hB0
  have hA1 : (A : ℝ) * ((d : ℝ) - (S : ℝ) * t) ≤ (A : ℝ) * δ :=
    mul_le_mul_of_nonneg_left hu.2 hA0
  have hA2 : (A : ℝ) * (-δ) ≤ (A : ℝ) * ((d : ℝ) - (S : ℝ) * t) :=
    mul_le_mul_of_nonneg_left hu.1 hA0
  have hBδ : (B : ℝ) * δ ≤ (K : ℝ) * δ := mul_le_mul_of_nonneg_right hBR hδ.le
  have hAδ : (A : ℝ) * δ ≤ (K : ℝ) * δ := mul_le_mul_of_nonneg_right hAR hδ.le
  have hEbound : |(E : ℝ)| ≤ 1 / 2 := by
    rw [hid, abs_le]
    constructor
    · linarith [hB2, hA1, hBδ, hAδ, hKδ]
    · linarith [hB1, hA2, hBδ, hAδ, hKδ]
  have hE1 : |(E : ℝ)| < 1 := lt_of_le_of_lt hEbound (by norm_num)
  have hE1' : ((|E| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact hE1
  have hE1'' : |E| < 1 := by exact_mod_cast hE1'
  have hE0 : E = 0 := by
    have h := abs_lt.mp hE1''
    omega
  have hfin : (B : ℤ) * d' - (A : ℤ) * d = 0 := by rw [← hE]; exact hE0
  linarith [hfin]

/-! ## The minor-arc energy floor -/

/-- **Anton Lemma 5.2 (minor-arc energy floor), PROVED.**  On the minor arc the band
energy is at least `κ₀ · log x`.  This is the axiom-free replacement of `lemma_5_2`. -/
theorem lemma_5_2' (a b c : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) :
    ∃ κ₀ : ℝ, ∃ X₅ : ℕ, 0 < κ₀ ∧ ∀ x : ℕ, X₅ ≤ x → ∀ t : ℝ,
      t ∈ MinorArc x → κ₀ * Real.log x ≤ Qenergy a b c x t := by
  classical
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hc1 : 1 ≤ c := by omega
  obtain ⟨c₀, C₀, D, hc₀, -, hD1, X₀g, -, hgrid⟩ :=
    grid_embedding (a := a) (b := b) (c := c) (by omega) (by omega) (by omega) hco
  -- the jump-coefficient bound K and the phase tolerance δ
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
  have h4K0 : (0 : ℝ) < 4 * (K : ℝ) := by linarith
  set δ : ℝ := 1 / (4 * (K : ℝ)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos one_pos h4K0
  have hδ32 : δ ≤ 1 / 32 := by
    rw [hδdef, div_le_div_iff₀ h4K0 (by norm_num : (0 : ℝ) < 32)]
    linarith
  have hKδeq : (K : ℝ) * δ = 1 / 4 := by
    rw [hδdef, mul_one_div, div_eq_div_iff h4K0.ne' (by norm_num : (4 : ℝ) ≠ 0)]
    ring
  have hKδ : (K : ℝ) * δ ≤ 1 / 4 := le_of_eq hKδeq
  set κ₀ : ℝ := c₀ * δ ^ 2 / 9 with hκdef
  have hκpos : 0 < κ₀ := by
    rw [hκdef]
    exact div_pos (mul_pos hc₀ (pow_pos hδpos 2)) (by norm_num)
  refine ⟨κ₀, max X₀g (max 3 ⌈Real.exp (96 / c₀)⌉₊), hκpos, fun x hx t ht => ?_⟩
  -- basic consequences of the threshold
  have hxX₀g : X₀g ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_left 3 _) (le_max_right X₀g _)) hx
  have hx0 : 0 < x := by omega
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
  have hxceil : ⌈Real.exp (96 / c₀)⌉₊ ≤ x :=
    le_trans (le_trans (le_max_right 3 _) (le_max_right X₀g _)) hx
  have hxceilR : Real.exp (96 / c₀) ≤ (x : ℝ) := by
    calc Real.exp (96 / c₀) ≤ (⌈Real.exp (96 / c₀)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (x : ℝ) := by exact_mod_cast hxceil
  have hL96 : 96 / c₀ ≤ Real.log x := by
    calc 96 / c₀ = Real.log (Real.exp (96 / c₀)) := (Real.log_exp _).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hxceilR
  have h96 : (96 : ℝ) ≤ c₀ * Real.log x := by
    have h1 := (div_le_iff₀ hc₀).mp hL96
    linarith
  -- suppose the energy is small
  by_contra hcon
  push_neg at hcon
  -- the grid data for this x
  obtain ⟨n, Φ, ⟨hnlo, -⟩, hband, hinj, hface, hjump⟩ := hgrid x hxX₀g
  have hn96R : (96 : ℝ) ≤ (n : ℝ) := le_trans h96 hnlo
  have hn96 : 96 ≤ n := by exact_mod_cast hn96R
  have hn48 : 48 ≤ n := by omega
  -- the bad-vertex count H
  have hQb := badF_card_le a b c x n Φ t δ hδpos hband hinj
  set H : ℕ := ((TriF n).filter (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
      - round ((wt a b c (Φ v) : ℝ) * t)|)).card with hHdef
  rw [hκdef] at hcon
  have hδsq : (0 : ℝ) < δ ^ 2 := pow_pos hδpos 2
  have hH9R : (H : ℝ) * 9 < (n : ℝ) := by
    have h1 : (H : ℝ) * δ ^ 2 < c₀ * δ ^ 2 / 9 * Real.log x := lt_of_le_of_lt hQb hcon
    have h2 : ((H : ℝ) * 9) * δ ^ 2 < (c₀ * Real.log x) * δ ^ 2 := by nlinarith [h1]
    have h3 : (H : ℝ) * 9 < c₀ * Real.log x := lt_of_mul_lt_mul_right h2 hδsq.le
    linarith [hnlo]
  have hH9 : 9 * H < n := by
    have h3 : ((9 * H : ℕ) : ℝ) < (n : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  have hH8 : 8 * H < n := by omega
  -- pigeonhole: a completely clean row and path
  have hHbound : ∀ F : Finset (ℕ × ℕ × ℕ),
      (∀ v ∈ F, v ∈ Tri n ∧ δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) → F.card ≤ H := by
    intro F hF
    rw [hHdef]
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hvT, hvB⟩ := hF v hv
    exact Finset.mem_filter.mpr ⟨mem_TriF.mpr hvT, hvB⟩
  obtain ⟨q, hq, j, hj, hrow4, hpath7⟩ :=
    exists_sparse_row_and_path hn48
      (fun v => δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)|)
      H hHbound
  have hjq : j ≤ q := by
    have h := (midJ_bounds hj).2
    omega
  -- both marked sets are empty
  have hrow0 : (rowBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
      - round ((wt a b c (Φ v) : ℝ) * t)|) n q).card = 0 := by
    by_contra hne
    have h1 : 1 ≤ (rowBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) n q).card := Nat.pos_of_ne_zero hne
    have h2 : n ≤ 4 * H := by
      calc n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * (rowBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
            - round ((wt a b c (Φ v) : ℝ) * t)|) n q).card := Nat.mul_le_mul_left n h1
        _ ≤ 4 * H := hrow4
    omega
  have hpath0 : (pathBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
      - round ((wt a b c (Φ v) : ℝ) * t)|) n q j).card = 0 := by
    by_contra hne
    have h1 : 1 ≤ (pathBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) n q j).card := Nat.pos_of_ne_zero hne
    have h2 : n ≤ 7 * H := by
      calc n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * (pathBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
            - round ((wt a b c (Φ v) : ℝ) * t)|) n q j).card := Nat.mul_le_mul_left n h1
        _ ≤ 7 * H := hpath7
    omega
  -- goodness along the row and the path
  have hrowGood : ∀ i, i ≤ q →
      |(wt a b c (Φ (rowV n q i)) : ℝ) * t
        - round ((wt a b c (Φ (rowV n q i)) : ℝ) * t)| ≤ δ := by
    intro i hi
    by_contra hbad
    push_neg at hbad
    have hmem : i ∈ rowBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) n q := by
      simp only [rowBad, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hbad⟩
    have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  have hpathGood : ∀ s, s ≤ n - q →
      |(wt a b c (Φ (pathV n q j s)) : ℝ) * t
        - round ((wt a b c (Φ (pathV n q j s)) : ℝ) * t)| ≤ δ := by
    intro s hs
    by_contra hbad
    push_neg at hbad
    have hmem : s ∈ pathBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) n q j := by
      simp only [pathBad, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hbad⟩
    have hpos := Finset.card_pos.mpr ⟨s, hmem⟩
    omega
  -- chain data: positivity of the weights
  have hrS_ge : ∀ i, i ≤ q → x ≤ wt a b c (Φ (rowV n q i)) := fun i hi =>
    (mem_Band.mp (hband _ (rowV_mem_Tri hn48 hq hi))).2.1
  have hrs : ∀ i, i ≤ q → 0 < wt a b c (Φ (rowV n q i)) := fun i hi =>
    lt_of_lt_of_le hx0 (hrS_ge i hi)
  have hpS_ge : ∀ s, s ≤ n - q → x ≤ wt a b c (Φ (pathV n q j s)) := fun s hs =>
    (mem_Band.mp (hband _ (pathV_mem_Tri hn48 hq hj hs))).2.1
  have hps : ∀ s, s ≤ n - q → 0 < wt a b c (Φ (pathV n q j s)) := fun s hs =>
    lt_of_lt_of_le hx0 (hpS_ge s hs)
  -- chain data: edge coefficients
  have hrB : ∀ i, i < q → 0 < edgeA a b c (Φ (rowV n q (i + 1))) (Φ (rowV n q i)) :=
    fun i _ => edgeA_pos (by omega) (by omega) (by omega) _ _
  have hpB : ∀ s, s < n - q → 0 < edgeA a b c (Φ (pathV n q j (s + 1))) (Φ (pathV n q j s)) :=
    fun s _ => edgeA_pos (by omega) (by omega) (by omega) _ _
  have hrrel : ∀ i, i < q →
      edgeA a b c (Φ (rowV n q i)) (Φ (rowV n q (i + 1))) * wt a b c (Φ (rowV n q i))
        = edgeA a b c (Φ (rowV n q (i + 1))) (Φ (rowV n q i))
          * wt a b c (Φ (rowV n q (i + 1))) :=
    fun i _ => edgeA_mul_wt a b c (Φ (rowV n q i)) (Φ (rowV n q (i + 1)))
  have hprel : ∀ s, s < n - q →
      edgeA a b c (Φ (pathV n q j s)) (Φ (pathV n q j (s + 1))) * wt a b c (Φ (pathV n q j s))
        = edgeA a b c (Φ (pathV n q j (s + 1))) (Φ (pathV n q j s))
          * wt a b c (Φ (pathV n q j (s + 1))) :=
    fun s _ => edgeA_mul_wt a b c (Φ (pathV n q j s)) (Φ (pathV n q j (s + 1)))
  -- chain data: exact integer relations across good edges
  have hrd : ∀ i, i < q →
      (edgeA a b c (Φ (rowV n q (i + 1))) (Φ (rowV n q i)) : ℤ)
          * round ((wt a b c (Φ (rowV n q (i + 1))) : ℝ) * t)
        = (edgeA a b c (Φ (rowV n q i)) (Φ (rowV n q (i + 1))) : ℤ)
          * round ((wt a b c (Φ (rowV n q i)) : ℝ) * t) := by
    intro i hi
    have hm1 : rowV n q i ∈ Tri n := rowV_mem_Tri hn48 hq (by omega)
    have hm2 : rowV n q (i + 1) ∈ Tri n := rowV_mem_Tri hn48 hq (by omega)
    obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hjump _ hm1 _ hm2 (rowV_adjacent (by omega))
    exact edge_defect_zero hδpos hKδ
      (edgeA_mul_wt a b c (Φ (rowV n q i)) (Φ (rowV n q (i + 1))))
      (by rw [hKdef]; exact edgeA_le ha1 hb1 hc1 j2 j4 j6)
      (by rw [hKdef]; exact edgeA_le ha1 hb1 hc1 j1 j3 j5)
      (hrowGood i (by omega)) (hrowGood (i + 1) (by omega))
  have hpd : ∀ s, s < n - q →
      (edgeA a b c (Φ (pathV n q j (s + 1))) (Φ (pathV n q j s)) : ℤ)
          * round ((wt a b c (Φ (pathV n q j (s + 1))) : ℝ) * t)
        = (edgeA a b c (Φ (pathV n q j s)) (Φ (pathV n q j (s + 1))) : ℤ)
          * round ((wt a b c (Φ (pathV n q j s)) : ℝ) * t) := by
    intro s hs
    have hm1 : pathV n q j s ∈ Tri n := pathV_mem_Tri hn48 hq hj (by omega)
    have hm2 : pathV n q j (s + 1) ∈ Tri n := pathV_mem_Tri hn48 hq hj (by omega)
    obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hjump _ hm1 _ hm2 (pathV_adjacent hjq (by omega))
    exact edge_defect_zero hδpos hKδ
      (edgeA_mul_wt a b c (Φ (pathV n q j s)) (Φ (pathV n q j (s + 1))))
      (by rw [hKdef]; exact edgeA_le ha1 hb1 hc1 j2 j4 j6)
      (by rw [hKdef]; exact edgeA_le ha1 hb1 hc1 j1 j3 j5)
      (hpathGood s (by omega)) (hpathGood (s + 1) (by omega))
  -- junction
  have hjunc_s : wt a b c (Φ (pathV n q j 0)) = wt a b c (Φ (rowV n q (q - j))) := by
    rw [pathV_zero hjq]
  have hjunc_d : round ((wt a b c (Φ (pathV n q j 0)) : ℝ) * t)
      = round ((wt a b c (Φ (rowV n q (q - j))) : ℝ) * t) := by
    rw [hjunc_s]
  -- the three face-anchored corners have coprime weights
  have hmem0 : rowV n q 0 ∈ Tri n := rowV_mem_Tri hn48 hq (Nat.zero_le q)
  have hmemq : rowV n q q ∈ Tri n := rowV_mem_Tri hn48 hq (le_refl q)
  have hmemP : pathV n q j (n - q) ∈ Tri n := pathV_mem_Tri hn48 hq hj (le_refl (n - q))
  have hk0 : (Φ (rowV n q 0)).1 = 0 := (hface _ hmem0).1 (by simp [rowV])
  have hl0 : (Φ (rowV n q q)).2.1 = 0 := (hface _ hmemq).2.1 (by simp [rowV])
  have hm0 : (Φ (pathV n q j (n - q))).2.2 = 0 := (hface _ hmemP).2.2 (by simp [pathV])
  have hw0 : wt a b c (Φ (rowV n q 0))
      = b ^ (Φ (rowV n q 0)).2.1 * c ^ (Φ (rowV n q 0)).2.2 := by
    rw [wt, hk0, pow_zero, one_mul]
  have hwq : wt a b c (Φ (rowV n q q))
      = a ^ (Φ (rowV n q q)).1 * c ^ (Φ (rowV n q q)).2.2 := by
    rw [wt, hl0, pow_zero, mul_one]
  have hwP : wt a b c (Φ (pathV n q j (n - q)))
      = a ^ (Φ (pathV n q j (n - q))).1 * b ^ (Φ (pathV n q j (n - q))).2.1 := by
    rw [wt, hm0, pow_zero, mul_one]
  have hgcd : Nat.gcd (Nat.gcd (wt a b c (Φ (rowV n q 0))) (wt a b c (Φ (rowV n q q))))
      (wt a b c (Φ (pathV n q j (n - q)))) = 1 := by
    rw [hw0, hwq, hwP]
    exact corner_gcd_eq_one hco _ _ _ _ _ _
  -- the chain divisibility
  have hdvd : (wt a b c (Φ (rowV n q 0)) : ℤ)
      ∣ round ((wt a b c (Φ (rowV n q 0)) : ℝ) * t) :=
    chain_dvd (q := q) (P := n - q)
      (fun i => wt a b c (Φ (rowV n q i)))
      (fun s => wt a b c (Φ (pathV n q j s)))
      (fun i => round ((wt a b c (Φ (rowV n q i)) : ℝ) * t))
      (fun s => round ((wt a b c (Φ (pathV n q j s)) : ℝ) * t))
      (fun i => edgeA a b c (Φ (rowV n q i)) (Φ (rowV n q (i + 1))))
      (fun i => edgeA a b c (Φ (rowV n q (i + 1))) (Φ (rowV n q i)))
      (fun s => edgeA a b c (Φ (pathV n q j s)) (Φ (pathV n q j (s + 1))))
      (fun s => edgeA a b c (Φ (pathV n q j (s + 1))) (Φ (pathV n q j s)))
      hrs hps hrB hpB hrrel hprel hrd hpd
      (q - j) (Nat.sub_le q j) hjunc_s hjunc_d hgcd
  obtain ⟨r, hr⟩ := hdvd
  -- t is within δ/x of the integer r
  have hgood0 : |(wt a b c (Φ (rowV n q 0)) : ℝ) * t
      - round ((wt a b c (Φ (rowV n q 0)) : ℝ) * t)| ≤ δ := hrowGood 0 (Nat.zero_le q)
  have hSxN : x ≤ wt a b c (Φ (rowV n q 0)) := hrS_ge 0 (Nat.zero_le q)
  have hSx : (x : ℝ) ≤ (wt a b c (Φ (rowV n q 0)) : ℝ) := by exact_mod_cast hSxN
  have hS₀pos : (0 : ℝ) < (wt a b c (Φ (rowV n q 0)) : ℝ) := lt_of_lt_of_le hxR hSx
  have hkey : |t - (r : ℝ)| ≤ δ / (x : ℝ) := by
    have hfac : (wt a b c (Φ (rowV n q 0)) : ℝ) * t
        - ((round ((wt a b c (Φ (rowV n q 0)) : ℝ) * t) : ℤ) : ℝ)
        = (wt a b c (Φ (rowV n q 0)) : ℝ) * (t - (r : ℝ)) := by
      rw [hr]; push_cast; ring
    have h1 : (wt a b c (Φ (rowV n q 0)) : ℝ) * |t - (r : ℝ)| ≤ δ := by
      calc (wt a b c (Φ (rowV n q 0)) : ℝ) * |t - (r : ℝ)|
          = |(wt a b c (Φ (rowV n q 0)) : ℝ) * (t - (r : ℝ))| := by
            rw [abs_mul, abs_of_pos hS₀pos]
        _ = |(wt a b c (Φ (rowV n q 0)) : ℝ) * t
              - ((round ((wt a b c (Φ (rowV n q 0)) : ℝ) * t) : ℤ) : ℝ)| := by rw [hfac]
        _ ≤ δ := hgood0
    rw [le_div_iff₀ hxR]
    calc |t - (r : ℝ)| * (x : ℝ)
        ≤ |t - (r : ℝ)| * (wt a b c (Φ (rowV n q 0)) : ℝ) :=
          mul_le_mul_of_nonneg_left hSx (abs_nonneg _)
      _ = (wt a b c (Φ (rowV n q 0)) : ℝ) * |t - (r : ℝ)| := mul_comm _ _
      _ ≤ δ := h1
  -- but t is on the minor arc: farther than 1/(8x) from both 0 and 1
  simp only [MinorArc, Set.mem_diff] at ht
  obtain ⟨htIoc, htmaj⟩ := ht
  simp only [MajorArc, Set.mem_setOf_eq, not_and, not_or, not_le] at htmaj
  obtain ⟨h1t, h2t⟩ := htmaj htIoc
  have hδx : δ / (x : ℝ) < 1 / (8 * (x : ℝ)) := by
    have h8x : (0 : ℝ) < 8 * (x : ℝ) := by linarith
    rw [div_lt_div_iff₀ hxR h8x]
    have h1 : δ * (8 * (x : ℝ)) ≤ 1 / 32 * (8 * (x : ℝ)) :=
      mul_le_mul_of_nonneg_right hδ32 h8x.le
    linarith
  have habs := abs_le.mp hkey
  rcases le_or_gt r 0 with hr0 | hr1
  · have hrR : (r : ℝ) ≤ 0 := by exact_mod_cast hr0
    linarith [habs.2, h1t, hδx, hrR]
  · have h1r : (1 : ℤ) ≤ r := by omega
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h1r
    linarith [habs.1, h2t, hδx, hrR]

end Erdos123Band

#print axioms Erdos123Band.lemma_5_2'
