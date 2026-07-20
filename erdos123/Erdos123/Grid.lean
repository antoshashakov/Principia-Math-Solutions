/-
M1 — The triangular grid embedding (paper Proposition 3.1).

`grid_embedding` produces, for every large `x`, an integer `n ≍ log x` and a map `Φ`
from the corner-less triangular grid `Tri n = {(i,j,r) : i+j+r = n} ∖ corners` into
exponent triples, such that

  * every image weight `a^k b^ℓ c^m` lies in the band `B_x = S ∩ [x, 3x/2)`;
  * distinct grid points have distinct image weights;
  * zero coordinates are preserved (`i = 0 → k = 0`, etc.);
  * grid points within `1` in every coordinate have images within `D` in every coordinate.

The corner-less condition guarantees at most one barycentric coordinate vanishes,
which is exactly what `three_rounding` requires.
-/
import Erdos123.Slab

set_option maxHeartbeats 1000000

namespace Erdos123Band

/-- Weight of an exponent triple. -/
def wt (a b c : ℕ) (v : ℕ × ℕ × ℕ) : ℕ := a ^ v.1 * b ^ v.2.1 * c ^ v.2.2

/-- The corner-less triangular grid `Δ_n°`. -/
def Tri (n : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {v | v.1 + v.2.1 + v.2.2 = n ∧ v ≠ (n, 0, 0) ∧ v ≠ (0, n, 0) ∧ v ≠ (0, 0, n)}

lemma Tri_sum {n : ℕ} {v : ℕ × ℕ × ℕ} (hv : v ∈ Tri n) : v.1 + v.2.1 + v.2.2 = n := hv.1

/-- In `Tri n` at most one coordinate vanishes. -/
lemma Tri_at_most_one_zero {n : ℕ} {v : ℕ × ℕ × ℕ} (hv : v ∈ Tri n) :
    ¬(v.1 = 0 ∧ v.2.1 = 0) ∧ ¬(v.1 = 0 ∧ v.2.2 = 0) ∧ ¬(v.2.1 = 0 ∧ v.2.2 = 0) := by
  obtain ⟨hsum, hc1, hc2, hc3⟩ := hv
  obtain ⟨i, j, r⟩ := v
  have hsum' : i + j + r = n := hsum
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    have h1' : i = 0 := h1
    have h2' : j = 0 := h2
    exact hc3 (by simp only [Prod.mk.injEq]; omega)
  · rintro ⟨h1, h2⟩
    have h1' : i = 0 := h1
    have h2' : r = 0 := h2
    exact hc2 (by simp only [Prod.mk.injEq]; omega)
  · rintro ⟨h1, h2⟩
    have h1' : j = 0 := h1
    have h2' : r = 0 := h2
    exact hc1 (by simp only [Prod.mk.injEq]; omega)

section GridEmbedding

variable {a b c : ℕ}

/-- **The grid embedding** (paper Prop 3.1, existential form).  The constants
`c₀, C₀, D` are uniform in `x`; only `n` and `Φ` depend on `x`. -/
theorem grid_embedding (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) :
    ∃ c₀ C₀ : ℝ, ∃ D : ℕ, 0 < c₀ ∧ 0 < C₀ ∧ 1 ≤ D ∧ ∃ X₀ : ℕ, 2 ≤ X₀ ∧
      ∀ x : ℕ, X₀ ≤ x →
      ∃ n : ℕ, ∃ Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ,
        (c₀ * Real.log x ≤ (n : ℝ) ∧ (n : ℝ) ≤ C₀ * Real.log x) ∧
        (∀ v ∈ Tri n, wt a b c (Φ v) ∈ Band a b c x) ∧
        (∀ v ∈ Tri n, ∀ w ∈ Tri n, wt a b c (Φ v) = wt a b c (Φ w) → v = w) ∧
        (∀ v ∈ Tri n,
          (v.1 = 0 → (Φ v).1 = 0) ∧ (v.2.1 = 0 → (Φ v).2.1 = 0) ∧
          (v.2.2 = 0 → (Φ v).2.2 = 0)) ∧
        (∀ v ∈ Tri n, ∀ w ∈ Tri n,
          (v.1 ≤ w.1 + 1 ∧ w.1 ≤ v.1 + 1 ∧ v.2.1 ≤ w.2.1 + 1 ∧ w.2.1 ≤ v.2.1 + 1 ∧
            v.2.2 ≤ w.2.2 + 1 ∧ w.2.2 ≤ v.2.2 + 1) →
          ((Φ v).1 ≤ (Φ w).1 + D ∧ (Φ w).1 ≤ (Φ v).1 + D ∧
            (Φ v).2.1 ≤ (Φ w).2.1 + D ∧ (Φ w).2.1 ≤ (Φ v).2.1 + D ∧
            (Φ v).2.2 ≤ (Φ w).2.2 + D ∧ (Φ w).2.2 ≤ (Φ v).2.2 + D)) := by
  classical
  obtain ⟨R₀, hR₀1, hround⟩ := three_rounding ha hb hc hco
  set α : ℝ := Real.log a with hαdef
  set β : ℝ := Real.log b with hβdef
  set γ : ℝ := Real.log c with hγdef
  set η : ℝ := Real.log (3 / 2) with hηdef
  have hα : 0 < α := log_base_pos ha
  have hβ : 0 < β := log_base_pos hb
  have hγ : 0 < γ := log_base_pos hc
  have hη : 0 < η := eta_pos
  have hη1 : η ≤ 1 := by
    have h1 : Real.log (3 / 2) < Real.log 2 := by
      apply Real.log_lt_log (by norm_num) (by norm_num)
    have h2 := Real.log_two_lt_d9
    simp only [hηdef]
    linarith
  set M₀ : ℝ := max α (max β γ) with hM₀def
  set m₀ : ℝ := min α (min β γ) with hm₀def
  have hM₀ : 0 < M₀ := lt_of_lt_of_le hα (le_max_left _ _)
  have hm₀ : 0 < m₀ := by
    simp only [hm₀def, lt_min_iff]
    exact ⟨hα, hβ, hγ⟩
  have hαM : α ≤ M₀ := le_max_left _ _
  have hβM : β ≤ M₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hγM : γ ≤ M₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hmα : m₀ ≤ α := min_le_left _ _
  have hmβ : m₀ ≤ β := le_trans (min_le_right _ _) (min_le_left _ _)
  have hmγ : m₀ ≤ γ := le_trans (min_le_right _ _) (min_le_right _ _)
  set τ₀ : ℝ := (4 * R₀ + 1) * M₀ with hτ₀def
  have hτ₀ : 0 < τ₀ := by
    apply mul_pos ?_ hM₀
    linarith
  have hτ₀M : τ₀ / M₀ = 4 * R₀ + 1 := by
    rw [hτ₀def, mul_div_assoc, div_self hM₀.ne', mul_one]
  -- the jump constant
  set Dr : ℝ := 2 * R₀ + 2 * τ₀ / m₀ with hDrdef
  have hDrpos : 0 < Dr := by positivity
  set D : ℕ := ⌈Dr⌉₊ with hDdef
  have hDrD : Dr ≤ (D : ℝ) := Nat.le_ceil Dr
  have hD1 : 1 ≤ D := by
    rw [hDdef]
    apply Nat.one_le_ceil_iff.mpr hDrpos
  -- the threshold: log x ≥ T := 4·τ₀ + 2
  set T : ℝ := 4 * τ₀ + 2 with hTdef
  set X₀ : ℕ := max 2 ⌈Real.exp T⌉₊ with hX₀def
  refine ⟨1 / (2 * τ₀), 2 / τ₀, D, by positivity, by positivity, hD1, X₀,
    le_max_left _ _, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := by omega
  set L : ℝ := Real.log x with hLdef
  have hLT : T ≤ L := by
    have hxT : Real.exp T ≤ (x : ℝ) := by
      calc Real.exp T ≤ (⌈Real.exp T⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (x : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hx
    calc T = Real.log (Real.exp T) := (Real.log_exp T).symm
      _ ≤ L := Real.log_le_log (Real.exp_pos T) hxT
  have hL0 : 0 < L := by
    have hT0 : (0 : ℝ) < T := by simp only [hTdef]; positivity
    linarith
  set Λ : ℝ := L + η / 2 with hΛdef
  have hΛ0 : 0 < Λ := by positivity
  have hLΛ : L ≤ Λ := by simp only [hΛdef]; linarith
  have hΛ2L : Λ ≤ 2 * L := by
    simp only [hΛdef]
    have : η / 2 ≤ L := by nlinarith [hLT, hη1]
    linarith
  set n : ℕ := ⌊Λ / τ₀⌋₊ with hndef
  have hn1 : 1 ≤ n := by
    rw [hndef]
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hτ₀, one_mul]
    simp only [hΛdef, hTdef] at hLT ⊢
    nlinarith [hη]
  have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  set τ : ℝ := Λ / n with hτdef
  have hτpos : 0 < τ := div_pos hΛ0 hn0R
  have hτlow : τ₀ ≤ τ := by
    rw [hτdef, le_div_iff₀ hn0R]
    have h1 : (n : ℝ) ≤ Λ / τ₀ := Nat.floor_le (by positivity)
    calc τ₀ * (n : ℝ) = (n : ℝ) * τ₀ := by ring
      _ ≤ (Λ / τ₀) * τ₀ := mul_le_mul_of_nonneg_right h1 hτ₀.le
      _ = Λ := div_mul_cancel₀ _ hτ₀.ne'
  have hτhigh : τ ≤ 2 * τ₀ := by
    rw [hτdef, div_le_iff₀ hn0R]
    have h1 : Λ / τ₀ < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : Λ < ((n : ℝ) + 1) * τ₀ := by
      calc Λ = (Λ / τ₀) * τ₀ := (div_mul_cancel₀ _ hτ₀.ne').symm
        _ < ((n : ℝ) + 1) * τ₀ := mul_lt_mul_of_pos_right h1 hτ₀
    nlinarith [hτ₀, hn1R]
  have hτn : τ * (n : ℝ) = Λ := by
    rw [hτdef]
    field_simp
  -- n ≍ L
  have hnlow : 1 / (2 * τ₀) * L ≤ (n : ℝ) := by
    have h1 : Λ / τ₀ < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : Λ < ((n : ℝ) + 1) * τ₀ := by
      calc Λ = (Λ / τ₀) * τ₀ := (div_mul_cancel₀ _ hτ₀.ne').symm
        _ < ((n : ℝ) + 1) * τ₀ := mul_lt_mul_of_pos_right h1 hτ₀
    have h3 : L < ((n : ℝ) + 1) * τ₀ := lt_of_le_of_lt hLΛ h2
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : (0:ℝ) < 2 * τ₀)]
    nlinarith [hn1R, hτ₀]
  have hnhigh : (n : ℝ) ≤ 2 / τ₀ * L := by
    have h1 : (n : ℝ) ≤ Λ / τ₀ := Nat.floor_le (by positivity)
    have h2 : Λ / τ₀ ≤ (2 * L) / τ₀ := by gcongr
    calc (n : ℝ) ≤ Λ / τ₀ := h1
      _ ≤ (2 * L) / τ₀ := h2
      _ = 2 / τ₀ * L := by ring
  -- targets
  set Xc : ℕ → ℝ := fun i => τ * i / α with hXcdef
  set Yc : ℕ → ℝ := fun j => τ * j / β with hYcdef
  set Zc : ℕ → ℝ := fun r => τ * r / γ with hZcdef
  -- generic coordinate helpers
  have coord_pos : ∀ (p : ℕ) (u : ℝ), 0 < u → u ≤ M₀ → 1 ≤ p →
      4 * R₀ + 1 ≤ τ * p / u := by
    intro p u hu huM hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    rw [le_div_iff₀ hu]
    have h1 : τ₀ ≤ τ * p := by
      calc τ₀ = τ₀ * 1 := (mul_one _).symm
        _ ≤ τ * (p : ℝ) := by
            apply mul_le_mul hτlow hp1 (by norm_num) hτpos.le
    calc (4 * R₀ + 1) * u ≤ (4 * R₀ + 1) * M₀ := by
          apply mul_le_mul_of_nonneg_left huM (by linarith)
      _ = τ₀ := hτ₀def.symm
      _ ≤ τ * p := h1
  have coord_sep : ∀ (p q : ℕ) (u : ℝ), 0 < u → u ≤ M₀ → p ≠ q →
      4 * R₀ + 1 ≤ |τ * p / u - τ * q / u| := by
    intro p q u hu huM hpq
    have h1 : |τ * p / u - τ * q / u| = (τ / u) * |(p : ℝ) - (q : ℝ)| := by
      rw [show τ * p / u - τ * q / u = (τ / u) * ((p : ℝ) - (q : ℝ)) by ring, abs_mul,
        abs_of_pos (div_pos hτpos hu)]
    have h2 : (1 : ℝ) ≤ |(p : ℝ) - (q : ℝ)| := by
      have h3 : ((p : ℤ) : ℝ) - ((q : ℤ) : ℝ) = (((p : ℤ) - (q : ℤ) : ℤ) : ℝ) := by push_cast; ring
      have h4 : (p : ℤ) ≠ (q : ℤ) := by exact_mod_cast hpq
      have h5 : 1 ≤ |(p : ℤ) - (q : ℤ)| := Int.one_le_abs (sub_ne_zero.mpr h4)
      have h6 : (1 : ℝ) ≤ |(((p : ℤ) - (q : ℤ) : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast h5
      calc (1 : ℝ) ≤ |(((p : ℤ) - (q : ℤ) : ℤ) : ℝ)| := h6
        _ = |(p : ℝ) - (q : ℝ)| := by rw [← h3]; push_cast; ring_nf
    have h7 : τ₀ / M₀ ≤ τ / u := by
      rw [div_le_div_iff₀ hM₀ hu]
      nlinarith [hτlow, huM, hτ₀, hu]
    rw [h1]
    calc 4 * R₀ + 1 = τ₀ / M₀ := hτ₀M.symm
      _ = (τ₀ / M₀) * 1 := (mul_one _).symm
      _ ≤ (τ / u) * |(p : ℝ) - (q : ℝ)| := by
          apply mul_le_mul h7 h2 (by norm_num) (div_pos hτpos hu).le
  have coord_close : ∀ (p q : ℕ) (u : ℝ), 0 < u → m₀ ≤ u → p ≤ q + 1 → q ≤ p + 1 →
      |τ * p / u - τ * q / u| ≤ 2 * τ₀ / m₀ := by
    intro p q u hu hum hpq hqp
    have h1 : |τ * p / u - τ * q / u| = (τ / u) * |(p : ℝ) - (q : ℝ)| := by
      rw [show τ * p / u - τ * q / u = (τ / u) * ((p : ℝ) - (q : ℝ)) by ring, abs_mul,
        abs_of_pos (div_pos hτpos hu)]
    have h2 : |(p : ℝ) - (q : ℝ)| ≤ 1 := by
      rw [abs_le]
      constructor
      · have : (q : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast hqp
        linarith
      · have : (p : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hpq
        linarith
    have h3 : τ / u ≤ 2 * τ₀ / m₀ := by
      rw [div_le_div_iff₀ hu hm₀]
      nlinarith [hτhigh, hum, hm₀, hτpos]
    rw [h1]
    calc (τ / u) * |(p : ℝ) - (q : ℝ)| ≤ (τ / u) * 1 := by
          apply mul_le_mul_of_nonneg_left h2 (div_pos hτpos hu).le
      _ = τ / u := mul_one _
      _ ≤ 2 * τ₀ / m₀ := h3
  -- the rounding, vertex by vertex
  have hex : ∀ v : ℕ × ℕ × ℕ, v ∈ Tri n →
      ∃ klm : ℕ × ℕ × ℕ,
        (L ≤ klm.1 * α + klm.2.1 * β + klm.2.2 * γ ∧
          klm.1 * α + klm.2.1 * β + klm.2.2 * γ < L + η) ∧
        |(klm.1 : ℝ) - Xc v.1| ≤ R₀ ∧ |(klm.2.1 : ℝ) - Yc v.2.1| ≤ R₀ ∧
        |(klm.2.2 : ℝ) - Zc v.2.2| ≤ R₀ ∧
        (v.1 = 0 → klm.1 = 0) ∧ (v.2.1 = 0 → klm.2.1 = 0) ∧
        (v.2.2 = 0 → klm.2.2 = 0) := by
    intro v hv
    obtain ⟨i, j, r⟩ := v
    obtain ⟨hz1, hz2, hz3⟩ := Tri_at_most_one_zero hv
    simp only at hz1 hz2 hz3
    have hsum : i + j + r = n := Tri_sum hv
    have hX0 : (0 : ℝ) ≤ Xc i := by
      simp only [hXcdef]; positivity
    have hY0 : (0 : ℝ) ≤ Yc j := by
      simp only [hYcdef]; positivity
    have hZ0 : (0 : ℝ) ≤ Zc r := by
      simp only [hZcdef]; positivity
    have hXzero : Xc i = 0 ↔ i = 0 := by
      simp only [hXcdef]
      constructor
      · intro h
        by_contra hi
        have hi1 : 1 ≤ i := by omega
        have := coord_pos i α hα hαM hi1
        rw [h] at this
        linarith [hR₀1]
      · intro h
        rw [h]
        simp
    have hYzero : Yc j = 0 ↔ j = 0 := by
      simp only [hYcdef]
      constructor
      · intro h
        by_contra hj
        have hj1 : 1 ≤ j := by omega
        have := coord_pos j β hβ hβM hj1
        rw [h] at this
        linarith [hR₀1]
      · intro h
        rw [h]
        simp
    have hZzero : Zc r = 0 ↔ r = 0 := by
      simp only [hZcdef]
      constructor
      · intro h
        by_contra hr
        have hr1 : 1 ≤ r := by omega
        have := coord_pos r γ hγ hγM hr1
        rw [h] at this
        linarith [hR₀1]
      · intro h
        rw [h]
        simp
    have hXalt : Xc i = 0 ∨ 2 * R₀ ≤ Xc i := by
      by_cases hi : i = 0
      · left; exact hXzero.mpr hi
      · right
        have := coord_pos i α hα hαM (by omega)
        linarith [hR₀1]
    have hYalt : Yc j = 0 ∨ 2 * R₀ ≤ Yc j := by
      by_cases hj : j = 0
      · left; exact hYzero.mpr hj
      · right
        have := coord_pos j β hβ hβM (by omega)
        linarith [hR₀1]
    have hZalt : Zc r = 0 ∨ 2 * R₀ ≤ Zc r := by
      by_cases hr : r = 0
      · left; exact hZzero.mpr hr
      · right
        have := coord_pos r γ hγ hγM (by omega)
        linarith [hR₀1]
    have hplane : Xc i * α + Yc j * β + Zc r * γ = L + η / 2 := by
      simp only [hXcdef, hYcdef, hZcdef]
      have h1 : τ * i / α * α + τ * j / β * β + τ * r / γ * γ
          = τ * ((i : ℝ) + (j : ℝ) + (r : ℝ)) := by
        field_simp
      rw [h1]
      have h2 : (i : ℝ) + (j : ℝ) + (r : ℝ) = (n : ℝ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hsum
      rw [h2, hτn]
    have hXYz : ¬(Xc i = 0 ∧ Yc j = 0) := by
      rintro ⟨h1, h2⟩
      exact hz1 ⟨hXzero.mp h1, hYzero.mp h2⟩
    have hXZz : ¬(Xc i = 0 ∧ Zc r = 0) := by
      rintro ⟨h1, h2⟩
      exact hz2 ⟨hXzero.mp h1, hZzero.mp h2⟩
    have hYZz : ¬(Yc j = 0 ∧ Zc r = 0) := by
      rintro ⟨h1, h2⟩
      exact hz3 ⟨hYzero.mp h1, hZzero.mp h2⟩
    obtain ⟨k, l, m, hslab, hk, hl, hm, hkz, hlz, hmz⟩ :=
      hround L (Xc i) (Yc j) (Zc r) hX0 hY0 hZ0 hXYz hXZz hYZz hXalt hYalt hZalt hplane
    exact ⟨(k, l, m), hslab, hk, hl, hm,
      fun h => hkz (hXzero.mpr h), fun h => hlz (hYzero.mpr h), fun h => hmz (hZzero.mpr h)⟩
  -- the map
  set Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ :=
    fun v => if h : v ∈ Tri n then (hex v h).choose else (0, 0, 0) with hΦdef
  have hΦspec : ∀ v (hv : v ∈ Tri n),
      (L ≤ (Φ v).1 * α + (Φ v).2.1 * β + (Φ v).2.2 * γ ∧
        (Φ v).1 * α + (Φ v).2.1 * β + (Φ v).2.2 * γ < L + η) ∧
      |((Φ v).1 : ℝ) - Xc v.1| ≤ R₀ ∧ |((Φ v).2.1 : ℝ) - Yc v.2.1| ≤ R₀ ∧
      |((Φ v).2.2 : ℝ) - Zc v.2.2| ≤ R₀ ∧
      (v.1 = 0 → (Φ v).1 = 0) ∧ (v.2.1 = 0 → (Φ v).2.1 = 0) ∧
      (v.2.2 = 0 → (Φ v).2.2 = 0) := by
    intro v hv
    simp only [hΦdef, dif_pos hv]
    exact (hex v hv).choose_spec
  refine ⟨n, Φ, ⟨hnlow, hnhigh⟩, ?_, ?_, ?_, ?_⟩
  · -- Band membership
    intro v hv
    obtain ⟨⟨hlo, hhi⟩, -⟩ := hΦspec v hv
    have := (mem_Band_iff_slab ha hb hc hx1 (Φ v).1 (Φ v).2.1 (Φ v).2.2).mpr
      ⟨by rw [← hLdef, ← hαdef, ← hβdef, ← hγdef]; linarith,
        by rw [← hLdef, ← hαdef, ← hβdef, ← hγdef, ← hηdef]; linarith⟩
    exact this
  · -- injectivity
    intro v hv w hw hwt
    obtain ⟨-, hkv, hlv, hmv, -⟩ := hΦspec v hv
    obtain ⟨-, hkw, hlw, hmw, -⟩ := hΦspec w hw
    obtain ⟨hkk, hll, hmm⟩ := coprime3_pow_inj ha hb hc hco hwt
    by_contra hvw
    -- some coordinate differs
    obtain ⟨i, j, r⟩ := v
    obtain ⟨i', j', r'⟩ := w
    simp only [Prod.mk.injEq, not_and] at hvw
    have hdiff : i ≠ i' ∨ j ≠ j' ∨ r ≠ r' := by
      by_contra hcon
      push_neg at hcon
      exact absurd (hcon.2.2) (hvw hcon.1 hcon.2.1)
    simp only at hkv hlv hmv hkw hlw hmw hkk hll hmm
    rcases hdiff with h | h | h
    · have hsep := coord_sep i i' α hα hαM h
      have h2 : ((Φ (i, j, r)).1 : ℝ) = ((Φ (i', j', r')).1 : ℝ) := by
        exact_mod_cast hkk
      have e1 : |Xc i - ((Φ (i, j, r)).1 : ℝ)| ≤ R₀ := by
        rw [abs_sub_comm]
        exact hkv
      have e2 : |((Φ (i, j, r)).1 : ℝ) - Xc i'| ≤ R₀ := by
        rw [h2]
        exact hkw
      have h1 : |Xc i - Xc i'| ≤ 2 * R₀ := by
        calc |Xc i - Xc i'|
            ≤ |Xc i - ((Φ (i, j, r)).1 : ℝ)| + |((Φ (i, j, r)).1 : ℝ) - Xc i'| :=
              abs_sub_le _ _ _
          _ ≤ R₀ + R₀ := add_le_add e1 e2
          _ = 2 * R₀ := by ring
      simp only [hXcdef] at h1 hsep
      linarith [hsep, h1, hR₀1]
    · have hsep := coord_sep j j' β hβ hβM h
      have h2 : ((Φ (i, j, r)).2.1 : ℝ) = ((Φ (i', j', r')).2.1 : ℝ) := by
        exact_mod_cast hll
      have e1 : |Yc j - ((Φ (i, j, r)).2.1 : ℝ)| ≤ R₀ := by
        rw [abs_sub_comm]
        exact hlv
      have e2 : |((Φ (i, j, r)).2.1 : ℝ) - Yc j'| ≤ R₀ := by
        rw [h2]
        exact hlw
      have h1 : |Yc j - Yc j'| ≤ 2 * R₀ := by
        calc |Yc j - Yc j'|
            ≤ |Yc j - ((Φ (i, j, r)).2.1 : ℝ)| + |((Φ (i, j, r)).2.1 : ℝ) - Yc j'| :=
              abs_sub_le _ _ _
          _ ≤ R₀ + R₀ := add_le_add e1 e2
          _ = 2 * R₀ := by ring
      simp only [hYcdef] at h1 hsep
      linarith [hsep, h1, hR₀1]
    · have hsep := coord_sep r r' γ hγ hγM h
      have h2 : ((Φ (i, j, r)).2.2 : ℝ) = ((Φ (i', j', r')).2.2 : ℝ) := by
        exact_mod_cast hmm
      have e1 : |Zc r - ((Φ (i, j, r)).2.2 : ℝ)| ≤ R₀ := by
        rw [abs_sub_comm]
        exact hmv
      have e2 : |((Φ (i, j, r)).2.2 : ℝ) - Zc r'| ≤ R₀ := by
        rw [h2]
        exact hmw
      have h1 : |Zc r - Zc r'| ≤ 2 * R₀ := by
        calc |Zc r - Zc r'|
            ≤ |Zc r - ((Φ (i, j, r)).2.2 : ℝ)| + |((Φ (i, j, r)).2.2 : ℝ) - Zc r'| :=
              abs_sub_le _ _ _
          _ ≤ R₀ + R₀ := add_le_add e1 e2
          _ = 2 * R₀ := by ring
      simp only [hZcdef] at h1 hsep
      linarith [hsep, h1, hR₀1]
  · -- face preservation
    intro v hv
    obtain ⟨-, -, -, -, h1, h2, h3⟩ := hΦspec v hv
    exact ⟨h1, h2, h3⟩
  · -- bounded jumps
    intro v hv w hw hclose
    obtain ⟨-, hkv, hlv, hmv, -⟩ := hΦspec v hv
    obtain ⟨-, hkw, hlw, hmw, -⟩ := hΦspec w hw
    obtain ⟨h11, h12, h21, h22, h31, h32⟩ := hclose
    have hboundk : |((Φ v).1 : ℝ) - ((Φ w).1 : ℝ)| ≤ Dr := by
      have hc := coord_close v.1 w.1 α hα hmα h11 h12
      calc |((Φ v).1 : ℝ) - ((Φ w).1 : ℝ)|
          ≤ |((Φ v).1 : ℝ) - Xc v.1| + |Xc v.1 - ((Φ w).1 : ℝ)| := abs_sub_le _ _ _
        _ ≤ R₀ + (|Xc v.1 - Xc w.1| + |Xc w.1 - ((Φ w).1 : ℝ)|) := by
            apply add_le_add hkv (abs_sub_le _ _ _)
        _ ≤ R₀ + (2 * τ₀ / m₀ + R₀) := by
            apply add_le_add le_rfl
            apply add_le_add
            · simpa [hXcdef] using hc
            · rwa [abs_sub_comm]
        _ = Dr := by rw [hDrdef]; ring
    have hboundl : |((Φ v).2.1 : ℝ) - ((Φ w).2.1 : ℝ)| ≤ Dr := by
      have hc := coord_close v.2.1 w.2.1 β hβ hmβ h21 h22
      calc |((Φ v).2.1 : ℝ) - ((Φ w).2.1 : ℝ)|
          ≤ |((Φ v).2.1 : ℝ) - Yc v.2.1| + |Yc v.2.1 - ((Φ w).2.1 : ℝ)| := abs_sub_le _ _ _
        _ ≤ R₀ + (|Yc v.2.1 - Yc w.2.1| + |Yc w.2.1 - ((Φ w).2.1 : ℝ)|) := by
            apply add_le_add hlv (abs_sub_le _ _ _)
        _ ≤ R₀ + (2 * τ₀ / m₀ + R₀) := by
            apply add_le_add le_rfl
            apply add_le_add
            · simpa [hYcdef] using hc
            · rwa [abs_sub_comm]
        _ = Dr := by rw [hDrdef]; ring
    have hboundm : |((Φ v).2.2 : ℝ) - ((Φ w).2.2 : ℝ)| ≤ Dr := by
      have hc := coord_close v.2.2 w.2.2 γ hγ hmγ h31 h32
      calc |((Φ v).2.2 : ℝ) - ((Φ w).2.2 : ℝ)|
          ≤ |((Φ v).2.2 : ℝ) - Zc v.2.2| + |Zc v.2.2 - ((Φ w).2.2 : ℝ)| := abs_sub_le _ _ _
        _ ≤ R₀ + (|Zc v.2.2 - Zc w.2.2| + |Zc w.2.2 - ((Φ w).2.2 : ℝ)|) := by
            apply add_le_add hmv (abs_sub_le _ _ _)
        _ ≤ R₀ + (2 * τ₀ / m₀ + R₀) := by
            apply add_le_add le_rfl
            apply add_le_add
            · simpa [hZcdef] using hc
            · rwa [abs_sub_comm]
        _ = Dr := by rw [hDrdef]; ring
    have conv : ∀ p q : ℕ, |(p : ℝ) - (q : ℝ)| ≤ Dr → p ≤ q + D ∧ q ≤ p + D := by
      intro p q hpq
      have h1 := abs_le.mp hpq
      constructor
      · have h2 : (p : ℝ) ≤ (q : ℝ) + (D : ℝ) := by linarith [h1.2, hDrD]
        exact_mod_cast h2
      · have h2 : (q : ℝ) ≤ (p : ℝ) + (D : ℝ) := by linarith [h1.1, hDrD]
        exact_mod_cast h2
    obtain ⟨e1, e2⟩ := conv _ _ hboundk
    obtain ⟨e3, e4⟩ := conv _ _ hboundl
    obtain ⟨e5, e6⟩ := conv _ _ hboundm
    exact ⟨e1, e2, e3, e4, e5, e6⟩

end GridEmbedding

end Erdos123Band
