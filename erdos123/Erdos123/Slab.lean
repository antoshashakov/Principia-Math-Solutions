/-
M0 — Slab rounding (paper §2) + sharp band-count upper bound (part of Prop 3.2).

Contents:
  * `exists_small_theta`   — a small positive element of ℤθ + ℤ (θ irrational)
  * `finite_net`           — paper Lemma 2.1, non-effective form: bounded-index δ-nets
  * `two_rounding`         — paper Lemma 2.2: rounding onto the strip A ≤ up+vq < A+η
  * `three_rounding`       — paper Lemma 2.4: rounding onto the exponent slab E_L,
                             preserving zero coordinates
  * `coprime3_pow_inj`     — three-base unique factorization
  * `band_card_le_sq`      — |B_x| ≤ (log₂(2x)+1)², the L² upper bound
  * `mem_Band_iff_slab`    — the Band ↔ exponent-slab dictionary

Everything is existential (no effective constants), matching the `IsDComplete` target.
-/
import Erdos123.Band

set_option maxHeartbeats 1000000

namespace Erdos123Band

open Real

/-! ## A small positive element of ℤθ + ℤ -/

/-- For irrational `θ`, the group `ℤθ + ℤ` contains a positive element below any `ε`. -/
theorem exists_small_theta {θ : ℝ} (hθ : Irrational θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m n : ℤ, 0 < (m : ℝ) * θ + (n : ℝ) ∧ (m : ℝ) * θ + (n : ℝ) < ε := by
  have hirr : Irrational (θ / 1) := by rwa [div_one]
  have hdense : Dense (AddSubgroup.closure {θ, (1 : ℝ)} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  obtain ⟨z, hz1, hz2⟩ :=
    (dense_iff_inter_open.mp hdense) (Set.Ioo 0 ε) isOpen_Ioo (Set.nonempty_Ioo.mpr hε)
  obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hz2
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at hmn
  exact ⟨m, n, by rw [hmn]; exact hz1.1, by rw [hmn]; exact hz1.2⟩

/-! ## Finite nets from an irrational rotation (paper Lemma 2.1) -/

/-- **Finite nets.** For irrational `θ` and `δ > 0` there is a bound `R` such that every
real `y` is within `δ` of `r·θ` modulo `1` for some `|r| ≤ R`. -/
theorem finite_net {θ : ℝ} (hθ : Irrational θ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∀ y : ℝ, ∃ r N : ℤ, |(r : ℝ)| ≤ R ∧ |y - r * θ - N| < δ := by
  obtain ⟨m, n₀, hωpos, hωlt⟩ := exists_small_theta hθ hδ
  set ω : ℝ := (m : ℝ) * θ + (n₀ : ℝ) with hωdef
  refine ⟨(|(m : ℝ)| + 1) / ω, by positivity, fun y => ?_⟩
  -- fractional part of y, by hand
  set y' : ℝ := y - (⌊y⌋ : ℝ) with hy'def
  have hy'0 : 0 ≤ y' := by
    have := Int.floor_le y
    simp only [hy'def]; linarith
  have hy'1 : y' < 1 := by
    have := Int.lt_floor_add_one y
    simp only [hy'def]; linarith
  -- step index along the ω-ladder
  set j : ℤ := ⌊y' / ω⌋ with hjdef
  have hj0 : 0 ≤ j := Int.floor_nonneg.mpr (div_nonneg hy'0 hωpos.le)
  have hj0R : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj0
  have hjle : (j : ℝ) * ω ≤ y' := by
    have h1 : (j : ℝ) ≤ y' / ω := Int.floor_le _
    calc (j : ℝ) * ω ≤ (y' / ω) * ω := mul_le_mul_of_nonneg_right h1 hωpos.le
      _ = y' := div_mul_cancel₀ _ hωpos.ne'
  have hjlt : y' < ((j : ℝ) + 1) * ω := by
    have h1 : y' / ω < (j : ℝ) + 1 := Int.lt_floor_add_one _
    calc y' = (y' / ω) * ω := (div_mul_cancel₀ _ hωpos.ne').symm
      _ < ((j : ℝ) + 1) * ω := mul_lt_mul_of_pos_right h1 hωpos
  -- the index bound
  have hjbound : (j : ℝ) * ω < 1 := lt_of_le_of_lt hjle hy'1
  have hjltinv : (j : ℝ) < 1 / ω := (lt_div_iff₀ hωpos).mpr hjbound
  refine ⟨j * m, ⌊y⌋ + j * n₀, ?_, ?_⟩
  · -- |j·m| ≤ (|m|+1)/ω
    have h1 : |((j * m : ℤ) : ℝ)| = (j : ℝ) * |(m : ℝ)| := by
      push_cast
      rw [abs_mul, abs_of_nonneg hj0R]
    rw [h1]
    have h2 : (j : ℝ) * |(m : ℝ)| ≤ (1 / ω) * |(m : ℝ)| :=
      mul_le_mul_of_nonneg_right hjltinv.le (abs_nonneg _)
    have h3 : (1 / ω) * |(m : ℝ)| ≤ (|(m : ℝ)| + 1) / ω := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hωpos hωpos]
      nlinarith [abs_nonneg (m : ℝ), hωpos]
    linarith [h2, h3]
  · -- the distance: y − (jm)θ − (⌊y⌋ + jn₀) = y' − jω ∈ [0, ω) ⊂ [0, δ)
    have hkey : y - ((j * m : ℤ) : ℝ) * θ - ((⌊y⌋ + j * n₀ : ℤ) : ℝ) = y' - (j : ℝ) * ω := by
      simp only [hy'def, hωdef]
      push_cast
      ring
    rw [hkey, abs_of_nonneg (by linarith)]
    linarith

/-! ## Two-coordinate slab rounding (paper Lemma 2.2) -/

/-- **Two-coordinate rounding.** For positive `u, v` with `u/v` irrational and
`0 < η < v`, there is `R ≥ 1` such that: whenever `u·X + v·Y = A + η/2` with
`X, Y ≥ R`, there are integers `p, q ≥ 0` with `A ≤ u·p + v·q < A + η` and
`|p − X|, |q − Y| ≤ R`. -/
theorem two_rounding {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hirr : Irrational (u / v))
    {η : ℝ} (hη : 0 < η) (hηv : η < v) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ A X Y : ℝ, R ≤ X → R ≤ Y → u * X + v * Y = A + η / 2 →
      ∃ p q : ℤ, 0 ≤ p ∧ 0 ≤ q ∧ A ≤ u * p + v * q ∧ u * p + v * q < A + η ∧
        |(p : ℝ) - X| ≤ R ∧ |(q : ℝ) - Y| ≤ R := by
  set θ : ℝ := u / v with hθdef
  set lam : ℝ := η / v with hlamdef
  have hlam0 : 0 < lam := div_pos hη hv
  have hlam1 : lam < 1 := (div_lt_one hv).mpr hηv
  obtain ⟨R₁, hR₁0, hnet⟩ := finite_net hirr (show (0 : ℝ) < lam / 8 by positivity)
  -- the final constant
  set C₂ : ℝ := 1 + (u * (1 + R₁) + η / 2) / v with hC₂def
  set R : ℝ := max (R₁ + 2) (C₂ + 1) with hRdef
  have hR1 : 1 ≤ R := le_trans (by linarith) (le_max_left _ _)
  refine ⟨R, hR1, fun A X Y hX hY hplane => ?_⟩
  set p₀ : ℤ := ⌊X⌋ with hp₀def
  have hp₀le : (p₀ : ℝ) ≤ X := Int.floor_le X
  have hp₀gt : X - 1 < (p₀ : ℝ) := by
    have := Int.lt_floor_add_one X
    linarith
  set y₀ : ℝ := (A - u * p₀) / v with hy₀def
  obtain ⟨r, N, hrR, hdist⟩ := hnet (y₀ - (1 - lam / 2))
  set p : ℤ := p₀ + r with hpdef
  set q : ℤ := N + 1 with hqdef
  set w : ℝ := y₀ - (r : ℝ) * θ with hwdef
  have hvne : v ≠ 0 := hv.ne'
  -- v·w = A − u·p
  have hvw : v * w = A - u * p := by
    simp only [hwdef, hy₀def, hθdef, hpdef]
    push_cast
    field_simp
    ring
  -- the net window: q − w ∈ (3λ/8, 5λ/8)
  have hq_cast : (q : ℝ) = (N : ℝ) + 1 := by
    simp only [hqdef]; push_cast; ring
  have habs := abs_lt.mp hdist
  have hwin1 : 3 * lam / 8 < (q : ℝ) - w := by
    rw [hq_cast]
    simp only [hwdef]
    linarith [habs.2]
  have hwin2 : (q : ℝ) - w < 5 * lam / 8 := by
    rw [hq_cast]
    simp only [hwdef]
    linarith [habs.1]
  -- the strip: u·p + v·q − A = v·(q − w)
  have hstrip : u * p + v * q - A = v * ((q : ℝ) - w) := by
    have : v * ((q : ℝ) - w) = v * q - v * w := by ring
    rw [this, hvw]; ring
  have hvlam : v * lam = η := by
    simp only [hlamdef]; field_simp
  have hstrip1 : A < u * p + v * q := by
    have h1 : 0 < v * ((q : ℝ) - w) := by
      have : (0 : ℝ) < 3 * lam / 8 := by positivity
      exact mul_pos hv (by linarith)
    linarith [hstrip]
  have hstrip2 : u * p + v * q < A + η := by
    have h1 : v * ((q : ℝ) - w) < v * (5 * lam / 8) := mul_lt_mul_of_pos_left hwin2 hv
    have h2 : v * (5 * lam / 8) = 5 * η / 8 := by
      rw [show v * (5 * lam / 8) = (v * lam) * 5 / 8 by ring, hvlam]; ring
    have h3 : 5 * η / 8 < η := by linarith
    linarith [hstrip]
  -- distance bounds
  have hpX : |(p : ℝ) - X| ≤ 1 + R₁ := by
    simp only [hpdef]
    push_cast
    have h1 : |(p₀ : ℝ) + (r : ℝ) - X| ≤ |(p₀ : ℝ) - X| + |(r : ℝ)| := by
      calc |(p₀ : ℝ) + (r : ℝ) - X| = |((p₀ : ℝ) - X) + (r : ℝ)| := by ring_nf
        _ ≤ |(p₀ : ℝ) - X| + |(r : ℝ)| := abs_add_le _ _
    have h2 : |(p₀ : ℝ) - X| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    linarith [h1, h2, hrR]
  -- w in terms of Y along the constraint plane
  have hwY : |w - Y| ≤ (u * (1 + R₁) + η / 2) / v := by
    have hA : A = u * X + v * Y - η / 2 := by linarith [hplane]
    have hw2 : w = (u * (X - (p : ℝ)) - η / 2) / v + Y := by
      have h1 : v * w = A - u * p := hvw
      rw [hA] at h1
      field_simp
      linarith [h1]
    rw [hw2]
    have h3 : |(u * (X - (p : ℝ)) - η / 2) / v + Y - Y| = |u * (X - (p : ℝ)) - η / 2| / v := by
      rw [add_sub_cancel_right, abs_div, abs_of_pos hv]
    rw [h3, div_le_div_iff₀ hv hv]
    have h4 : |u * (X - (p : ℝ))| = u * |X - (p : ℝ)| := by
      rw [abs_mul, abs_of_pos hu]
    have h5 : |X - (p : ℝ)| ≤ 1 + R₁ := by rwa [abs_sub_comm]
    have hnum : |u * (X - (p : ℝ)) - η / 2| ≤ u * (1 + R₁) + η / 2 := by
      calc |u * (X - (p : ℝ)) - η / 2|
          = |u * (X - (p : ℝ)) + -(η / 2)| := by ring_nf
        _ ≤ |u * (X - (p : ℝ))| + |-(η / 2)| := abs_add_le _ _
        _ = u * |X - (p : ℝ)| + η / 2 := by
            rw [h4, abs_neg, abs_of_pos (by positivity : (0:ℝ) < η / 2)]
        _ ≤ u * (1 + R₁) + η / 2 := by
            have := mul_le_mul_of_nonneg_left h5 hu.le
            linarith
    nlinarith [hnum, hv]
  have hqw : |(q : ℝ) - w| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hwin1, hlam0]
    · linarith [hwin2, hlam1]
  have hqY : |(q : ℝ) - Y| ≤ C₂ := by
    have h1 : |(q : ℝ) - Y| ≤ |(q : ℝ) - w| + |w - Y| := abs_sub_le _ _ _
    simp only [hC₂def]
    linarith [hqw, hwY]
  -- nonnegativity
  have hRp : R₁ + 2 ≤ R := le_max_left _ _
  have hRq : C₂ + 1 ≤ R := le_max_right _ _
  have hp0 : 0 ≤ p := by
    have h1 : X - (1 + R₁) ≤ (p : ℝ) := by
      have := abs_le.mp hpX
      linarith [this.1]
    have h2 : (1 : ℝ) ≤ (p : ℝ) := by linarith [hX, hRp]
    exact_mod_cast le_trans (by norm_num : (0:ℝ) ≤ 1) h2
  have hq0 : 0 ≤ q := by
    have h1 : Y - C₂ ≤ (q : ℝ) := by
      have := abs_le.mp hqY
      linarith [this.1]
    have h2 : (1 : ℝ) ≤ (q : ℝ) := by linarith [hY, hRq]
    exact_mod_cast le_trans (by norm_num : (0:ℝ) ≤ 1) h2
  exact ⟨p, q, hp0, hq0, hstrip1.le, hstrip2, hpX.trans (by linarith),
    hqY.trans (by linarith)⟩

/-! ## Logarithm bookkeeping -/

section Logs

variable {a b c : ℕ}

/-- `log(3/2) > 0`. -/
lemma eta_pos : (0 : ℝ) < Real.log (3 / 2) := Real.log_pos (by norm_num)

/-- `log(3/2) < log d` for `d ≥ 2`. -/
lemma eta_lt_log {d : ℕ} (hd : 2 ≤ d) : Real.log (3 / 2) < Real.log d := by
  apply Real.log_lt_log (by norm_num)
  have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  linarith

lemma log_base_pos {d : ℕ} (hd : 2 ≤ d) : (0 : ℝ) < Real.log d := by
  apply Real.log_pos
  exact_mod_cast hd

end Logs

/-! ## Three-coordinate slab rounding (paper Lemma 2.4) -/

section ThreeRounding

variable {a b c : ℕ}

/-- **Uniform rounding to the exponent slab.** With `α = log a`, `β = log b`, `γ = log c`,
`η = log(3/2)`: there is `R₀ ≥ 1` such that any nonnegative real target `(X,Y,Z)` on the
plane `αX + βY + γZ = L + η/2`, having at most one zero coordinate and all positive
coordinates `≥ 2R₀`, rounds to `(k,ℓ,m) ∈ ℕ³` with
`L ≤ αk + βℓ + γm < L + η`, coordinatewise within `R₀`, preserving zero coordinates. -/
theorem three_rounding (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L X Y Z : ℝ, 0 ≤ X → 0 ≤ Y → 0 ≤ Z →
      ¬(X = 0 ∧ Y = 0) → ¬(X = 0 ∧ Z = 0) → ¬(Y = 0 ∧ Z = 0) →
      (X = 0 ∨ 2 * R₀ ≤ X) → (Y = 0 ∨ 2 * R₀ ≤ Y) → (Z = 0 ∨ 2 * R₀ ≤ Z) →
      X * Real.log a + Y * Real.log b + Z * Real.log c = L + Real.log (3 / 2) / 2 →
      ∃ k l m : ℕ,
        (L ≤ k * Real.log a + l * Real.log b + m * Real.log c ∧
          k * Real.log a + l * Real.log b + m * Real.log c < L + Real.log (3 / 2)) ∧
        |(k : ℝ) - X| ≤ R₀ ∧ |(l : ℝ) - Y| ≤ R₀ ∧ |(m : ℝ) - Z| ≤ R₀ ∧
        (X = 0 → k = 0) ∧ (Y = 0 → l = 0) ∧ (Z = 0 → m = 0) := by
  obtain ⟨hab, hac, hbc⟩ := hco
  set α : ℝ := Real.log a with hαdef
  set β : ℝ := Real.log b with hβdef
  set γ : ℝ := Real.log c with hγdef
  set η : ℝ := Real.log (3 / 2) with hηdef
  have hα : 0 < α := log_base_pos ha
  have hβ : 0 < β := log_base_pos hb
  have hγ : 0 < γ := log_base_pos hc
  have hη : 0 < η := eta_pos
  have hηα : η < α := eta_lt_log ha
  have hηβ : η < β := eta_lt_log hb
  have hηγ : η < γ := eta_lt_log hc
  -- the three irrational ratios
  have hirr_ac : Irrational (α / γ) := by
    simpa [hαdef, hγdef] using log_ratio_irrational hac.symm hc ha
  have hirr_bc : Irrational (β / γ) := by
    simpa [hβdef, hγdef] using log_ratio_irrational hbc.symm hc hb
  have hirr_ab : Irrational (α / β) := by
    simpa [hαdef, hβdef] using log_ratio_irrational hab.symm hb ha
  obtain ⟨Rac, hRac1, hRac⟩ := two_rounding hα hγ hirr_ac hη hηγ
  obtain ⟨Rbc, hRbc1, hRbc⟩ := two_rounding hβ hγ hirr_bc hη hηγ
  obtain ⟨Rab, hRab1, hRab⟩ := two_rounding hα hβ hirr_ab hη hηβ
  set R₀ : ℝ := 1 + Rac + Rbc + Rab + β / (2 * γ) with hR₀def
  have hβγ0 : 0 < β / (2 * γ) := by positivity
  have hR₀1 : 1 ≤ R₀ := by simp only [hR₀def]; linarith
  refine ⟨R₀, hR₀1, fun L X Y Z hX0 hY0 hZ0 hXY hXZ hYZ hXalt hYalt hZalt hplane => ?_⟩
  by_cases hX : X = 0
  · -- k = 0; round (Y, Z) with the pair (β, γ)
    have hY' : 2 * R₀ ≤ Y := by
      rcases hYalt with h | h
      · exact absurd ⟨hX, h⟩ hXY
      · exact h
    have hZ' : 2 * R₀ ≤ Z := by
      rcases hZalt with h | h
      · exact absurd ⟨hX, h⟩ hXZ
      · exact h
    have hplane' : β * Y + γ * Z = L + η / 2 := by
      rw [hX] at hplane; linarith [hplane]
    have hYR : Rbc ≤ Y := by linarith [hR₀1, hRbc1, hβγ0, hRac1, hRab1]
    have hZR : Rbc ≤ Z := by linarith [hR₀1, hRbc1, hβγ0, hRac1, hRab1]
    obtain ⟨p, q, hp0, hq0, hlo, hhi, hpY, hqZ⟩ := hRbc L Y Z hYR hZR hplane'
    refine ⟨0, p.toNat, q.toNat, ?_, ?_, ?_, ?_, fun _ => rfl, ?_, ?_⟩
    · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hp0
      have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hq0
      constructor
      · push_cast
        rw [hpcast, hqcast]
        linarith [hlo]
      · push_cast
        rw [hpcast, hqcast]
        linarith [hhi]
    · rw [hX]
      simp only [Nat.cast_zero, sub_zero, abs_zero]
      linarith
    · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hp0
      rw [hpcast]
      linarith [hpY, hR₀1, hRac1, hRab1, hβγ0]
    · have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hq0
      rw [hqcast]
      linarith [hqZ, hR₀1, hRac1, hRab1, hβγ0]
    · intro hY'0
      exfalso
      rw [hY'0] at hY'
      linarith [hR₀1]
    · intro hZ'0
      exfalso
      rw [hZ'0] at hZ'
      linarith [hR₀1]
  · by_cases hY : Y = 0
    · -- l = 0; round (X, Z) with the pair (α, γ)
      have hX' : 2 * R₀ ≤ X := by
        rcases hXalt with h | h
        · exact absurd h hX
        · exact h
      have hZ' : 2 * R₀ ≤ Z := by
        rcases hZalt with h | h
        · exact absurd ⟨hY, h⟩ hYZ
        · exact h
      have hplane' : α * X + γ * Z = L + η / 2 := by
        rw [hY] at hplane; linarith [hplane]
      have hXR : Rac ≤ X := by linarith [hR₀1, hRac1, hβγ0, hRbc1, hRab1]
      have hZR : Rac ≤ Z := by linarith [hR₀1, hRac1, hβγ0, hRbc1, hRab1]
      obtain ⟨p, q, hp0, hq0, hlo, hhi, hpX, hqZ⟩ := hRac L X Z hXR hZR hplane'
      refine ⟨p.toNat, 0, q.toNat, ?_, ?_, ?_, ?_, ?_, fun _ => rfl, ?_⟩
      · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hp0
        have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hq0
        constructor
        · push_cast
          rw [hpcast, hqcast]
          linarith [hlo]
        · push_cast
          rw [hpcast, hqcast]
          linarith [hhi]
      · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hp0
        rw [hpcast]
        linarith [hpX, hR₀1, hRbc1, hRab1, hβγ0]
      · rw [hY]
        simp only [Nat.cast_zero, sub_zero, abs_zero]
        linarith
      · have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hq0
        rw [hqcast]
        linarith [hqZ, hR₀1, hRbc1, hRab1, hβγ0]
      · intro hX'0; exact absurd hX'0 hX
      · intro hZ'0
        exfalso
        rw [hZ'0] at hZ'
        linarith [hR₀1]
    · by_cases hZ : Z = 0
      · -- m = 0; round (X, Y) with the pair (α, β)
        have hX' : 2 * R₀ ≤ X := by
          rcases hXalt with h | h
          · exact absurd h hX
          · exact h
        have hY' : 2 * R₀ ≤ Y := by
          rcases hYalt with h | h
          · exact absurd h hY
          · exact h
        have hplane' : α * X + β * Y = L + η / 2 := by
          rw [hZ] at hplane; linarith [hplane]
        have hXR : Rab ≤ X := by linarith [hR₀1, hRab1, hβγ0, hRbc1, hRac1]
        have hYR : Rab ≤ Y := by linarith [hR₀1, hRab1, hβγ0, hRbc1, hRac1]
        obtain ⟨p, q, hp0, hq0, hlo, hhi, hpX, hqY⟩ := hRab L X Y hXR hYR hplane'
        refine ⟨p.toNat, q.toNat, 0, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => rfl⟩
        · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hp0
          have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hq0
          constructor
          · push_cast
            rw [hpcast, hqcast]
            linarith [hlo]
          · push_cast
            rw [hpcast, hqcast]
            linarith [hhi]
        · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hp0
          rw [hpcast]
          linarith [hpX, hR₀1, hRbc1, hRac1, hβγ0]
        · have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hq0
          rw [hqcast]
          linarith [hqY, hR₀1, hRbc1, hRac1, hβγ0]
        · rw [hZ]
          simp only [Nat.cast_zero, sub_zero, abs_zero]
          linarith
        · intro hX'0; exact absurd hX'0 hX
        · intro hY'0; exact absurd hY'0 hY
      · -- main case: X, Y, Z > 0; round Y to ℓ₀ and (X, Z') with the pair (α, γ)
        have hX' : 2 * R₀ ≤ X := by
          rcases hXalt with h | h
          · exact absurd h hX
          · exact h
        have hY' : 2 * R₀ ≤ Y := by
          rcases hYalt with h | h
          · exact absurd h hY
          · exact h
        have hZ' : 2 * R₀ ≤ Z := by
          rcases hZalt with h | h
          · exact absurd h hZ
          · exact h
        set l₀ : ℤ := round Y with hl₀def
        have hl₀Y : |(l₀ : ℝ) - Y| ≤ 1 / 2 := by
          rw [abs_sub_comm]
          exact abs_sub_round Y
        have hl₀pos : (1 : ℝ) ≤ (l₀ : ℝ) := by
          have h1 := abs_le.mp hl₀Y
          linarith [hY', hR₀1, h1.1]
        have hl₀0 : 0 ≤ l₀ := by exact_mod_cast le_trans (by norm_num : (0:ℝ) ≤ 1) hl₀pos
        set Z' : ℝ := Z + (β / γ) * (Y - (l₀ : ℝ)) with hZ'def
        have hZ'Z : |Z' - Z| ≤ β / (2 * γ) := by
          simp only [hZ'def, add_sub_cancel_left]
          rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < β / γ), abs_sub_comm]
          calc (β / γ) * |(l₀ : ℝ) - Y| ≤ (β / γ) * (1 / 2) :=
                mul_le_mul_of_nonneg_left hl₀Y (by positivity)
            _ = β / (2 * γ) := by ring
        have hplane' : α * X + γ * Z' = (L - β * l₀) + η / 2 := by
          have hexp : γ * (β / γ * (Y - (l₀ : ℝ))) = β * (Y - (l₀ : ℝ)) := by
            have hγne : γ ≠ 0 := hγ.ne'
            field_simp
          calc α * X + γ * Z'
              = α * X + γ * Z + γ * (β / γ * (Y - (l₀ : ℝ))) := by
                rw [hZ'def]; ring
            _ = α * X + γ * Z + β * (Y - (l₀ : ℝ)) := by rw [hexp]
            _ = (L - β * l₀) + η / 2 := by linarith [hplane]
        have hXR : Rac ≤ X := by linarith [hR₀1, hRac1, hβγ0, hRbc1, hRab1]
        have hZ'R : Rac ≤ Z' := by
          have h1 := abs_le.mp hZ'Z
          have h2 : Z - β / (2 * γ) ≤ Z' := by linarith [h1.1]
          simp only [hR₀def] at hZ'
          linarith [hZ', hRbc1, hRab1]
        obtain ⟨p, q, hp0, hq0, hlo, hhi, hpX, hqZ'⟩ :=
          hRac (L - β * l₀) X Z' hXR hZ'R hplane'
        refine ⟨p.toNat, l₀.toNat, q.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hp0
          have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hq0
          have hlcast : ((l₀.toNat : ℕ) : ℝ) = (l₀ : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hl₀0
          constructor
          · push_cast
            rw [hpcast, hqcast, hlcast]
            linarith [hlo]
          · push_cast
            rw [hpcast, hqcast, hlcast]
            linarith [hhi]
        · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hp0
          rw [hpcast]
          linarith [hpX, hR₀1, hRbc1, hRab1, hβγ0]
        · have hlcast : ((l₀.toNat : ℕ) : ℝ) = (l₀ : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hl₀0
          rw [hlcast]
          calc |(l₀ : ℝ) - Y| ≤ 1 / 2 := hl₀Y
            _ ≤ R₀ := by linarith [hR₀1]
        · have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hq0
          rw [hqcast]
          have h1 : |(q : ℝ) - Z| ≤ |(q : ℝ) - Z'| + |Z' - Z| := abs_sub_le _ _ _
          simp only [hR₀def]
          linarith [hqZ', hZ'Z, hRbc1, hRab1]
        · intro hX'0; exact absurd hX'0 hX
        · intro hY'0; exact absurd hY'0 hY
        · intro hZ'0; exact absurd hZ'0 hZ

end ThreeRounding

/-! ## Three-base unique factorization -/

section UniqueFactorization

variable {a b c : ℕ}

/-- Unique factorization for three pairwise-coprime bases. -/
theorem coprime3_pow_inj (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) {k l m k' l' m' : ℕ}
    (h : a ^ k * b ^ l * c ^ m = a ^ k' * b ^ l' * c ^ m') :
    k = k' ∧ l = l' ∧ m = m' := by
  obtain ⟨hab, hac, hbc⟩ := hco
  have key : ∀ {k l m k' l' m' : ℕ}, a ^ k * b ^ l * c ^ m = a ^ k' * b ^ l' * c ^ m' →
      k ≤ k' → k = k' := by
    intro k l m k' l' m' h hkk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkk
    have hpos : 0 < a ^ k := pow_pos (by omega) k
    have h2 : b ^ l * c ^ m = a ^ d * (b ^ l' * c ^ m') := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc a ^ k * (b ^ l * c ^ m) = a ^ k * b ^ l * c ^ m := by ring
        _ = a ^ (k + d) * b ^ l' * c ^ m' := h
        _ = a ^ k * (a ^ d * (b ^ l' * c ^ m')) := by rw [pow_add]; ring
    have hdvd : a ^ d ∣ b ^ l * c ^ m := ⟨b ^ l' * c ^ m', h2⟩
    have hcop : Nat.Coprime (a ^ d) (b ^ l * c ^ m) :=
      Nat.Coprime.mul_right (hab.pow d l) (hac.pow d m)
    have had1 : a ^ d = 1 := (Nat.gcd_eq_left hdvd).symm.trans hcop
    have hd0 : d = 0 := by
      rcases Nat.pow_eq_one.mp had1 with h1 | h1
      · omega
      · exact h1
    omega
  have hk : k = k' := by
    rcases le_total k k' with h' | h'
    · exact key h h'
    · exact (key h.symm h').symm
  subst hk
  have hpos : 0 < a ^ k := pow_pos (by omega) k
  have h2 : b ^ l * c ^ m = b ^ l' * c ^ m' := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc a ^ k * (b ^ l * c ^ m) = a ^ k * b ^ l * c ^ m := by ring
      _ = a ^ k * b ^ l' * c ^ m' := h
      _ = a ^ k * (b ^ l' * c ^ m') := by ring
  obtain ⟨hl, hm⟩ := coprime_pow_inj hbc hb hc h2
  exact ⟨rfl, hl, hm⟩

/-- A classical choice of exponent triple for a member of `Smooth3`. -/
noncomputable def expTriple (a b c s : ℕ) : ℕ × ℕ × ℕ :=
  letI := Classical.dec (s ∈ Smooth3 a b c)
  if h : s ∈ Smooth3 a b c then
    (h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose)
  else (0, 0, 0)

lemma expTriple_spec {s : ℕ} (h : s ∈ Smooth3 a b c) :
    s = a ^ (expTriple a b c s).1 * b ^ (expTriple a b c s).2.1
      * c ^ (expTriple a b c s).2.2 := by
  classical
  unfold expTriple
  rw [dif_pos h]
  exact h.choose_spec.choose_spec.choose_spec

end UniqueFactorization

/-! ## The L² band-count upper bound (part of paper Prop 3.2) -/

section BandCount

variable {a b c : ℕ}

/-- **Band-count upper bound**: `|B_x| ≤ (log₂(2x) + 1)²`.  A band element is
determined by its `(k, ℓ)` exponents alone (a width-3/2 window cannot contain
two elements with ratio a power of `c ≥ 2`). -/
theorem band_card_le_sq (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) (x : ℕ) :
    (Band a b c x).card ≤ (Nat.log 2 (2 * x) + 1) ^ 2 := by
  classical
  set K := Nat.log 2 (2 * x) with hK
  set f : ℕ → ℕ × ℕ := fun s => ((expTriple a b c s).1, (expTriple a b c s).2.1) with hf
  have hmaps : ∀ s ∈ Band a b c x, f s ∈ Finset.range (K + 1) ×ˢ Finset.range (K + 1) := by
    intro s hs
    obtain ⟨hS, hxs, h2s⟩ := mem_Band.mp hs
    have hspos : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · exfalso; omega
      · exact h0
    have hs2x : s < 2 * x := by omega
    have hspec := expTriple_spec (a := a) (b := b) (c := c) hS
    set k := (expTriple a b c s).1
    set l := (expTriple a b c s).2.1
    set m := (expTriple a b c s).2.2
    have hbpos : 0 < b ^ l := pow_pos (by omega) l
    have hcpos : 0 < c ^ m := pow_pos (by omega) m
    have hapos : 0 < a ^ k := pow_pos (by omega) k
    have hak : a ^ k ≤ s := by
      rw [hspec, mul_assoc]
      exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hbpos hcpos)
    have hbl : b ^ l ≤ s := by
      rw [hspec]
      calc b ^ l ≤ a ^ k * b ^ l := Nat.le_mul_of_pos_left _ hapos
        _ ≤ a ^ k * b ^ l * c ^ m := Nat.le_mul_of_pos_right _ hcpos
    have hbound : ∀ d e : ℕ, 2 ≤ d → d ^ e ≤ s → e ≤ K := by
      intro d e hd hde
      rw [hK]
      refine Nat.le_log_of_pow_le (by norm_num) ?_
      calc 2 ^ e ≤ d ^ e := Nat.pow_le_pow_left hd e
        _ ≤ s := hde
        _ ≤ 2 * x := by omega
    simp only [hf, Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hbound a k ha hak), Nat.lt_succ_of_le (hbound b l hb hbl)⟩
  have hinj : Set.InjOn f (Band a b c x) := by
    intro s hs s' hs' heq
    obtain ⟨hS, hxs, h2s⟩ := mem_Band.mp hs
    obtain ⟨hS', hxs', h2s'⟩ := mem_Band.mp hs'
    have hspec := expTriple_spec (a := a) (b := b) (c := c) hS
    have hspec' := expTriple_spec (a := a) (b := b) (c := c) hS'
    have hkk : (expTriple a b c s).1 = (expTriple a b c s').1 := by
      have := congrArg Prod.fst heq; simpa [hf] using this
    have hll : (expTriple a b c s).2.1 = (expTriple a b c s').2.1 := by
      have := congrArg Prod.snd heq; simpa [hf] using this
    set k := (expTriple a b c s).1
    set l := (expTriple a b c s).2.1
    set m := (expTriple a b c s).2.2
    set m' := (expTriple a b c s').2.2
    rw [← hkk, ← hll] at hspec'
    -- s = a^k b^l c^m, s' = a^k b^l c^m'; the band forces m = m'
    have hmm : m = m' := by
      by_contra hne
      -- wlog m < m'
      rcases Nat.lt_or_ge m m' with hlt | hge
      · -- s' = s * c^(m'-m) ≥ 2 s, contradicting the band width
        have hdiv : s' = s * c ^ (m' - m) := by
          have hpow : c ^ m * c ^ (m' - m) = c ^ m' := by
            rw [← pow_add]
            congr 1
            omega
          rw [hspec, hspec', ← hpow]
          ring
        have hcge : 2 ≤ c ^ (m' - m) := by
          calc 2 ≤ c := hc
            _ = c ^ 1 := (pow_one c).symm
            _ ≤ c ^ (m' - m) := Nat.pow_le_pow_right (by omega) (by omega)
        have : 2 * s ≤ s' := by
          calc 2 * s = s * 2 := by ring
            _ ≤ s * c ^ (m' - m) := Nat.mul_le_mul_left s hcge
            _ = s' := hdiv.symm
        omega
      · have hlt : m' < m := by omega
        have hdiv : s = s' * c ^ (m - m') := by
          have hpow : c ^ m' * c ^ (m - m') = c ^ m := by
            rw [← pow_add]
            congr 1
            omega
          rw [hspec, hspec', ← hpow]
          ring
        have hcge : 2 ≤ c ^ (m - m') := by
          calc 2 ≤ c := hc
            _ = c ^ 1 := (pow_one c).symm
            _ ≤ c ^ (m - m') := Nat.pow_le_pow_right (by omega) (by omega)
        have : 2 * s' ≤ s := by
          calc 2 * s' = s' * 2 := by ring
            _ ≤ s' * c ^ (m - m') := Nat.mul_le_mul_left s' hcge
            _ = s := hdiv.symm
        omega
    rw [hspec, hspec', hmm]
  calc (Band a b c x).card
      ≤ (Finset.range (K + 1) ×ˢ Finset.range (K + 1)).card :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ = (K + 1) ^ 2 := by
        rw [Finset.card_product, Finset.card_range]; ring

end BandCount

/-! ## The Band ↔ slab dictionary -/

section Dictionary

variable {a b c : ℕ}

/-- Membership of a monomial in the band, in logarithmic (slab) coordinates. -/
theorem mem_Band_iff_slab (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    {x : ℕ} (hx : 1 ≤ x) (k l m : ℕ) :
    a ^ k * b ^ l * c ^ m ∈ Band a b c x ↔
      (Real.log x ≤ k * Real.log a + l * Real.log b + m * Real.log c ∧
        k * Real.log a + l * Real.log b + m * Real.log c
          < Real.log x + Real.log (3 / 2)) := by
  set s : ℕ := a ^ k * b ^ l * c ^ m with hsdef
  have hapos : (0 : ℝ) < (a : ℝ) := by
    have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hcpos : (0 : ℝ) < (c : ℝ) := by
    have : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    linarith
  have hspos : 0 < s := by
    simp only [hsdef]
    positivity
  have hsposR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos
  have hxposR : (0 : ℝ) < (x : ℝ) := by
    have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hlogs : Real.log s = k * Real.log a + l * Real.log b + m * Real.log c := by
    have hcast : (s : ℝ) = (a : ℝ) ^ k * (b : ℝ) ^ l * (c : ℝ) ^ m := by
      simp only [hsdef]; push_cast; ring
    rw [hcast, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
  have hmemS : s ∈ Smooth3 a b c := ⟨k, l, m, rfl⟩
  rw [mem_Band]
  constructor
  · rintro ⟨-, hxs, h2s⟩
    constructor
    · rw [← hlogs]
      apply Real.log_le_log hxposR
      exact_mod_cast hxs
    · rw [← hlogs]
      have h1 : (s : ℝ) < 3 / 2 * (x : ℝ) := by
        have : (2 * s : ℝ) < (3 * x : ℝ) := by exact_mod_cast h2s
        linarith
      have h2 : Real.log s < Real.log (3 / 2 * (x : ℝ)) :=
        Real.log_lt_log hsposR h1
      rw [Real.log_mul (by norm_num) hxposR.ne'] at h2
      linarith
  · rintro ⟨hlo, hhi⟩
    refine ⟨hmemS, ?_, ?_⟩
    · rw [← hlogs] at hlo
      have h1 : (x : ℝ) ≤ (s : ℝ) := by
        have := Real.log_le_log_iff hxposR hsposR
        exact this.mp hlo
      exact_mod_cast h1
    · rw [← hlogs] at hhi
      have h1 : Real.log s < Real.log (3 / 2 * (x : ℝ)) := by
        rw [Real.log_mul (by norm_num) hxposR.ne']
        linarith
      have h2 : (s : ℝ) < 3 / 2 * (x : ℝ) :=
        (Real.log_lt_log_iff hsposR (by positivity)).mp h1
      have h3 : (2 * s : ℝ) < (3 * x : ℝ) := by linarith
      exact_mod_cast h3

end Dictionary

end Erdos123Band
