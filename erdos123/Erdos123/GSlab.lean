/-
G1 — Slab rounding for a general width `η` + the general-band dictionary and
L² band-count upper bound (generalizing `Erdos123.Slab` from `η = log(3/2)` to
`η = log p − log q`).

Contents:
  * `gthree_rounding`     — Lemma 2.4 with an arbitrary width `0 < η < min(log a, log b, log c)`
  * `mem_GBand_iff_slab`  — the GBand ↔ exponent-slab dictionary
  * `gband_card_le_sq`    — `|B_x| ≤ (log₂(2px)+1)²`

`finite_net` and `two_rounding` from `Erdos123.Slab` are already fully general and
are reused as-is.
-/
import Erdos123.GBand

set_option maxHeartbeats 1000000

namespace Erdos123Band

open Real

/-! ## Three-coordinate slab rounding, general width (paper Lemma 2.4) -/

section ThreeRounding

variable {a b c : ℕ}

/-- **Uniform rounding to the exponent slab, general width.** Identical to
`three_rounding` except that the slab width `η` is an arbitrary real with
`0 < η < min (log a) (min (log b) (log c))`. -/
theorem gthree_rounding (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) {η : ℝ} (hη : 0 < η)
    (hηα : η < Real.log a) (hηβ : η < Real.log b) (hηγ : η < Real.log c) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L X Y Z : ℝ, 0 ≤ X → 0 ≤ Y → 0 ≤ Z →
      ¬(X = 0 ∧ Y = 0) → ¬(X = 0 ∧ Z = 0) → ¬(Y = 0 ∧ Z = 0) →
      (X = 0 ∨ 2 * R₀ ≤ X) → (Y = 0 ∨ 2 * R₀ ≤ Y) → (Z = 0 ∨ 2 * R₀ ≤ Z) →
      X * Real.log a + Y * Real.log b + Z * Real.log c = L + η / 2 →
      ∃ k l m : ℕ,
        (L ≤ k * Real.log a + l * Real.log b + m * Real.log c ∧
          k * Real.log a + l * Real.log b + m * Real.log c < L + η) ∧
        |(k : ℝ) - X| ≤ R₀ ∧ |(l : ℝ) - Y| ≤ R₀ ∧ |(m : ℝ) - Z| ≤ R₀ ∧
        (X = 0 → k = 0) ∧ (Y = 0 → l = 0) ∧ (Z = 0 → m = 0) := by
  obtain ⟨hab, hac, hbc⟩ := hco
  set α : ℝ := Real.log a with hαdef
  set β : ℝ := Real.log b with hβdef
  set γ : ℝ := Real.log c with hγdef
  have hα : 0 < α := log_base_pos ha
  have hβ : 0 < β := log_base_pos hb
  have hγ : 0 < γ := log_base_pos hc
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

/-! ## The GBand ↔ slab dictionary -/

section Dictionary

variable {a b c p q : ℕ}

/-- Membership of a monomial in the general band, in logarithmic (slab) coordinates:
the slab has width `η = log p − log q`. -/
theorem mem_GBand_iff_slab (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hq : 0 < q) (hp : 0 < p) {x : ℕ} (hx : 1 ≤ x) (k l m : ℕ) :
    a ^ k * b ^ l * c ^ m ∈ GBand a b c p q x ↔
      (Real.log x ≤ k * Real.log a + l * Real.log b + m * Real.log c ∧
        k * Real.log a + l * Real.log b + m * Real.log c
          < Real.log x + (Real.log p - Real.log q)) := by
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
    exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
      (pow_pos (by omega) _)
  have hsposR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos
  have hxposR : (0 : ℝ) < (x : ℝ) := by
    have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hpposR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlogs : Real.log s = k * Real.log a + l * Real.log b + m * Real.log c := by
    have hcast : (s : ℝ) = (a : ℝ) ^ k * (b : ℝ) ^ l * (c : ℝ) ^ m := by
      simp only [hsdef]; push_cast; ring
    rw [hcast, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
  have hmemS : s ∈ Smooth3 a b c := ⟨k, l, m, rfl⟩
  rw [mem_GBand hq]
  constructor
  · rintro ⟨-, hxs, h2s⟩
    constructor
    · rw [← hlogs]
      apply Real.log_le_log hxposR
      exact_mod_cast hxs
    · rw [← hlogs]
      have h1 : (q : ℝ) * (s : ℝ) < (p : ℝ) * (x : ℝ) := by exact_mod_cast h2s
      have h2 : Real.log ((q : ℝ) * (s : ℝ)) < Real.log ((p : ℝ) * (x : ℝ)) :=
        Real.log_lt_log (by positivity) h1
      rw [Real.log_mul hqposR.ne' hsposR.ne', Real.log_mul hpposR.ne' hxposR.ne'] at h2
      linarith
  · rintro ⟨hlo, hhi⟩
    refine ⟨hmemS, ?_, ?_⟩
    · rw [← hlogs] at hlo
      have h1 : (x : ℝ) ≤ (s : ℝ) := by
        have := Real.log_le_log_iff hxposR hsposR
        exact this.mp hlo
      exact_mod_cast h1
    · rw [← hlogs] at hhi
      have h1 : Real.log ((q : ℝ) * (s : ℝ)) < Real.log ((p : ℝ) * (x : ℝ)) := by
        rw [Real.log_mul hqposR.ne' hsposR.ne', Real.log_mul hpposR.ne' hxposR.ne']
        linarith
      have h2 : (q : ℝ) * (s : ℝ) < (p : ℝ) * (x : ℝ) :=
        (Real.log_lt_log_iff (by positivity) (by positivity)).mp h1
      exact_mod_cast h2

end Dictionary

/-! ## The L² band-count upper bound -/

section BandCount

variable {a b c p q : ℕ}

/-- **Band-count upper bound**: `|B_x| ≤ (log₂(2px) + 1)²`. A band element is
determined by its `(k, ℓ)` exponents alone: two elements with ratio a power of
`c` differ by a factor `≥ c > p/q`, which does not fit in the band. -/
theorem gband_card_le_sq (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hpc : p < q * c) (x : ℕ) :
    (GBand a b c p q x).card ≤ (Nat.log 2 (2 * p * x) + 1) ^ 2 := by
  classical
  set K := Nat.log 2 (2 * p * x) with hK
  set f : ℕ → ℕ × ℕ := fun s => ((expTriple a b c s).1, (expTriple a b c s).2.1) with hf
  have hle2px : ∀ s ∈ GBand a b c p q x, s ≤ 2 * p * x := by
    intro s hs
    have h1 : s ≤ p * x := gband_le hq hs
    have h2 : p * x ≤ 2 * p * x := Nat.mul_le_mul_right x (by omega)
    omega
  have hmaps : ∀ s ∈ GBand a b c p q x,
      f s ∈ Finset.range (K + 1) ×ˢ Finset.range (K + 1) := by
    intro s hs
    obtain ⟨hS, hxs, h2s⟩ := of_mem_GBand hs
    have hspos : 0 < s := by
      obtain ⟨k, l, m, hklm⟩ := hS
      rw [hklm]
      exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
        (pow_pos (by omega) _)
    have hs2x : s ≤ 2 * p * x := hle2px s hs
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
        _ ≤ 2 * p * x := hs2x
    simp only [hf, Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hbound a k ha hak), Nat.lt_succ_of_le (hbound b l hb hbl)⟩
  have hinj : Set.InjOn f (GBand a b c p q x) := by
    intro s hs s' hs' heq
    obtain ⟨hS, hxs, h2s⟩ := of_mem_GBand hs
    obtain ⟨hS', hxs', h2s'⟩ := of_mem_GBand hs'
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
      rcases Nat.lt_or_ge m m' with hlt | hge
      · -- s' = s * c^(m'-m) ≥ c·s: q·s' ≥ q·c·s > p·s ≥ p·x, contradiction
        have hdiv : s' = s * c ^ (m' - m) := by
          have hpow : c ^ m * c ^ (m' - m) = c ^ m' := by
            rw [← pow_add]
            congr 1
            omega
          rw [hspec, hspec', ← hpow]
          ring
        have hcge : c ≤ c ^ (m' - m) := by
          calc c = c ^ 1 := (pow_one c).symm
            _ ≤ c ^ (m' - m) := Nat.pow_le_pow_right (by omega) (by omega)
        have hspos : 0 < s := by
          rw [hspec]
          exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
            (pow_pos (by omega) _)
        have h6 : q * c * s ≤ q * s' := by
          rw [hdiv]
          calc q * c * s = q * (c * s) := by ring
            _ ≤ q * (c ^ (m' - m) * s) :=
                Nat.mul_le_mul_left q (Nat.mul_le_mul_right s hcge)
            _ = q * (s * c ^ (m' - m)) := by ring
        have h7 : p * x ≤ p * s := Nat.mul_le_mul_left p hxs
        have h8 : p * s < q * c * s := (Nat.mul_lt_mul_right hspos).mpr hpc
        exact absurd (calc q * s' < p * x := h2s'
          _ ≤ p * s := h7
          _ < q * c * s := h8
          _ ≤ q * s' := h6) (lt_irrefl _)
      · have hlt : m' < m := by omega
        have hdiv : s = s' * c ^ (m - m') := by
          have hpow : c ^ m' * c ^ (m - m') = c ^ m := by
            rw [← pow_add]
            congr 1
            omega
          rw [hspec, hspec', ← hpow]
          ring
        have hcge : c ≤ c ^ (m - m') := by
          calc c = c ^ 1 := (pow_one c).symm
            _ ≤ c ^ (m - m') := Nat.pow_le_pow_right (by omega) (by omega)
        have hspos' : 0 < s' := by
          rw [hspec']
          exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
            (pow_pos (by omega) _)
        have h6 : q * c * s' ≤ q * s := by
          rw [hdiv]
          calc q * c * s' = q * (c * s') := by ring
            _ ≤ q * (c ^ (m - m') * s') :=
                Nat.mul_le_mul_left q (Nat.mul_le_mul_right s' hcge)
            _ = q * (s' * c ^ (m - m')) := by ring
        have h7 : p * x ≤ p * s' := Nat.mul_le_mul_left p hxs'
        have h8 : p * s' < q * c * s' := (Nat.mul_lt_mul_right hspos').mpr hpc
        exact absurd (calc q * s < p * x := h2s
          _ ≤ p * s' := h7
          _ < q * c * s' := h8
          _ ≤ q * s := h6) (lt_irrefl _)
    rw [hspec, hspec', hmm]
  calc (GBand a b c p q x).card
      ≤ (Finset.range (K + 1) ×ˢ Finset.range (K + 1)).card :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ = (K + 1) ^ 2 := by
        rw [Finset.card_product, Finset.card_range]; ring

end BandCount

end Erdos123Band
