/-
G-Aux — band-size, moment, and symmetry facts feeding the general-ratio local CLT.

Contents:
  * `gS4_le`               — fourth moment `≤ (px)² · GS2`
  * `gsum_sq_band`         — `∑ (s t)² = GS2 · t²`
  * `gintegrand_re_reflect`— the real integrand is invariant under `t ↦ 1 − t`
  * `gsplit_half`          — folding the full period onto the half period
  * `gV_lower`, `gV_upper` — two-sided `V = √GS2 ≍ x · log x`
-/
import Erdos123.GSlab
import Erdos123.MajorArcLB
import Erdos123.GGrid

set_option maxHeartbeats 1000000

namespace Erdos123Band

open Real MeasureTheory

/-! ## Fourth moment and the quadratic form -/

/-- Fourth moment bound: `∑ s⁴ ≤ (p x)² · GS2`. -/
theorem gS4_le {a b c p q : ℕ} (hq : 0 < q) (x : ℕ) :
    (∑ s ∈ GBand a b c p q x, (s : ℝ) ^ 4) ≤ ((p : ℝ) * (x : ℝ)) ^ 2 * (GS2 a b c p q x : ℝ) := by
  have hGS2 : (GS2 a b c p q x : ℝ) = ∑ s ∈ GBand a b c p q x, (s : ℝ) ^ 2 := by
    rw [GS2, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun s _ => by push_cast; ring)
  rw [hGS2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun s hs => ?_)
  have hsle : (s : ℝ) ≤ (p : ℝ) * (x : ℝ) := by
    have := gband_le hq hs
    have : ((s : ℕ) : ℝ) ≤ ((p * x : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hsq : (s : ℝ) ^ 2 ≤ ((p : ℝ) * (x : ℝ)) ^ 2 := by nlinarith
  calc (s : ℝ) ^ 4 = (s : ℝ) ^ 2 * (s : ℝ) ^ 2 := by ring
    _ ≤ ((p : ℝ) * (x : ℝ)) ^ 2 * (s : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- `∑_{s ∈ B} (s t)² = GS2 · t²`. -/
theorem gsum_sq_band (a b c p q x : ℕ) (t : ℝ) :
    (∑ s ∈ GBand a b c p q x, ((s : ℝ) * t) ^ 2) = (GS2 a b c p q x : ℝ) * t ^ 2 := by
  rw [GS2, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun s _ => by push_cast; ring)

/-! ## Reflection symmetry -/

/-- Reflection symmetry of the subset-sum integrand over the general band:
`f (1 − u) = conj (f u)`. -/
lemma gintegrand_reflect (a b c p q x n : ℕ) (u : ℝ) :
    (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * (1 - u)))) * e (-((n : ℝ) * (1 - u)))
      = (starRingEnd ℂ)
          ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * u))) * e (-((n : ℝ) * u))) := by
  rw [map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl (fun s _ => ?_)
    rw [map_add, map_one, e_conj]
    congr 1
    rw [show (s : ℝ) * (1 - u) = ((s : ℤ) : ℝ) + -((s : ℝ) * u) by push_cast; ring,
      e_add, e_int, one_mul]
  · rw [e_conj]
    rw [show -((n : ℝ) * (1 - u)) = ((-(n : ℤ) : ℤ) : ℝ) + (n : ℝ) * u by push_cast; ring,
      e_add, e_int, one_mul, neg_neg]

/-- The real integrand is invariant under `t ↦ 1 - t`. -/
theorem gintegrand_re_reflect (a b c p q x n : ℕ) (u : ℝ) :
    (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * (1 - u))))
        * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * (1 - u)))
      = (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * u)))
        * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * u)) := by
  have hkey : ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * (1 - u))))
        * e (-((n : ℝ) * (1 - u)))).re
      = ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * u))) * e (-((n : ℝ) * u))).re := by
    rw [gintegrand_reflect, Complex.conj_re]
  rw [gintegrand_re a b c p q x n (1 - u), gintegrand_re a b c p q x n u] at hkey
  have hpow : (0 : ℝ) < 2 ^ (GBand a b c p q x).card := by positivity
  rw [mul_assoc, mul_assoc] at hkey
  exact mul_left_cancel₀ (ne_of_gt hpow) hkey

/-! ## Folding the period -/

/-- Folding a continuous integrand that is symmetric about `t = 1/2`. -/
lemma gfold_half (F : ℝ → ℝ) (hcont : Continuous F) (hsymm : ∀ u : ℝ, F (1 - u) = F u) :
    (∫ t in (0:ℝ)..1, F t) = 2 * ∫ t in (0:ℝ)..(1/2), F t := by
  have hsplit : (∫ t in (0:ℝ)..1, F t)
      = (∫ t in (0:ℝ)..(1/2), F t) + ∫ t in (1/2:ℝ)..1, F t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 (1/2)) (hcont.intervalIntegrable (1/2) 1)).symm
  have hmirror : (∫ t in (1/2:ℝ)..1, F t) = ∫ t in (0:ℝ)..(1/2), F t := by
    have hsub : (∫ t in (0:ℝ)..(1/2 : ℝ), F (1 - t))
        = ∫ t in (1 - 1/2 : ℝ)..(1 - 0 : ℝ), F t :=
      intervalIntegral.integral_comp_sub_left F 1
    rw [show (1 - 1/2 : ℝ) = 1/2 by norm_num, sub_zero] at hsub
    rw [← hsub]
    exact intervalIntegral.integral_congr (fun u _ => hsymm u)
  rw [hsplit, hmirror]; ring

/-- Folding the full period onto the half period. -/
theorem gsplit_half (a b c p q x n : ℕ) :
    (∫ t in (0:ℝ)..1, (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
        * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)))
      = 2 * ∫ t in (0:ℝ)..(1/2),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) :=
  gfold_half
    (fun t => (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
      * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)))
    (by fun_prop)
    (gintegrand_re_reflect a b c p q x n)

/-! ## Two-sided bound `V = √GS2 ≍ x · log x` -/

/-- `Nat.log 2 m ≤ log m / log 2` for `m ≥ 1`.

The `Nat.log → Real.log` bridge. Mathlib also has the hypothesis-free
`Real.natLog_le_logb (a b : ℕ) : (Nat.log b a : ℝ) ≤ Real.logb b a`
(`Mathlib/Analysis/SpecialFunctions/Log/Base.lean:421`); this local version is a
direct transcription of `Erdos123.Band.natLog_two_le_realLog`, generalized from
`2 * x` to an arbitrary argument, and avoids unfolding `Real.logb`. -/
lemma gnatLog2_le_real (m : ℕ) (hm : 1 ≤ m) :
    (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpow : (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) := by
    have h := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
    calc (2 : ℝ) ^ Nat.log 2 m = ((2 ^ Nat.log 2 m : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (m : ℝ) := by exact_mod_cast h
  have hlog : Real.log ((2 : ℝ) ^ Nat.log 2 m) ≤ Real.log m :=
    Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  linarith

theorem gV_upper (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ CV : ℝ, 0 < CV ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      Real.sqrt (GS2 a b c p q x) ≤ CV * (x : ℝ) * Real.log x := by
  have hp : 0 < p := lt_trans hq hqp
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpc : p < q * c :=
    lt_of_lt_of_le hpd (Nat.mul_le_mul_left q (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨4 * (p : ℝ), by linarith, max 3 (2 * p), fun x hx => ?_⟩
  have hx3 : 3 ≤ x := le_trans (le_max_left _ _) hx
  have hx2p : 2 * p ≤ x := le_trans (le_max_right _ _) hx
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hL1 : 1 ≤ Real.log x := one_le_log hx3
  have h2p : (0 : ℝ) < ((2 * p : ℕ) : ℝ) := by
    have h : 0 < 2 * p := by omega
    exact_mod_cast h
  have hm1 : 1 ≤ 2 * p * x := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  have hKR0 : (0 : ℝ) ≤ ((Nat.log 2 (2 * p * x) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hKle : ((Nat.log 2 (2 * p * x) : ℕ) : ℝ)
      ≤ Real.log ((2 * p * x : ℕ) : ℝ) / Real.log 2 :=
    gnatLog2_le_real (2 * p * x) hm1
  have hsplit : Real.log ((2 * p * x : ℕ) : ℝ)
      = Real.log ((2 * p : ℕ) : ℝ) + Real.log x := by
    rw [show ((2 * p * x : ℕ) : ℝ) = ((2 * p : ℕ) : ℝ) * (x : ℝ) by push_cast; ring,
      Real.log_mul h2p.ne' hxpos.ne']
  have hlog2p : Real.log ((2 * p : ℕ) : ℝ) ≤ Real.log x :=
    Real.log_le_log h2p (by exact_mod_cast hx2p)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hKmul : ((Nat.log 2 (2 * p * x) : ℕ) : ℝ) * Real.log 2 ≤ 2 * Real.log x := by
    have h := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp hKle
    rw [hsplit] at h
    linarith
  have hprod : 0 ≤ ((Nat.log 2 (2 * p * x) : ℕ) : ℝ) * (Real.log 2 - 0.6931471803) :=
    mul_nonneg hKR0 (by linarith)
  have hK4 : ((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1 ≤ 4 * Real.log x := by nlinarith
  -- the moment bound
  have hcard := gband_card_le_sq (a := a) (b := b) (c := c) (p := p) (q := q)
    (by omega) (by omega) (by omega) hco hq hpc x
  have hS2 := gS2_upper (a := a) (b := b) (c := c) (p := p) (q := q) hq x
  have hchain : GS2 a b c p q x ≤ (Nat.log 2 (2 * p * x) + 1) ^ 2 * (p * x) ^ 2 :=
    le_trans hS2 (Nat.mul_le_mul_right _ hcard)
  have hchainR : (GS2 a b c p q x : ℝ)
      ≤ ((((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) * ((p : ℝ) * (x : ℝ))) ^ 2 := by
    have hc2 : ((GS2 a b c p q x : ℕ) : ℝ)
        ≤ (((Nat.log 2 (2 * p * x) + 1) ^ 2 * (p * x) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hchain
    calc (GS2 a b c p q x : ℝ)
        ≤ (((Nat.log 2 (2 * p * x) + 1) ^ 2 * (p * x) ^ 2 : ℕ) : ℝ) := hc2
      _ = ((((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) * ((p : ℝ) * (x : ℝ))) ^ 2 := by
          push_cast; ring
  have hnn : (0 : ℝ) ≤ (((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) * ((p : ℝ) * (x : ℝ)) := by
    positivity
  calc Real.sqrt (GS2 a b c p q x)
      ≤ Real.sqrt (((((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) * ((p : ℝ) * (x : ℝ))) ^ 2) :=
        Real.sqrt_le_sqrt hchainR
    _ = (((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) * ((p : ℝ) * (x : ℝ)) := Real.sqrt_sq hnn
    _ ≤ (4 * Real.log x) * ((p : ℝ) * (x : ℝ)) :=
        mul_le_mul_of_nonneg_right hK4 (by positivity)
    _ = 4 * (p : ℝ) * (x : ℝ) * Real.log x := by ring

theorem gV_lower (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ cV : ℝ, 0 < cV ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      cV * (x : ℝ) * Real.log x ≤ Real.sqrt (GS2 a b c p q x) := by
  obtain ⟨c₁, hc₁, X₁, hX₁⟩ := gband_card_ge_sq a b c p q ha hb hc hco hq hqp hpd
  refine ⟨Real.sqrt c₁, Real.sqrt_pos.mpr hc₁, max X₁ 3, fun x hx => ?_⟩
  have hx1 : X₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hL1 : 1 ≤ Real.log x := one_le_log hx3
  have hcard : c₁ * Real.log x ^ 2 ≤ ((GBand a b c p q x).card : ℝ) := hX₁ x hx1
  have hS2 : ((GBand a b c p q x).card : ℝ) * (x : ℝ) ^ 2 ≤ (GS2 a b c p q x : ℝ) := by
    have h := gS2_ge_card_sq a b c p q x
    have h2 : (((GBand a b c p q x).card * x ^ 2 : ℕ) : ℝ) ≤ ((GS2 a b c p q x : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h2
    linarith
  have hkey : c₁ * ((x : ℝ) * Real.log x) ^ 2 ≤ (GS2 a b c p q x : ℝ) := by
    have h2 : c₁ * Real.log x ^ 2 * (x : ℝ) ^ 2
        ≤ ((GBand a b c p q x).card : ℝ) * (x : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    calc c₁ * ((x : ℝ) * Real.log x) ^ 2 = c₁ * Real.log x ^ 2 * (x : ℝ) ^ 2 := by ring
      _ ≤ ((GBand a b c p q x).card : ℝ) * (x : ℝ) ^ 2 := h2
      _ ≤ (GS2 a b c p q x : ℝ) := hS2
  have hnn : (0 : ℝ) ≤ (x : ℝ) * Real.log x := mul_nonneg hxpos.le (by linarith)
  calc Real.sqrt c₁ * (x : ℝ) * Real.log x
      = Real.sqrt c₁ * Real.sqrt (((x : ℝ) * Real.log x) ^ 2) := by
        rw [Real.sqrt_sq hnn]; ring
    _ = Real.sqrt (c₁ * ((x : ℝ) * Real.log x) ^ 2) := (Real.sqrt_mul hc₁.le _).symm
    _ ≤ Real.sqrt (GS2 a b c p q x) := Real.sqrt_le_sqrt hkey

end Erdos123Band
