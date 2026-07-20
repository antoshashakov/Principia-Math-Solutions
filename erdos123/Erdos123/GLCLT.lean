/-
ERDŐS #123 — LOCAL CENTRAL LIMIT THEOREM (paper §4), general ratio `ρ = p/q`.

This file is the FINAL ASSEMBLY of the three-range Fourier split:

  * `gprincipal_lower` (Erdos123.GPrincipal) : `∫₀^{t₁} ≥ 1/(5V)`
  * `gtail_upper`      (Erdos123.GTail)      : `|∫_{t₁}^{1/2}| ≤ 1/(10V)`
  * `gsplit_half`      (Erdos123.GBandAux)   : `∫₀¹ = 2·∫₀^{1/2}`
  * `subsetSum_fourier`(Erdos123.Band)       : `#{T ⊆ B : ΣT = n} = ∫₀¹ ∏(1+e(st))·e(−nt)`
  * `gintegrand_re`    (Erdos123.GBand)      : the real part of that integrand

giving `#{T ⊆ B_x : ΣT = n} = 2^{|B_x|}·∫₀¹ (∏cos πst)·cos(π(S₁−2n)t) dt ≥ 2^{|B_x|}/(5V) > 0`
for every `n` in the FULL central window `(2n − S₁)² ≤ S₂`, hence `glclt_coverage`.
-/
import Erdos123.GTail
import Erdos123.GBandAux
import Erdos123.GaussFT

set_option maxHeartbeats 1000000

namespace Erdos123Band

open MeasureTheory

/-- **The counting identity.** The number of subsets of the general band summing to `n`
equals `2^{|B|}` times the real Fourier integral. -/
theorem gcount_eq_integral (a b c p q x n : ℕ) :
    ((((GBand a b c p q x).powerset.filter (fun T => ∑ s ∈ T, s = n)).card : ℕ) : ℝ)
      = 2 ^ (GBand a b c p q x).card
        * ∫ t in (0:ℝ)..1,
            (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
              * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) := by
  classical
  have hcont : Continuous
      (fun t : ℝ => (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))) := by
    fun_prop
  have hIoc : IntegrableOn
      (fun t : ℝ => (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))
      (Set.Ioc (0:ℝ) 1) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hcont.intervalIntegrable 0 1
  have hfourier : (∫ t in (0:ℝ)..1,
        (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))
      = ((((GBand a b c p q x).powerset.filter (fun T => ∑ s ∈ T, s = n)).card : ℕ) : ℂ) :=
    subsetSum_fourier (GBand a b c p q x) n
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] at hfourier
  have h2 := congrArg Complex.re hfourier
  simp only [Complex.natCast_re] at h2
  have hre : (∫ t in Set.Ioc (0:ℝ) 1,
        (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = ∫ t in Set.Ioc (0:ℝ) 1,
          ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re := by
    simpa using (Complex.reCLM.integral_comp_comm hIoc).symm
  have hcongr : (∫ t in Set.Ioc (0:ℝ) 1,
        ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re)
      = ∫ t in Set.Ioc (0:ℝ) 1, 2 ^ (GBand a b c p q x).card *
          ((∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    rw [gintegrand_re a b c p q x n t, mul_assoc]
  rw [hre, hcongr, MeasureTheory.integral_const_mul] at h2
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact h2.symm

/-- **The local CLT coverage, general ratio.** For all sufficiently large `x`, every `n`
in the FULL central window `(2n − S₁)² ≤ S₂` is a subset sum of the band. -/
theorem glclt_coverage (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      (2 * (n : ℤ) - (GS1 a b c p q x : ℤ)) ^ 2 ≤ (GS2 a b c p q x : ℤ) →
      ∃ T : Finset ℕ, T ⊆ GBand a b c p q x ∧ T.sum id = n := by
  classical
  obtain ⟨X₁, hprin⟩ := gprincipal_lower a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨X₂, htail⟩ := gtail_upper a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨cV, hcV, X₃, hVlow⟩ := gV_lower a b c p q ha hb hc hco hq hqp hpd
  refine ⟨max (max X₁ X₂) (max X₃ 3), fun x hx n hn => ?_⟩
  have hxX₁ : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxX₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxX₃ : X₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxR : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx3
  have hlog : (1:ℝ) ≤ Real.log x := one_le_log hx3
  have hVpos : (0:ℝ) < Real.sqrt (GS2 a b c p q x) := by
    have hpos : (0:ℝ) < cV * (x:ℝ) * Real.log x :=
      mul_pos (mul_pos hcV (by linarith)) (by linarith)
    linarith [hVlow x hxX₃]
  have hP := hprin x hxX₁ n hn
  have hTl := abs_le.mp (htail x hxX₂ n)
  -- adjacent-interval split of `∫₀^{1/2}`
  have hsplit :
      (∫ t in (0:ℝ)..(gt₁ a b c p q x),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)))
        + (∫ t in (gt₁ a b c p q x)..(1/2 : ℝ),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)))
      = ∫ t in (0:ℝ)..(1/2 : ℝ),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) :=
    intervalIntegral.integral_add_adjacent_intervals
      ((gintegrand_continuous a b c p q x n).intervalIntegrable (μ := volume)
        0 (gt₁ a b c p q x))
      ((gintegrand_continuous a b c p q x n).intervalIntegrable (μ := volume)
        (gt₁ a b c p q x) (1/2 : ℝ))
  have hid : (1:ℝ) / (5 * Real.sqrt (GS2 a b c p q x))
      = 2 * (1 / (10 * Real.sqrt (GS2 a b c p q x))) := by
    have hne : Real.sqrt (GS2 a b c p q x) ≠ 0 := ne_of_gt hVpos
    first
      | (field_simp; ring)
      | field_simp
  have hhalf : 1 / (10 * Real.sqrt (GS2 a b c p q x))
      ≤ ∫ t in (0:ℝ)..(1/2 : ℝ),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) := by
    rw [← hsplit]; linarith [hP, hTl.1]
  have hfull : 1 / (5 * Real.sqrt (GS2 a b c p q x))
      ≤ ∫ t in (0:ℝ)..1,
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) := by
    rw [gsplit_half a b c p q x n]; linarith [hhalf]
  have hIpos : (0:ℝ) < ∫ t in (0:ℝ)..1,
      (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
        * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) :=
    lt_of_lt_of_le (div_pos one_pos (by linarith)) hfull
  have hcnt : (0:ℝ)
      < ((((GBand a b c p q x).powerset.filter (fun T => ∑ s ∈ T, s = n)).card : ℕ) : ℝ) := by
    rw [gcount_eq_integral]
    exact mul_pos (by positivity) hIpos
  obtain ⟨T, hT⟩ := Finset.card_pos.mp (by exact_mod_cast hcnt)
  rw [Finset.mem_filter, Finset.mem_powerset] at hT
  exact ⟨T, hT.1, by simpa using hT.2⟩

end Erdos123Band
