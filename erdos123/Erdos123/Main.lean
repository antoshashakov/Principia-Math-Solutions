/-
The axiom-free assembly for Erdős problem #123 (band + local-CLT route).

Historically, `Erdos123.Band` carried three `axiom`s for the analytic inputs. Those
axioms have since been DELETED: nothing in this repository is axiomatized. This file
assembles the theorems that replaced them,
  * `major_arc_lower'`   (Erdos123.MajorArcLB)   — the Gaussian main term;
  * `lemma_5_2'`         (Erdos123.Rigidity)     — the minor-arc energy floor;
  * `low_energy_measure` (Erdos123.LowEnergy)    — the low-energy measure bound;
and reassembles

  `erdos123_dcomplete'` :
    ∀ a b c, 1 < a → 1 < b → 1 < c → PairwiseCoprime3 a b c →
      IsDComplete (Smooth3 a b c)

with axiom footprint exactly `[propext, Classical.choice, Quot.sound]`.

Differences from the (conditional) assembly in Band.lean:
  * the central window is `100·(2n − S1)² ≤ S2` (a 1/10-width window), paid for by
    a band-count `≥ 2500` in the sweep — this makes the major-arc lower bound
    elementary (no Gaussian Fourier transform needed);
  * the major-arc constant is existential (`C₅`) rather than the hard-coded `2`;
  * the low-energy input is the single-level bound `vol{Q ≤ log x} ≤ L^C₄/x`.
-/
import Erdos123.Band
import Erdos123.Rigidity
import Erdos123.MajorArcLB
import Erdos123.LowEnergy

set_option maxHeartbeats 1000000

namespace Erdos123Band

variable {a b c : ℕ}

/-- **Minor-arc bound** against an arbitrary main-term constant `C₅`. -/
theorem minor_arc_bound' (a b c : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (C₅ : ℝ) (hC₅ : 1 ≤ C₅) :
    ∃ X₄ : ℕ, ∀ x : ℕ, X₄ ≤ x →
      2 ^ (Band a b c x).card * (∫ t in MinorArc x, chiBand a b c x t)
        < (2 : ℝ) ^ (Band a b c x).card / (C₅ * (x : ℝ) * Real.log x) := by
  obtain ⟨C₄, hC₄, X₂, hprop⟩ := low_energy_measure a b c ha hb hc hco
  obtain ⟨κ₀, X₅, hκ₀, hfloor⟩ := lemma_5_2' a b c ha hb hc hco
  have hgrow : Filter.Tendsto
      (fun x : ℝ => C₅ * Real.log x ^ ((1 : ℝ) + C₄) * x ^ (-(2 * κ₀))
        + C₅ * Real.log x * x ^ (-(1 : ℝ))) Filter.atTop (nhds 0) := by
    have h1 := poly_log_rpow_tendsto (p := (1 : ℝ) + C₄) (q := 2 * κ₀) (by linarith)
    have h2 := poly_log_rpow_tendsto (p := (1 : ℝ)) (q := (1 : ℝ)) (by norm_num)
    have hsum := (h1.const_mul C₅).add (h2.const_mul C₅)
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr (fun x => ?_)
    rw [Real.rpow_one]
    ring
  have hev := (hgrow.comp tendsto_natCast_atTop_atTop).eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨X_g, hX_g⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max X₂ X₅) (max X_g 3), fun x hx => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxX₂, hxX₅⟩, hxXg, hx3⟩ := hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hLpos : (0 : ℝ) < Real.log x := Real.log_pos hx1
  set L := Real.log (x : ℝ) with hLdef
  -- the measure input at level z = L
  have hMeasProp := hprop x hxX₂
  have hMeas𝔪 := minor_meas_le hMeasProp
  have hMval_nonneg : (0 : ℝ) ≤ 1 / (x : ℝ) * L ^ (C₄ : ℕ) := by positivity
  have hMbound : (MeasureTheory.volume
      {t : ℝ | t ∈ MinorArc x ∧ Qenergy a b c x t ≤ L}).toReal
      ≤ 1 / (x : ℝ) * L ^ (C₄ : ℕ) :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hMeas𝔪).trans_eq
      (ENNReal.toReal_ofReal hMval_nonneg)
  have hintbound := minor_exp_integral_le a b c x (hfloor x hxX₅) hMbound
  -- rpow conversions
  have hc1 : Real.exp (-(2 * κ₀ * L)) = (x : ℝ) ^ (-(2 * κ₀)) := by
    rw [Real.rpow_def_of_pos hxpos, hLdef]
    ring_nf
  have hc3 : Real.exp (-(2 * L)) = (x : ℝ) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_def_of_pos hxpos, hLdef]
    ring_nf
  calc 2 ^ (Band a b c x).card * (∫ t in MinorArc x, chiBand a b c x t)
      ≤ 2 ^ (Band a b c x).card * (∫ t in MinorArc x, Real.exp (-(2 * Qenergy a b c x t))) :=
        mul_le_mul_of_nonneg_left (integral_chi_le_exp_on_minor a b c x) (by positivity)
    _ ≤ 2 ^ (Band a b c x).card
          * (Real.exp (-(2 * κ₀ * L)) * (1 / (x : ℝ) * L ^ (C₄ : ℕ))
              + Real.exp (-(2 * L))) :=
        mul_le_mul_of_nonneg_left hintbound (by positivity)
    _ < (2 : ℝ) ^ (Band a b c x).card / (C₅ * (x : ℝ) * L) := by
        rw [lt_div_iff₀ (show (0 : ℝ) < C₅ * (x : ℝ) * L by positivity)]
        have hkey := hX_g x hxXg
        have hLpow : L ^ ((1 : ℝ) + C₄) = L ^ (C₄ : ℕ) * L := by
          rw [show ((1 : ℝ) + C₄) = ((C₄ + 1 : ℕ) : ℝ) by push_cast; ring,
            Real.rpow_natCast, pow_succ]
        have heq : (Real.exp (-(2 * κ₀ * L)) * (1 / (x : ℝ) * L ^ (C₄ : ℕ))
              + Real.exp (-(2 * L))) * (C₅ * (x : ℝ) * L)
            = C₅ * Real.log (x : ℝ) ^ ((1 : ℝ) + C₄) * (x : ℝ) ^ (-(2 * κ₀))
              + C₅ * Real.log (x : ℝ) * (x : ℝ) ^ (-(1 : ℝ)) := by
          rw [hc1, hc3, hLpow,
            show (-(1 : ℝ)) = -(2 : ℝ) + 1 by ring, Real.rpow_add hxpos, Real.rpow_one,
            ← hLdef]
          field_simp
        have hgoal : (Real.exp (-(2 * κ₀ * L)) * (1 / (x : ℝ) * L ^ (C₄ : ℕ))
              + Real.exp (-(2 * L))) * (C₅ * (x : ℝ) * L) < 1 := by
          rw [heq]
          simpa using hkey
        have h2pow : (0 : ℝ) < 2 ^ (Band a b c x).card := by positivity
        calc 2 ^ (Band a b c x).card
              * (Real.exp (-(2 * κ₀ * L)) * (1 / (x : ℝ) * L ^ (C₄ : ℕ))
                  + Real.exp (-(2 * L))) * (C₅ * (x : ℝ) * L)
            = 2 ^ (Band a b c x).card
                * ((Real.exp (-(2 * κ₀ * L)) * (1 / (x : ℝ) * L ^ (C₄ : ℕ))
                    + Real.exp (-(2 * L))) * (C₅ * (x : ℝ) * L)) := by ring
          _ < 2 ^ (Band a b c x).card * 1 := by
              exact mul_lt_mul_of_pos_left hgoal h2pow
          _ = (2 : ℝ) ^ (Band a b c x).card := mul_one _

/-- **Short-band coverage** (the unconditional `lclt_coverage`, with the 1/10 window):
every integer in the shrunk central window is a subset sum of the band. -/
theorem lclt_coverage' (a b c : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      100 * (2 * (n : ℤ) - (S1 a b c x : ℤ)) ^ 2 ≤ (S2 a b c x : ℤ) →
      ∃ T : Finset ℕ, T ⊆ Band a b c x ∧ T.sum id = n := by
  obtain ⟨C₅, hC₅, X₃, hmaj⟩ := major_arc_lower' a b c ha hb hc hco
  obtain ⟨X₄, hmin⟩ := minor_arc_bound' a b c ha hb hc hco C₅ hC₅
  refine ⟨max X₃ X₄, fun x hx n hn => ?_⟩
  have hx3 : X₃ ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : X₄ ≤ x := le_trans (le_max_right _ _) hx
  set f : ℝ → ℂ :=
    fun t => (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)) with hf
  have hcont : Continuous f := by
    rw [hf]
    fun_prop
  have hIoc : MeasureTheory.IntegrableOn f (Set.Ioc (0 : ℝ) 1) MeasureTheory.volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hcont.intervalIntegrable 0 1
  have hsub : MajorArc x ⊆ Set.Ioc (0 : ℝ) 1 := fun t ht => ht.1
  have hMmeas : MeasurableSet (MajorArc x) := measurableSet_MajorArc x
  have hsplit : (∫ t in Set.Ioc (0 : ℝ) 1, f t)
      = (∫ t in MajorArc x, f t) + (∫ t in MinorArc x, f t) := by
    rw [MinorArc, ← MeasureTheory.setIntegral_union Set.disjoint_sdiff_right
        (measurableSet_Ioc.diff hMmeas) (hIoc.mono_set hsub) (hIoc.mono_set Set.diff_subset),
      Set.union_diff_cancel hsub]
  have hfourier : (∫ t in (0 : ℝ)..1, f t)
      = (((Band a b c x).powerset.filter (fun T => ∑ s ∈ T, s = n)).card : ℂ) :=
    subsetSum_fourier (Band a b c x) n
  rw [intervalIntegral.integral_of_le (by norm_num), hsplit] at hfourier
  have hRe : (((Band a b c x).powerset.filter (fun T => ∑ s ∈ T, s = n)).card : ℝ)
      = (∫ t in MajorArc x, f t).re + (∫ t in MinorArc x, f t).re := by
    have := congrArg Complex.re hfourier
    simpa [Complex.add_re] using this.symm
  have h1 : (2 : ℝ) ^ (Band a b c x).card / (C₅ * (x : ℝ) * Real.log x)
      ≤ (∫ t in MajorArc x, f t).re := hmaj x hx3 n hn
  have h3 : ‖∫ t in MinorArc x, f t‖
      ≤ 2 ^ (Band a b c x).card * ∫ t in MinorArc x, chiBand a b c x t := by
    rw [hf]
    exact norm_setIntegral_prod_le a b c x n (MinorArc x)
  have h4 : 2 ^ (Band a b c x).card * (∫ t in MinorArc x, chiBand a b c x t)
      < (2 : ℝ) ^ (Band a b c x).card / (C₅ * (x : ℝ) * Real.log x) :=
    hmin x hx4
  have hminre : -(2 ^ (Band a b c x).card * ∫ t in MinorArc x, chiBand a b c x t)
      ≤ (∫ t in MinorArc x, f t).re := by
    have habs : |(∫ t in MinorArc x, f t).re|
        ≤ 2 ^ (Band a b c x).card * ∫ t in MinorArc x, chiBand a b c x t :=
      le_trans (Complex.abs_re_le_norm _) h3
    linarith [abs_le.mp habs |>.1]
  have hpos : (0 : ℝ) < ((Band a b c x).powerset.filter (fun T => ∑ s ∈ T, s = n)).card := by
    rw [hRe]
    linarith
  obtain ⟨T, hT⟩ := Finset.card_pos.mp (by exact_mod_cast hpos)
  rw [Finset.mem_filter, Finset.mem_powerset] at hT
  exact ⟨T, hT.1, by simpa using hT.2⟩

/-- **The sweep with the 1/10 window**: the shrunk central windows still cover a
half-line, because the band count is eventually at least `2500`. -/
theorem sweep' (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (X₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∃ x : ℕ, X₀ ≤ x ∧
      100 * (2 * (n : ℤ) - (S1 a b c x : ℤ)) ^ 2 ≤ (S2 a b c x : ℤ) := by
  classical
  obtain ⟨X₁, hX₁⟩ := band_card_eventually_ge ha hb hc hco 2500
  set X₂ : ℕ := max (max X₀ X₁) 2 with hX₂def
  have hX₂card : ∀ x : ℕ, X₂ ≤ x → 2500 ≤ (Band a b c x).card := fun x hx =>
    hX₁ x (le_trans (le_trans (le_max_right X₀ X₁) (le_max_left _ 2)) hx)
  have hS2of : ∀ x : ℕ, X₂ ≤ x → 2500 * x ^ 2 ≤ S2 a b c x := by
    intro x hx
    have hstep : (Band a b c x).card • (x ^ 2) ≤ (Band a b c x).sum (fun s => s ^ 2) := by
      apply Finset.card_nsmul_le_sum
      intro s hs
      exact Nat.pow_le_pow_left (mem_Band.mp hs).2.1 2
    calc 2500 * x ^ 2 ≤ (Band a b c x).card * x ^ 2 :=
          Nat.mul_le_mul_right _ (hX₂card x hx)
      _ = (Band a b c x).card • (x ^ 2) := (smul_eq_mul _ _).symm
      _ ≤ S2 a b c x := hstep
  refine ⟨S1 a b c X₂ + 1, fun n hn => ?_⟩
  set Q : ℕ → Prop := fun x' => X₂ ≤ x' ∧ S1 a b c x' ≤ 2 * n with hQdef
  have hQ_le : ∀ x', Q x' → x' ≤ 2 * n := by
    intro x' ⟨hx', hs1⟩
    have hcard : 1 ≤ (Band a b c x').card := le_trans (by norm_num) (hX₂card x' hx')
    exact le_trans (le_S1_of_card_pos hcard) hs1
  have hQX₂ : Q X₂ := ⟨le_refl _, by omega⟩
  have hX₂le : X₂ ≤ 2 * n + 1 := le_trans (hQ_le X₂ hQX₂) (by omega)
  set x : ℕ := Nat.findGreatest Q (2 * n + 1) with hxdef
  have hspec : Q x := Nat.findGreatest_spec hX₂le hQX₂
  have hxle : x ≤ 2 * n := hQ_le x hspec
  have hnot : ¬Q (x + 1) :=
    Nat.findGreatest_is_greatest (P := Q) (n := 2 * n + 1) (k := x + 1)
      (by omega) (by omega)
  have hnext : 2 * n < S1 a b c (x + 1) := by
    by_contra hcon
    exact hnot ⟨le_trans hspec.1 (by omega), by omega⟩
  have hstep := S1_step_upper (a := a) (b := b) (c := c) x
  have hS2 := hS2of x hspec.1
  have hx2 : 2 ≤ x := le_trans (le_max_right _ 2) hspec.1
  refine ⟨x, le_trans (le_trans (le_max_left X₀ X₁) (le_max_left _ 2)) hspec.1, ?_⟩
  have h1 : (S1 a b c x : ℤ) ≤ 2 * (n : ℤ) := by exact_mod_cast hspec.2
  have h2 : 2 * (n : ℤ) - (S1 a b c x : ℤ) ≤ 3 * (x : ℤ) + 3 := by
    have hz : (2 * n : ℤ) < (S1 a b c (x + 1) : ℤ) := by exact_mod_cast hnext
    have hcast : (S1 a b c (x + 1) : ℤ) ≤ (S1 a b c x : ℤ) + (3 * (x : ℤ) + 3) := by
      exact_mod_cast hstep
    omega
  have h3 : (2500 : ℤ) * (x : ℤ) ^ 2 ≤ (S2 a b c x : ℤ) := by exact_mod_cast hS2
  have hx2' : (2 : ℤ) ≤ (x : ℤ) := by exact_mod_cast hx2
  have hsq : 2 * (x : ℤ) ≤ (x : ℤ) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (2 * (n : ℤ) - (S1 a b c x : ℤ)), h1, h2, h3, hx2', hsq]

/-- **Erdős Problem #123, unconditional**: for pairwise-coprime `a, b, c > 1` the set
`{a^k b^ℓ c^m}` is d-complete.  Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem erdos123_dcomplete' :
    ∀ a b c : ℕ, 1 < a → 1 < b → 1 < c → PairwiseCoprime3 a b c →
      IsDComplete (Smooth3 a b c) := by
  intro a b c ha hb hc hco
  obtain ⟨X₀, hcov⟩ := lclt_coverage' a b c ha hb hc hco
  obtain ⟨N₀, hsweep⟩ := sweep' ha hb hc hco X₀
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨x, hx, hwin⟩ := hsweep n hn
  obtain ⟨T, hsub, hsum⟩ := hcov x hx n hwin
  refine ⟨T, fun y hy => ?_, (band_primitive x).subset hsub, hsum⟩
  exact (mem_Band.mp (hsub hy)).1

end Erdos123Band

#print axioms Erdos123Band.erdos123_dcomplete'
