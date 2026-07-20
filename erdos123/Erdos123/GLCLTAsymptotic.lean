/-
ERDŐS #123 — THE LOCAL LIMIT LAW, paper eq. (1.1)
=================================================
`Erdos123.GLCLT` proves the COVERAGE half of Theorem 1.1 (`glclt_coverage`).  This file
proves the ASYMPTOTIC half, eq. (1.1):

  P(Y_x = n) = (1/(√(2π)·σ_x))·exp(−(n−μ_x)²/(2σ_x²)) + o(1/σ_x),  UNIFORMLY in n,

where `Y_x = ∑_{s∈B_x} s ξ_s` with iid fair `ξ_s ∈ {0,1}`.  No measure-theoretic
probability is used: `P(Y_x = n)` is the finite ratio `gProb`, and
`gcount_eq_integral` turns it into an exact Fourier integral.

Structure:
  * `gprincipal_two_sided` — a TWO-SIDED analogue of `gprincipal_abstract`, keeping the
    Gaussian main term exact (and dropping the central-window hypothesis `θ² ≤ V²`,
    which is what makes the result uniform in `n`).
  * `gintermediate_raw`, `gminor_raw` — the intermediate/minor range bounds of
    `Erdos123.GTail` restated with their genuine `o(1/V)` right-hand sides instead of
    the fixed `1/(20V)` (which is too weak for an `ε`-statement).
  * `gtail_upper_eps` — the `ε`-version of `gtail_upper`.
  * `glclt_asymptotic` — the theorem.
-/
import Erdos123.GLCLT

set_option maxHeartbeats 1000000

open MeasureTheory

namespace Erdos123Band

noncomputable section

/-! ## The statistics of the band -/

/-- `σ_x = √(S₂)/2`, the standard deviation of `Y_x = ∑_{s ∈ B_x} s ξ_s`. -/
noncomputable def gSigma (a b c p q x : ℕ) : ℝ := Real.sqrt (GS2 a b c p q x) / 2

/-- `μ_x = S₁/2`, the mean of `Y_x`. -/
noncomputable def gMu (a b c p q x : ℕ) : ℝ := (GS1 a b c p q x : ℝ) / 2

/-- `P(Y_x = n)`: the fraction of subsets of the band summing to `n`. -/
noncomputable def gProb (a b c p q x n : ℕ) : ℝ :=
  ((((GBand a b c p q x).powerset.filter (fun T => ∑ s ∈ T, s = n)).card : ℕ) : ℝ)
    / 2 ^ (GBand a b c p q x).card

/-- `gProb` is exactly the Fourier integral (divide `gcount_eq_integral` by `2^{|B|}`). -/
lemma gprob_eq_integral (a b c p q x n : ℕ) :
    gProb a b c p q x n
      = ∫ t in (0 : ℝ)..1, (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) := by
  have hpow : (0 : ℝ) < 2 ^ (GBand a b c p q x).card := by positivity
  rw [gProb, gcount_eq_integral, mul_div_cancel_left₀ _ (ne_of_gt hpow)]

/-! ## The amplitude reconciliation -/

/-- `1/(√(2π)·(V/2)) = √(2/π)/V`. -/
lemma gamp_eq {V : ℝ} (hV : 0 < V) :
    1 / (Real.sqrt (2 * Real.pi) * (V / 2)) = Real.sqrt (2 / Real.pi) / V := by
  have hp : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hm : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  have hd : Real.sqrt (2 / Real.pi) = Real.sqrt 2 / Real.sqrt Real.pi := by
    rw [show (2 : ℝ) / Real.pi = 2 * (Real.pi)⁻¹ by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_inv]
    ring
  have hpne : Real.sqrt Real.pi ≠ 0 := hp.ne'
  have hR : Real.sqrt 2 / Real.sqrt Real.pi * (Real.sqrt 2 * Real.sqrt Real.pi * (V / 2))
      = V := by
    rw [div_mul_eq_mul_div, show Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt Real.pi * (V / 2))
        = (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt Real.pi * (V / 2)) by ring, h22]
    field_simp
  rw [hm, hd, div_eq_div_iff (by positivity) (by positivity)]
  linarith [hR]

/-! ## Step 1 — the two-sided principal-range estimate

`gprincipal_abstract` (Erdos123.GPrincipal) is one-sided and collapses the Gaussian main
term using the central-window hypothesis `θ² ≤ V²`.  Its hypothesis `hb` is already
two-sided and both error terms are explicit, so the following is obtained by the same
proof, keeping the main term exact and DROPPING `hθ` — which is exactly why the resulting
asymptotic is uniform in `n`. -/

/-- **Two-sided principal-range estimate.**  If `φ` is uniformly within `E` of the
Gaussian `exp(−(π²V²/2)t²)` on `[0, T/V]`, then its oscillatory integral there agrees with
the exact half-line Gaussian transform `√(2/π)/V · exp(−θ²/(2V²)) / 2` up to the quartic
error `(T/V)·E` plus the Gaussian tail. -/
lemma gprincipal_two_sided {φ : ℝ → ℝ} {V θ T E : ℝ}
    (hφ : Continuous φ) (hV : 0 < V) (hT : 0 < T)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) (T / V),
      |φ t - Real.exp (-(Real.pi ^ 2 * V ^ 2 / 2 * t ^ 2))| ≤ E) :
    |(∫ t in (0 : ℝ)..(T / V), φ t * Real.cos (Real.pi * θ * t))
        - Real.sqrt (2 / Real.pi) / V * Real.exp (-(θ ^ 2 / (2 * V ^ 2))) / 2|
      ≤ (T / V) * E + 2 * Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) / (Real.pi ^ 2 * V * T) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hVne : V ≠ 0 := hV.ne'
  have hTne : T ≠ 0 := hT.ne'
  set A : ℝ := Real.pi ^ 2 * V ^ 2 / 2 with hAdef
  have hA : 0 < A := by
    rw [hAdef]; exact div_pos (mul_pos (pow_pos hpi 2) (pow_pos hV 2)) two_pos
  set t₁ : ℝ := T / V with ht₁def
  have ht₁ : 0 < t₁ := div_pos hT hV
  have hcosC : Continuous (fun t : ℝ => Real.cos (Real.pi * θ * t)) := by fun_prop
  have hexpC : Continuous (fun t : ℝ => Real.exp (-(A * t ^ 2))) := by fun_prop
  have hgint : Integrable
      (fun u : ℝ => Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u)) :=
    gaussian_integrable_scaled hA (Real.pi * θ)
  have hb2 : (∫ t in (0 : ℝ)..t₁, Real.exp (-(A * t ^ 2)) * Real.cos (Real.pi * θ * t))
      = (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u))
        - ∫ u in Set.Ioi t₁, Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u) :=
    (intervalIntegral.integral_Ioi_sub_Ioi hgint.integrableOn ht₁.le).symm
  have hsqrt : Real.sqrt (Real.pi / A) = Real.sqrt (2 / Real.pi) / V := by
    have hnn : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) / V := div_nonneg (Real.sqrt_nonneg _) hV.le
    have hkey : Real.pi / A = (Real.sqrt (2 / Real.pi) / V) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity), hAdef]
      field_simp
    rw [hkey, Real.sqrt_sq hnn]
  have hquot : (Real.pi * θ) ^ 2 / (4 * A) = θ ^ 2 / (2 * V ^ 2) := by
    rw [hAdef]; field_simp; ring
  have hmainEq : (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u))
      = Real.sqrt (2 / Real.pi) / V * Real.exp (-(θ ^ 2 / (2 * V ^ 2))) / 2 := by
    rw [gauss_half_line hA (Real.pi * θ), hsqrt, hquot]
  -- the Gaussian tail
  have htail : |∫ u in Set.Ioi t₁, Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u)|
      ≤ 2 * Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) / (Real.pi ^ 2 * V * T) := by
    have h := gauss_osc_tail_Ioi (A := A) (T := t₁) hA ht₁ (Real.pi * θ)
    have e1 : A * t₁ ^ 2 = Real.pi ^ 2 * T ^ 2 / 2 := by
      rw [hAdef, ht₁def]; field_simp
    have e2 : A * t₁ = Real.pi ^ 2 * V * T / 2 := by
      rw [hAdef, ht₁def]; field_simp
    rw [e1, e2] at h
    refine h.trans (le_of_eq ?_)
    field_simp
  -- the quartic error
  have hIg : IntervalIntegrable
      (fun u : ℝ => Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u)) volume 0 t₁ :=
    (hexpC.mul hcosC).intervalIntegrable _ _
  have hIF : IntervalIntegrable
      (fun t => (φ t - Real.exp (-(A * t ^ 2))) * Real.cos (Real.pi * θ * t))
      volume 0 t₁ := ((hφ.sub hexpC).mul hcosC).intervalIntegrable _ _
  have hsplit : (∫ t in (0 : ℝ)..t₁, φ t * Real.cos (Real.pi * θ * t))
      = (∫ t in (0 : ℝ)..t₁, Real.exp (-(A * t ^ 2)) * Real.cos (Real.pi * θ * t))
        + ∫ t in (0 : ℝ)..t₁, (φ t - Real.exp (-(A * t ^ 2))) * Real.cos (Real.pi * θ * t) := by
    rw [← intervalIntegral.integral_add hIg hIF]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  have herr : |∫ t in (0 : ℝ)..t₁, (φ t - Real.exp (-(A * t ^ 2)))
      * Real.cos (Real.pi * θ * t)| ≤ t₁ * E := by
    have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
      (f := fun t => (φ t - Real.exp (-(A * t ^ 2))) * Real.cos (Real.pi * θ * t)) ht₁.le
    have h2 : (∫ t in (0 : ℝ)..t₁, |(φ t - Real.exp (-(A * t ^ 2)))
        * Real.cos (Real.pi * θ * t)|) ≤ ∫ _t in (0 : ℝ)..t₁, E := by
      refine intervalIntegral.integral_mono_on ht₁.le hIF.abs
        intervalIntegrable_const (fun t ht => ?_)
      rw [abs_mul]
      have hc : |Real.cos (Real.pi * θ * t)| ≤ 1 := Real.abs_cos_le_one _
      have hd : |φ t - Real.exp (-(A * t ^ 2))| ≤ E := hb t ⟨ht.1, ht.2⟩
      nlinarith [abs_nonneg (φ t - Real.exp (-(A * t ^ 2))),
        abs_nonneg (Real.cos (Real.pi * θ * t))]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h2
    linarith
  have heq : (∫ t in (0 : ℝ)..t₁, φ t * Real.cos (Real.pi * θ * t))
      = Real.sqrt (2 / Real.pi) / V * Real.exp (-(θ ^ 2 / (2 * V ^ 2))) / 2
        - (∫ u in Set.Ioi t₁, Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u))
        + ∫ t in (0 : ℝ)..t₁, (φ t - Real.exp (-(A * t ^ 2)))
            * Real.cos (Real.pi * θ * t) := by
    rw [hsplit, hb2, hmainEq]
  have hA1 := abs_le.mp herr
  have hA2 := abs_le.mp htail
  rw [heq, abs_le]
  constructor
  · linarith [hA1.1, hA2.2]
  · linarith [hA1.2, hA2.1]

/-! ## Step 2 — the intermediate and minor ranges with their genuine `o(1/V)` bounds

`gintermediate_upper` and `gminor_upper` (Erdos123.GTail) each conclude `≤ 1/(20V)`, a
FIXED multiple of `1/V`, which is not small enough for an `ε`-statement.  Their internals
are genuinely `o(1/V)`; the two lemmas below are the same proofs stopped one step earlier,
so that the true right-hand side (`exp(−2T²)/(2VT)` resp.
`x^{−2κ₀}L^{C₄}/x + x^{−2}`) is exposed. -/

/-- **INTERMEDIATE RANGE, raw bound.**  As `gintermediate_upper`, but concluding with the
true Gaussian tail `exp(−2T²)/(2VT)` instead of `1/(20V)`. -/
lemma gintermediate_raw (a b c p q : ℕ) (hq : 0 < q) (hpd : p < q * min a (min b c))
    {δ : ℝ} (hδd : δ * ((min a (min b c) : ℕ) : ℝ) ≤ 1 / 8)
    (x : ℕ) (hx : 0 < x) {F : ℝ → ℝ} (hFcont : Continuous F)
    (hFabs : ∀ t : ℝ, |F t| ≤ Real.exp (-(2 * GQenergy a b c p q x t)))
    (hVpos : 0 < Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ))
    (hT2 : (2 : ℝ) ≤ gT x)
    (h12 : gt₁ a b c p q x ≤ 2 * δ / (x : ℝ)) :
    |∫ t in (gt₁ a b c p q x)..(2 * δ / (x : ℝ)), F t|
      ≤ Real.exp (-(2 * gT x ^ 2))
          / (2 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) * gT x) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  set V : ℝ := Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) with hVdef
  have hVne : V ≠ 0 := ne_of_gt hVpos
  have hV2 : V ^ 2 = ((GS2 a b c p q x : ℕ) : ℝ) := by
    rw [hVdef]; exact Real.sq_sqrt (by positivity)
  set T : ℝ := gT x with hTdef
  have hTpos : (0 : ℝ) < T := by linarith
  set t₁ : ℝ := gt₁ a b c p q x with ht₁def
  have ht₁eq : t₁ = T / V := by rw [ht₁def, hTdef, hVdef, gt₁]
  have ht₁pos : 0 < t₁ := by rw [ht₁eq]; positivity
  set t₂ : ℝ := 2 * δ / (x : ℝ) with ht₂def
  have hFabsInt : ∀ u v : ℝ, IntervalIntegrable (fun t => |F t|) volume u v :=
    fun u v => (hFcont.abs).intervalIntegrable u v
  set A : ℝ := 2 * ((GS2 a b c p q x : ℕ) : ℝ) with hAdef
  have hApos : 0 < A := by rw [hAdef]; nlinarith [hV2, hVpos]
  have hgi : MeasureTheory.Integrable (fun u : ℝ => Real.exp (-(A * u ^ 2))) := by
    have := gaussian_integrable_scaled hApos 0
    simpa using this
  have hstep1 : |∫ t in t₁..t₂, F t| ≤ ∫ t in t₁..t₂, |F t| := by
    have := intervalIntegral.norm_integral_le_integral_norm (f := F) (μ := volume) h12
    simpa only [Real.norm_eq_abs] using this
  have hstep2 : (∫ t in t₁..t₂, |F t|) ≤ ∫ t in t₁..t₂, Real.exp (-(A * t ^ 2)) := by
    refine intervalIntegral.integral_mono_on h12 (hFabsInt t₁ t₂)
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(A * t ^ 2))).intervalIntegrable _ _)
      (fun t ht => ?_)
    have htpos : 0 ≤ t := le_trans ht₁pos.le ht.1
    have hQ : GQenergy a b c p q x t = ((GS2 a b c p q x : ℕ) : ℝ) * t ^ 2 := by
      refine gQenergy_eq_of_small hq hpd htpos ?_
      have hdx0 : (0 : ℝ) ≤ ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) := by positivity
      have h1 : ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) * t
          ≤ ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) * t₂ := by nlinarith [ht.2]
      have h2 : ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) * t₂
          = ((min a (min b c) : ℕ) : ℝ) * (2 * δ) := by
        rw [ht₂def]; field_simp
      nlinarith [h1, h2, hδd]
    calc |F t| ≤ Real.exp (-(2 * GQenergy a b c p q x t)) := hFabs t
      _ = Real.exp (-(A * t ^ 2)) := by rw [hQ, hAdef]; congr 1; ring
  have hstep3 : (∫ t in t₁..t₂, Real.exp (-(A * t ^ 2)))
      ≤ ∫ t in Set.Ioi t₁, Real.exp (-(A * t ^ 2)) := by
    rw [intervalIntegral.integral_of_le h12]
    refine MeasureTheory.setIntegral_mono_set hgi.integrableOn ?_
      (HasSubset.Subset.eventuallyLE Set.Ioc_subset_Ioi_self)
    filter_upwards with t using Real.exp_nonneg _
  have hstep4 := gauss_tail_Ioi hApos ht₁pos
  have hAt1 : A * t₁ ^ 2 = 2 * T ^ 2 := by rw [hAdef, ht₁eq, ← hV2]; field_simp
  have hAt1' : A * t₁ = 2 * V * T := by rw [hAdef, ht₁eq, ← hV2]; field_simp
  rw [hAt1, hAt1'] at hstep4
  linarith [hstep1, hstep2, hstep3, hstep4]

/-- **MINOR RANGE, raw bound.**  As `gminor_upper`, but concluding with the true layer-split
bound `x^{−2κ₀}·L^{C₄}/x + x^{−2}` instead of `1/(20V)`. -/
lemma gminor_raw (a b c p q : ℕ) {κ₀ δ : ℝ} {C₄ : ℕ} (x : ℕ) (hx1 : 1 ≤ x)
    (hδ : 0 < δ) (hδ16 : δ ≤ 1 / 16) (hL1 : (1 : ℝ) ≤ Real.log x)
    {F : ℝ → ℝ} (hFcont : Continuous F)
    (hFabs : ∀ t : ℝ, |F t| ≤ Real.exp (-(2 * GQenergy a b c p q x t)))
    (hvl : ∀ t : ℝ, GQenergy a b c p q x t < κ₀ * Real.log x →
      ∃ r : ℤ, |t - (r : ℝ)| ≤ δ / (x : ℝ))
    (hmeasx : volume {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ Real.log x}
      ≤ ENNReal.ofReal (1 / (x : ℝ) * Real.log x ^ C₄)) :
    |∫ t in (2 * δ / (x : ℝ))..(1 / 2), F t|
      ≤ Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
        + Real.exp (-(2 * Real.log x)) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  set t₂ : ℝ := 2 * δ / (x : ℝ) with ht₂def
  have ht₂pos : 0 < t₂ := by rw [ht₂def]; positivity
  have ht₂half : t₂ ≤ 1 / 2 := by
    rw [ht₂def, div_le_iff₀ hxpos]; nlinarith [hδ16, hx1R]
  have hstep1 : |∫ t in t₂..(1 / 2), F t| ≤ ∫ t in t₂..(1 / 2), |F t| := by
    have := intervalIntegral.norm_integral_le_integral_norm (f := F) (μ := volume) ht₂half
    simpa only [Real.norm_eq_abs] using this
  have hstep2 : (∫ t in t₂..(1 / 2), |F t|)
      ≤ ∫ t in t₂..(1 / 2), Real.exp (-(2 * GQenergy a b c p q x t)) :=
    intervalIntegral.integral_mono_on ht₂half ((hFcont.abs).intervalIntegrable _ _)
      (gexp_neg_two_Q_intervalIntegrable a b c p q x t₂ (1 / 2)) (fun t _ => hFabs t)
  have hdx : δ / (x : ℝ) ≤ 1 / 16 := by
    rw [div_le_iff₀ hxpos]; nlinarith [hδ16, hx1R]
  have hfloor : ∀ t ∈ Set.Ioc t₂ (1 / 2 : ℝ), κ₀ * Real.log x ≤ GQenergy a b c p q x t := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, hr⟩ := hvl t hcon
    have htpos : 0 < t := lt_trans ht₂pos ht.1
    have hhalf : δ / (x : ℝ) < t₂ := by
      have heq : t₂ - δ / (x : ℝ) = δ / (x : ℝ) := by rw [ht₂def]; field_simp; norm_num
      have hpos : 0 < δ / (x : ℝ) := div_pos hδ hxpos
      linarith
    have hcontr : δ / (x : ℝ) < |t - (r : ℝ)| := by
      rcases le_or_gt 1 r with h | h
      · have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.2, hdx]
      · rcases le_or_gt r (-1) with h' | h'
        · have hrR : ((r : ℤ) : ℝ) ≤ -1 := by exact_mod_cast h'
          rw [abs_of_nonneg (by linarith)]
          linarith [hdx]
        · have hr0 : r = 0 := by omega
          subst hr0
          rw [Int.cast_zero, sub_zero, abs_of_pos htpos]
          linarith [ht.1, hhalf]
    linarith [hr, hcontr]
  have hSsub : Set.Ioc t₂ (1 / 2 : ℝ) ⊆ Set.Ioc (0 : ℝ) 1 :=
    fun t ht => ⟨lt_trans ht₂pos ht.1, by linarith [ht.2]⟩
  have hmeasS : (volume {t : ℝ | t ∈ Set.Ioc t₂ (1 / 2 : ℝ) ∧
      GQenergy a b c p q x t ≤ Real.log x}).toReal ≤ 1 / (x : ℝ) * Real.log x ^ C₄ := by
    have hsub : {t : ℝ | t ∈ Set.Ioc t₂ (1 / 2 : ℝ) ∧ GQenergy a b c p q x t ≤ Real.log x}
        ⊆ {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ Real.log x} := by
      rintro t ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith [ht₂pos], by linarith⟩, h3⟩
    have hle := (measure_mono hsub).trans hmeasx
    have hnn : (0 : ℝ) ≤ 1 / (x : ℝ) * Real.log x ^ C₄ :=
      mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq (ENNReal.toReal_ofReal hnn)
  have hmain := gexp_integral_le_on a b c p q x measurableSet_Ioc hSsub hfloor hmeasS
  rw [← intervalIntegral.integral_of_le ht₂half] at hmain
  linarith [hstep1, hstep2, hmain]

/-! ## Step 3 — the `ε`-version of `gtail_upper` -/

/-- **The intermediate + minor ranges are `o(1/V)`, uniformly in `n`.**  The `ε`-strengthening
of `gtail_upper` (which gives only the fixed bound `1/(10V)`). -/
theorem gtail_upper_eps (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      |∫ t in (gt₁ a b c p q x)..(1 / 2),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))|
        ≤ ε / Real.sqrt (GS2 a b c p q x) := by
  classical
  obtain ⟨κ₀, δ, X₅, hκ₀, hδ, hδd, hvl⟩ := gvery_low_sharp a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨C₄, hC₄, X₂, hmeasx⟩ := glow_energy_measure a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨CV, hCV, X₆, hVup⟩ := gV_upper a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨cV, hcV, X₇, hVlow⟩ := gV_lower a b c p q ha hb hc hco hq hqp hpd
  have hd2 : 2 ≤ min a (min b c) := by simp only [le_min_iff]; omega
  have hdR2 : (2 : ℝ) ≤ ((min a (min b c) : ℕ) : ℝ) := by exact_mod_cast hd2
  have hδ16 : δ ≤ 1 / 16 := by nlinarith [hδd, hdR2, hδ]
  have hlogtop : Filter.Tendsto (fun x : ℕ => Real.log x) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Xa, hXa⟩ := Filter.eventually_atTop.mp
    (hlogtop.eventually_ge_atTop (max 16 ((1 / (2 * δ * cV)) ^ 2)))
  have hgrow : Filter.Tendsto
      (fun y : ℝ => 2 * CV * Real.log y ^ ((1 : ℝ) + (C₄ : ℝ)) * y ^ (-(2 * κ₀))
        + 2 * CV * Real.log y * y ^ (-(1 : ℝ))) Filter.atTop (nhds 0) := by
    have h1 := poly_log_rpow_tendsto (p := (1 : ℝ) + (C₄ : ℝ)) (q := 2 * κ₀) (by linarith)
    have h2 := poly_log_rpow_tendsto (p := (1 : ℝ)) (q := (1 : ℝ)) (by norm_num)
    have hsum := (h1.const_mul (2 * CV)).add (h2.const_mul (2 * CV))
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr (fun y => ?_)
    rw [Real.rpow_one]
    ring
  obtain ⟨Xb, hXb⟩ := Filter.eventually_atTop.mp
    ((hgrow.comp tendsto_natCast_atTop_atTop).eventually_lt_const hε)
  obtain ⟨Xc, hXc⟩ := gT_eventually_ge (2 + 1 / ε)
  refine ⟨max (max (max X₅ X₂) (max X₆ X₇)) (max (max Xa Xb) (max Xc 2)), fun x hx n => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hxX₅, hxX₂⟩, hxX₆, hxX₇⟩, ⟨hxXa, hxXb⟩, hxXc, hx2⟩ := hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hLbig := hXa x hxXa
  rw [max_le_iff] at hLbig
  obtain ⟨hL16, hLB⟩ := hLbig
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hVge : cV * (x : ℝ) * Real.log x ≤ Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) :=
    hVlow x hxX₇
  have hVpos : 0 < Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) :=
    lt_of_lt_of_le (mul_pos (mul_pos hcV hxpos) hLpos) hVge
  have hVle : Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) ≤ CV * (x : ℝ) * Real.log x :=
    hVup x hxX₆
  set V : ℝ := Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) with hVdef
  -- `T = (log x)^{1/4}` is large
  have hTM : 2 + 1 / ε ≤ gT x := hXc x hxXc
  have hepos : (0 : ℝ) < 1 / ε := by positivity
  have hT2 : (2 : ℝ) ≤ gT x := by linarith
  have hTe : 1 / ε ≤ gT x := by linarith
  set T : ℝ := gT x with hTdef
  have hTpos : (0 : ℝ) < T := by linarith
  have hsq16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsq4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsL4 : (4 : ℝ) ≤ Real.sqrt (Real.log x) := by
    have h := Real.sqrt_le_sqrt hL16; rwa [hsq16] at h
  have hTle : T ≤ Real.sqrt (Real.log x) := by
    rw [hTdef]; unfold gT
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg (Real.log x)),
      Real.sqrt_nonneg (Real.sqrt (Real.log x)), hsL4,
      sq_nonneg (Real.sqrt (Real.sqrt (Real.log x)) - 2)]
  -- `t₁ ≤ t₂ = 2δ/x`
  have h12 : gt₁ a b c p q x ≤ 2 * δ / (x : ℝ) := by
    have hp : (0 : ℝ) < 2 * δ * cV := by positivity
    have hkey : 1 / (2 * δ * cV) ≤ Real.sqrt (Real.log x) := by
      have h := Real.sqrt_le_sqrt hLB
      rwa [Real.sqrt_sq (by positivity)] at h
    have h3 : 1 ≤ 2 * δ * cV * Real.sqrt (Real.log x) := by
      rw [div_le_iff₀ hp] at hkey; linarith
    have hself : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
      Real.mul_self_sqrt hLpos.le
    have h4 : Real.sqrt (Real.log x) ≤ 2 * δ * cV * Real.log x := by
      nlinarith [h3, Real.sqrt_nonneg (Real.log x), hself]
    unfold gt₁
    rw [← hTdef, ← hVdef, div_le_div_iff₀ hVpos hxpos]
    nlinarith [mul_le_mul_of_nonneg_right (hTle.trans h4) hxpos.le,
      mul_le_mul_of_nonneg_left hVge (show (0 : ℝ) ≤ 2 * δ by linarith)]
  -- (A) the intermediate range is `≤ ε/(2V)`
  have hAraw := gintermediate_raw a b c p q hq hpd hδd x (by omega)
    (gintegrand_continuous a b c p q x n) (gintegrand_abs_le a b c p q x n) hVpos hT2 h12
  rw [← hTdef, ← hVdef] at hAraw
  have hAeps : Real.exp (-(2 * T ^ 2)) / (2 * V * T) ≤ ε / (2 * V) := by
    have hexp : Real.exp (-(2 * T ^ 2)) ≤ 1 / (2 * T ^ 2) := by
      have h1 : 2 * T ^ 2 ≤ Real.exp (2 * T ^ 2) := by
        linarith [Real.add_one_le_exp (2 * T ^ 2)]
      have h2 : (2 * T ^ 2) * Real.exp (-(2 * T ^ 2)) ≤ 1 := by
        have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg (-(2 * T ^ 2)))
        rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h3
      rw [le_div_iff₀ (by positivity)]
      linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hkey : Real.exp (-(2 * T ^ 2)) ≤ ε * T := by
      have hb1 : 1 ≤ ε * T := by
        rw [div_le_iff₀ hε] at hTe; linarith
      have hT2sq : (4 : ℝ) ≤ T ^ 2 := by nlinarith [hT2, hTpos]
      have hb2 : 1 / (2 * T ^ 2) ≤ ε * T := by
        rw [div_le_iff₀ (by positivity)]
        have hmul : 1 * T ^ 2 ≤ (ε * T) * T ^ 2 :=
          mul_le_mul_of_nonneg_right hb1 (sq_nonneg T)
        nlinarith [hmul, hT2sq]
      linarith
    calc Real.exp (-(2 * T ^ 2)) * (2 * V)
        ≤ (ε * T) * (2 * V) := mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = ε * (2 * V * T) := by ring
  -- (B) the minor range is `≤ ε/(2V)`
  have hBraw := gminor_raw a b c p q x (by omega) hδ hδ16 hL1
    (gintegrand_continuous a b c p q x n) (gintegrand_abs_le a b c p q x n)
    (hvl x hxX₅) (hmeasx x hxX₂)
  have h2V : (0 : ℝ) < 2 * V := by linarith
  have hBeps : Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
      + Real.exp (-(2 * Real.log x)) ≤ ε / (2 * V) := by
    have hEnn : (0 : ℝ) ≤ Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
        + Real.exp (-(2 * Real.log x)) :=
      add_nonneg (mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))) (Real.exp_nonneg _)
    have hc1 : Real.exp (-(2 * κ₀ * Real.log x)) = (x : ℝ) ^ (-(2 * κ₀)) := by
      rw [Real.rpow_def_of_pos hxpos]; ring_nf
    have hc3 : Real.exp (-(2 * Real.log x)) = (x : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_def_of_pos hxpos]; ring_nf
    have hLpow : Real.log (x : ℝ) ^ ((1 : ℝ) + (C₄ : ℝ))
        = Real.log (x : ℝ) ^ C₄ * Real.log x := by
      rw [show ((1 : ℝ) + (C₄ : ℝ)) = ((C₄ + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, pow_succ]
    have hkey := hXb x hxXb
    simp only [Function.comp_apply] at hkey
    rw [le_div_iff₀ h2V]
    have heq : (Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
          + Real.exp (-(2 * Real.log x))) * (2 * CV * (x : ℝ) * Real.log x)
        = 2 * CV * Real.log (x : ℝ) ^ ((1 : ℝ) + (C₄ : ℝ)) * (x : ℝ) ^ (-(2 * κ₀))
          + 2 * CV * Real.log (x : ℝ) * (x : ℝ) ^ (-(1 : ℝ)) := by
      rw [hc1, hc3, hLpow,
        show (-(1 : ℝ)) = -(2 : ℝ) + 1 by ring, Real.rpow_add hxpos, Real.rpow_one]
      field_simp
    have hmono : (Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
          + Real.exp (-(2 * Real.log x))) * (2 * V)
        ≤ (Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
          + Real.exp (-(2 * Real.log x))) * (2 * CV * (x : ℝ) * Real.log x) := by
      refine mul_le_mul_of_nonneg_left ?_ hEnn
      linarith
    rw [heq] at hmono
    linarith [hmono, hkey]
  -- assemble
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((gintegrand_continuous a b c p q x n).intervalIntegrable (μ := volume)
      (gt₁ a b c p q x) (2 * δ / (x : ℝ)))
    ((gintegrand_continuous a b c p q x n).intervalIntegrable (μ := volume)
      (2 * δ / (x : ℝ)) (1 / 2))
  rw [← hsplit]
  refine le_trans (abs_add_le _ _) ?_
  have hsum : ε / (2 * V) + ε / (2 * V) = ε / V := by field_simp; ring
  linarith [hAraw.trans hAeps, hBraw.trans hBeps, hsum]

/-! ## Step 4 — the local limit law -/

/-- **Local central limit theorem, paper eq. (1.1)**, uniformly in `n`.

`P(Y_x = n) = (1/(√(2π)σ_x))·exp(−(n−μ_x)²/(2σ_x²)) + o(1/σ_x)` uniformly in `n ∈ ℤ`:
the quantifier order `∀ ε > 0, ∃ X₀, ∀ x ≥ X₀, ∀ n` IS the uniformity in `n`. -/
theorem glclt_asymptotic (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      |gProb a b c p q x n
         - (1 / (Real.sqrt (2 * Real.pi) * gSigma a b c p q x))
             * Real.exp (-(((n : ℝ) - gMu a b c p q x) ^ 2
                 / (2 * gSigma a b c p q x ^ 2)))|
        ≤ ε / gSigma a b c p q x := by
  classical
  intro ε hε
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi9 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2, Real.pi_pos]
  have hpi81 : (81 : ℝ) ≤ Real.pi ^ 4 := by nlinarith [hpi9]
  obtain ⟨cV, hcV, X₁, hX₁⟩ := gV_lower a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨Xt, hXt⟩ := gtail_upper_eps a b c p q ha hb hc hco hq hqp hpd (ε / 3) (by linarith)
  set M : ℝ := 5 + 1 / ε + Real.pi * p / cV + 3 * Real.pi ^ 4 * (p : ℝ) ^ 2 / (ε * cV ^ 2)
    with hMdef
  obtain ⟨X₂, hX₂⟩ := gT_eventually_ge M
  refine ⟨max (max X₁ X₂) (max Xt 2), fun x hx n => ?_⟩
  have hxX₁ : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxX₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxXt : Xt ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  set T : ℝ := gT x with hTdef
  set V : ℝ := Real.sqrt (GS2 a b c p q x) with hVdef
  set L : ℝ := Real.log x with hLdef
  have hTM : M ≤ T := hX₂ x hxX₂
  have hMnn0 : (0 : ℝ) < 1 / ε := by positivity
  have hMnn1 : (0 : ℝ) ≤ Real.pi * p / cV := div_nonneg (by positivity) hcV.le
  have hMnn2 : (0 : ℝ) ≤ 3 * Real.pi ^ 4 * (p : ℝ) ^ 2 / (ε * cV ^ 2) := by positivity
  have hT5 : (5 : ℝ) ≤ T := by rw [hMdef] at hTM; linarith
  have hTe : 1 / ε ≤ T := by rw [hMdef] at hTM; linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hxR : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hLpos : (0 : ℝ) < L := by
    rw [hLdef]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hxR
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hT4 : T ^ 4 = L := gT_pow_four (by omega)
  have hVlow : cV * (x : ℝ) * L ≤ V := hX₁ x hxX₁
  have hWpos : (0 : ℝ) < cV * (x : ℝ) * L := mul_pos (mul_pos hcV hxpos) hLpos
  have hVpos : (0 : ℝ) < V := lt_of_lt_of_le hWpos hVlow
  have hVne : V ≠ 0 := hVpos.ne'
  have hS2eq : ((GS2 a b c p q x : ℕ) : ℝ) = V ^ 2 := by
    rw [hVdef, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hT3 : T ≤ T ^ 3 := by
    have h1 : (1 : ℝ) ≤ T := by linarith
    have h2 : (1 : ℝ) ≤ T ^ 2 := by nlinarith [h1]
    calc T = T * 1 := (mul_one T).symm
      _ ≤ T * T ^ 2 := mul_le_mul_of_nonneg_left h2 hTpos.le
      _ = T ^ 3 := by ring
  have hb1 : 1 ≤ ε * T := by rw [div_le_iff₀ hε] at hTe; linarith
  have hcube1 : Real.pi * (p : ℝ) ≤ cV * T ^ 3 := by
    have h1 : Real.pi * (p : ℝ) / cV ≤ T := by rw [hMdef] at hTM; linarith
    have h2 : Real.pi * (p : ℝ) ≤ cV * T := by rw [div_le_iff₀ hcV] at h1; linarith
    calc Real.pi * (p : ℝ) ≤ cV * T := h2
      _ ≤ cV * T ^ 3 := mul_le_mul_of_nonneg_left hT3 hcV.le
  have hcube2 : 3 * Real.pi ^ 4 * (p : ℝ) ^ 2 ≤ ε * cV ^ 2 * T ^ 3 := by
    have h1 : 3 * Real.pi ^ 4 * (p : ℝ) ^ 2 / (ε * cV ^ 2) ≤ T := by
      rw [hMdef] at hTM; linarith
    have h2 : 3 * Real.pi ^ 4 * (p : ℝ) ^ 2 ≤ ε * cV ^ 2 * T := by
      rw [div_le_iff₀ (by positivity)] at h1; linarith
    calc 3 * Real.pi ^ 4 * (p : ℝ) ^ 2 ≤ ε * cV ^ 2 * T := h2
      _ ≤ ε * cV ^ 2 * T ^ 3 := mul_le_mul_of_nonneg_left hT3 (by positivity)
  -- smallness on the principal range
  have hsmall : ∀ t : ℝ, 0 ≤ t → t ≤ T / V → ∀ s ∈ GBand a b c p q x,
      |Real.pi * ((s : ℝ) * t)| ≤ 1 := by
    intro t ht0 htt s hs
    have hsle : (s : ℝ) ≤ (p : ℝ) * (x : ℝ) := by exact_mod_cast gband_le hq hs
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    rw [abs_of_nonneg (mul_nonneg hpi.le (mul_nonneg hs0 ht0))]
    have hkey : Real.pi * ((p : ℝ) * (x : ℝ)) * T ≤ V := by
      have h1 : Real.pi * ((p : ℝ) * (x : ℝ)) * T ≤ cV * (x : ℝ) * L := by
        rw [← hT4]
        nlinarith [mul_le_mul_of_nonneg_right hcube1 (mul_nonneg hxpos.le hTpos.le)]
      linarith
    have h3 : Real.pi * ((p : ℝ) * (x : ℝ)) * (T / V) ≤ 1 := by
      rw [show Real.pi * ((p : ℝ) * (x : ℝ)) * (T / V)
          = (Real.pi * ((p : ℝ) * (x : ℝ)) * T) / V by ring, div_le_one hVpos]
      exact hkey
    have h2 : (s : ℝ) * t ≤ ((p : ℝ) * (x : ℝ)) * (T / V) :=
      mul_le_mul hsle htt ht0 (by positivity)
    calc Real.pi * ((s : ℝ) * t)
        ≤ Real.pi * (((p : ℝ) * (x : ℝ)) * (T / V)) := mul_le_mul_of_nonneg_left h2 hpi.le
      _ ≤ 1 := by linarith [h3]
  -- the uniform Gaussian error on the principal range
  set E : ℝ := Real.pi ^ 4 * (T / V) ^ 4
      * (((p : ℝ) * (x : ℝ)) ^ 2 * ((GS2 a b c p q x : ℕ) : ℝ)) with hEdef
  have hEnn : (0 : ℝ) ≤ E := by rw [hEdef]; positivity
  have hbnd : ∀ t ∈ Set.Icc (0 : ℝ) (T / V),
      |(∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
        - Real.exp (-(Real.pi ^ 2 * V ^ 2 / 2 * t ^ 2))| ≤ E := by
    intro t ht
    obtain ⟨ht0, htt⟩ := ht
    have happ : |(∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
          - Real.exp (-((∑ s ∈ GBand a b c p q x, (Real.pi * ((s : ℝ) * t)) ^ 2) / 2))|
        ≤ ∑ s ∈ GBand a b c p q x, (Real.pi * ((s : ℝ) * t)) ^ 4 :=
      abs_prod_cos_sub_exp_le (GBand a b c p q x)
        (fun s => Real.pi * ((s : ℝ) * t)) (fun s hs => hsmall t ht0 htt s hs)
    have hsum2 : (∑ s ∈ GBand a b c p q x, (Real.pi * ((s : ℝ) * t)) ^ 2)
        = Real.pi ^ 2 * (((GS2 a b c p q x : ℕ) : ℝ) * t ^ 2) := by
      rw [← gsum_sq_band a b c p q x t, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    have hexpeq : -((∑ s ∈ GBand a b c p q x, (Real.pi * ((s : ℝ) * t)) ^ 2) / 2)
        = -(Real.pi ^ 2 * V ^ 2 / 2 * t ^ 2) := by rw [hsum2, hS2eq]; ring
    rw [hexpeq] at happ
    refine happ.trans ?_
    have hsum4 : (∑ s ∈ GBand a b c p q x, (Real.pi * ((s : ℝ) * t)) ^ 4)
        = Real.pi ^ 4 * t ^ 4 * (∑ s ∈ GBand a b c p q x, (s : ℝ) ^ 4) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    have h4 : (∑ s ∈ GBand a b c p q x, (s : ℝ) ^ 4)
        ≤ ((p : ℝ) * (x : ℝ)) ^ 2 * ((GS2 a b c p q x : ℕ) : ℝ) := gS4_le hq x
    have ht4 : t ^ 4 ≤ (T / V) ^ 4 := pow_le_pow_left₀ ht0 htt 4
    rw [hsum4, hEdef]
    calc Real.pi ^ 4 * t ^ 4 * (∑ s ∈ GBand a b c p q x, (s : ℝ) ^ 4)
        ≤ Real.pi ^ 4 * t ^ 4 * (((p : ℝ) * (x : ℝ)) ^ 2 * ((GS2 a b c p q x : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ Real.pi ^ 4 * (T / V) ^ 4
            * (((p : ℝ) * (x : ℝ)) ^ 2 * ((GS2 a b c p q x : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left ht4 (by positivity)) (by positivity)
  -- the scale `W = ε / V`
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ε / V := ⟨_, rfl⟩
  -- the quartic error is `≤ W/3`
  have hkey2 : 3 * (Real.pi ^ 4 * T ^ 5 * ((p : ℝ) * (x : ℝ)) ^ 2) ≤ ε * V ^ 2 := by
    calc 3 * (Real.pi ^ 4 * T ^ 5 * ((p : ℝ) * (x : ℝ)) ^ 2)
        = (3 * Real.pi ^ 4 * (p : ℝ) ^ 2) * (T ^ 5 * (x : ℝ) ^ 2) := by ring
      _ ≤ (ε * cV ^ 2 * T ^ 3) * (T ^ 5 * (x : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hcube2
            (mul_nonneg (pow_nonneg hTpos.le 5) (sq_nonneg _))
      _ = ε * (cV ^ 2 * (x : ℝ) ^ 2 * T ^ 8) := by ring
      _ = ε * (cV * (x : ℝ) * L) ^ 2 := by rw [← hT4]; ring
      _ ≤ ε * V ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hWpos.le hVlow 2) hε.le
  have hDerr : (T / V) * E ≤ W / 3 := by
    have hE' : (T / V) * E = (Real.pi ^ 4 * T ^ 5 * ((p : ℝ) * (x : ℝ)) ^ 2) / V ^ 3 := by
      rw [hEdef, hS2eq]; field_simp; try ring
    rw [hE', hW, div_le_iff₀ (pow_pos hVpos 3)]
    have hrw : ε / V / 3 * V ^ 3 = ε * V ^ 2 / 3 := by field_simp; try ring
    rw [hrw]
    linarith [hkey2]
  -- the Gaussian tail is `≤ W/3`
  have hTail : 2 * Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) / (Real.pi ^ 2 * V * T) ≤ W / 3 := by
    have h1 : Real.pi ^ 2 * T ^ 2 / 2 ≤ Real.exp (Real.pi ^ 2 * T ^ 2 / 2) := by
      linarith [Real.add_one_le_exp (Real.pi ^ 2 * T ^ 2 / 2)]
    have hA1 : Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) * (Real.pi ^ 2 * T ^ 2) ≤ 2 := by
      have h3 := mul_le_mul_of_nonneg_right h1
        (Real.exp_nonneg (-(Real.pi ^ 2 * T ^ 2 / 2)))
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h3
      nlinarith [h3]
    have hT2sq : (25 : ℝ) ≤ T ^ 2 := by nlinarith [hT5, hTpos]
    have hmul : 1 * T ^ 2 ≤ (ε * T) * T ^ 2 := mul_le_mul_of_nonneg_right hb1 (sq_nonneg T)
    have hεT3 : (25 : ℝ) ≤ ε * T ^ 3 := by nlinarith [hmul, hT2sq]
    have hprod : (81 : ℝ) * 25 ≤ Real.pi ^ 4 * (ε * T ^ 3) :=
      mul_le_mul hpi81 hεT3 (by norm_num) (by positivity)
    have hden : (0 : ℝ) < Real.pi ^ 2 * T ^ 2 := by positivity
    have hmul2 : 6 * Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) * (Real.pi ^ 2 * T ^ 2)
        ≤ (ε * Real.pi ^ 2 * T) * (Real.pi ^ 2 * T ^ 2) := by
      calc 6 * Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) * (Real.pi ^ 2 * T ^ 2)
          = 6 * (Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) * (Real.pi ^ 2 * T ^ 2)) := by ring
        _ ≤ 6 * 2 := by linarith [hA1]
        _ ≤ Real.pi ^ 4 * (ε * T ^ 3) := by linarith [hprod]
        _ = (ε * Real.pi ^ 2 * T) * (Real.pi ^ 2 * T ^ 2) := by ring
    have hfinal : 6 * Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) ≤ ε * Real.pi ^ 2 * T :=
      le_of_mul_le_mul_right hmul2 hden
    rw [hW, div_le_iff₀ (by positivity)]
    have hrw : ε / V / 3 * (Real.pi ^ 2 * V * T) = ε * Real.pi ^ 2 * T / 3 := by
      field_simp; try ring
    rw [hrw]
    linarith [hfinal]
  -- the two-sided principal estimate, in beta-reduced form
  have habs : |(∫ t in (0 : ℝ)..(T / V),
        (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * ((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))
      - Real.sqrt (2 / Real.pi) / V
          * Real.exp (-(((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) ^ 2 / (2 * V ^ 2))) / 2|
      ≤ (T / V) * E + 2 * Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) / (Real.pi ^ 2 * V * T) :=
    gprincipal_two_sided
      (φ := fun t => ∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
      (V := V) (θ := (GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) (T := T) (E := E)
      (by fun_prop) hVpos hTpos hbnd
  have hgt : gt₁ a b c p q x = T / V := by simp only [gt₁, hTdef, hVdef]
  have hI0 : (∫ t in (0 : ℝ)..(gt₁ a b c p q x),
        (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)))
      = ∫ t in (0 : ℝ)..(T / V),
        (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * ((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t) := by
    rw [hgt]
    exact intervalIntegral.integral_congr (fun t _ => by rw [mul_assoc])
  have hprob : gProb a b c p q x n
      = 2 * ((∫ t in (0 : ℝ)..(gt₁ a b c p q x),
            (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
              * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)))
          + ∫ t in (gt₁ a b c p q x)..(1 / 2),
            (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
              * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))) := by
    rw [gprob_eq_integral, gsplit_half]
    congr 1
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((gintegrand_continuous a b c p q x n).intervalIntegrable (μ := volume)
        0 (gt₁ a b c p q x))
      ((gintegrand_continuous a b c p q x n).intervalIntegrable (μ := volume)
        (gt₁ a b c p q x) (1 / 2))).symm
  -- the Gaussian target: amplitude and exponent reconciliation
  have hsig : gSigma a b c p q x = V / 2 := by simp only [gSigma, hVdef]
  have htarget : (1 / (Real.sqrt (2 * Real.pi) * gSigma a b c p q x))
        * Real.exp (-(((n : ℝ) - gMu a b c p q x) ^ 2 / (2 * gSigma a b c p q x ^ 2)))
      = 2 * (Real.sqrt (2 / Real.pi) / V
          * Real.exp (-(((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) ^ 2 / (2 * V ^ 2))) / 2) := by
    have hexpo : ((n : ℝ) - (GS1 a b c p q x : ℝ) / 2) ^ 2 / (2 * (V / 2) ^ 2)
        = ((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) ^ 2 / (2 * V ^ 2) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    simp only [hsig, gMu]
    rw [gamp_eq hVpos, hexpo]
    ring
  -- the tail
  have hQb := hXt x hxXt n
  rw [← hVdef] at hQb
  have hQb3 : |∫ t in (gt₁ a b c p q x)..(1 / 2),
        (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))| ≤ W / 3 := by
    refine hQb.trans (le_of_eq ?_)
    rw [hW]; ring
  -- assembly
  have hepsV : ε / (V / 2) = 2 * W := by rw [hW]; field_simp; try ring
  rw [hprob, hI0, htarget, hsig, hepsV, abs_le]
  have h1 := abs_le.mp habs
  have h2 := abs_le.mp hQb3
  constructor
  · linarith [h1.1, h2.1, hDerr, hTail]
  · linarith [h1.2, h2.2, hDerr, hTail]

/-! ## Interface certification

Restatement of the target type verbatim, discharged by `@glclt_asymptotic`.  If this
`example` elaborates, no hypothesis was added, no quantifier was reordered or narrowed
(in particular `∀ n` stays INSIDE `∃ X₀`), and no parameter was specialized. -/
example : ∀ (a b c p q : ℕ), 1 < a → 1 < b → 1 < c →
    PairwiseCoprime3 a b c → 0 < q → q < p →
    p < q * min a (min b c) →
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      |gProb a b c p q x n
         - (1 / (Real.sqrt (2 * Real.pi) * gSigma a b c p q x))
             * Real.exp (-(((n : ℝ) - gMu a b c p q x) ^ 2
                 / (2 * gSigma a b c p q x ^ 2)))|
        ≤ ε / gSigma a b c p q x := @glclt_asymptotic

end

#print axioms Erdos123Band.glclt_asymptotic

end Erdos123Band
