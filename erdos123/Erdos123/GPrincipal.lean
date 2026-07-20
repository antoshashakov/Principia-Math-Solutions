/-
ERDŐS #123 — THE PRINCIPAL RANGE OF THE THREE-RANGE SPLIT
=========================================================
The analytic crux of the faithful local CLT: on `t ∈ [0, T/V]` with `T = (log x)^{1/4}`
and `V = √S₂`, the Fourier-inversion integrand
   `(∏_{s∈B} cos(π s t)) · cos(π (S₁ − 2n) t)`
is compared DIRECTLY (no `log cos` expansion) with the Gaussian `exp(−π²S₂t²/2)`, and the
resulting integral is bounded below by `1/(5V)` uniformly over the central window
`(2n − S₁)² ≤ S₂`.

Constant budget (see the module docstring of `gprincipal_abstract`):

  main term   ∫₀^∞ e^{−At²}cos(yt)dt = (1/(2V))·√(2/π)·e^{−θ²/(2V²)} ≥ 0.2419707…/V
  quartic err ≤ t₁·E = π⁴T⁵(px)²/V³                  ≤ 1/(100V)   for `T` large
  Gauss tail  ≤ 2e^{−π²T²/2}/(π²VT)                  ≤ 1/(100V)   for `T ≥ 5`
  ------------------------------------------------------------------------------
  ≥ (0.23 − 0.01 − 0.01)/V = 0.21/V ≥ 1/(5V).

Main result: `gprincipal_lower`.
-/
import Erdos123.GBandAux
import Erdos123.GaussFT
import Erdos123.GCosApprox

set_option maxHeartbeats 1000000

open MeasureTheory

namespace Erdos123Band

noncomputable section

/-- The principal cutoff scale `T = (log x)^{1/4}`, written without `rpow`. -/
noncomputable def gT (x : ℕ) : ℝ := Real.sqrt (Real.sqrt (Real.log x))

/-- The principal cutoff `t₁ = T / V`, `V = √S₂`. -/
noncomputable def gt₁ (a b c p q x : ℕ) : ℝ := gT x / Real.sqrt (GS2 a b c p q x)

/-! ## Step 0 — the half-line Gaussian-cosine integral -/

/-- `∫_{u>0} e^{−Au²} cos(yu) du = ½√(π/A)·e^{−y²/(4A)}` by evenness. -/
lemma gauss_half_line {A : ℝ} (hA : 0 < A) (y : ℝ) :
    (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(A * u ^ 2)) * Real.cos (y * u))
      = Real.sqrt (Real.pi / A) * Real.exp (-(y ^ 2 / (4 * A))) / 2 := by
  have heven : ∀ u : ℝ,
      (fun v : ℝ => Real.exp (-(A * v ^ 2)) * Real.cos (y * v)) |u|
        = Real.exp (-(A * u ^ 2)) * Real.cos (y * u) := by
    intro u
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h]
      show Real.exp (-(A * (-u) ^ 2)) * Real.cos (y * (-u))
        = Real.exp (-(A * u ^ 2)) * Real.cos (y * u)
      rw [show (-u) ^ 2 = u ^ 2 by ring, show y * -u = -(y * u) by ring, Real.cos_neg]
  have hcomp := integral_comp_abs
    (f := fun v : ℝ => Real.exp (-(A * v ^ 2)) * Real.cos (y * v))
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall heven),
    gaussian_ft_scaled hA y] at hcomp
  linarith

/-! ## Step 1 — the abstract principal-range lower bound -/

/-- **Abstract principal-range estimate.**  If a continuous `φ` is uniformly within `E`
of the Gaussian `exp(−(π²V²/2)t²)` on `[0, T/V]`, then its oscillatory integral over that
interval is at least the Gaussian main term minus the quartic error `(T/V)·E` minus the
Gaussian tail.

Derivation of the main term (independently re-verified, see the file header):
with `A = π²V²/2`, `y = πθ`, `∫_ℝ e^{−Au²}cos(yu)du = √(π/A)·e^{−y²/(4A)}`;
`π/A = 2/(πV²)` so `√(π/A) = √(2/π)/V`, and `y²/(4A) = θ²/(2V²)`.  Halving by evenness,
`∫₀^∞ = (1/(2V))·√(2/π)·e^{−θ²/(2V²)}`, which under `θ² ≤ V²` is `≥ √(2/π)e^{−1/2}/(2V)`. -/
lemma gprincipal_abstract {φ : ℝ → ℝ} {V θ T E : ℝ}
    (hφ : Continuous φ) (hV : 0 < V) (hT : 0 < T) (hθ : θ ^ 2 ≤ V ^ 2) (hE : 0 ≤ E)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) (T / V),
      |φ t - Real.exp (-(Real.pi ^ 2 * V ^ 2 / 2 * t ^ 2))| ≤ E) :
    Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / (2 * V)
        - (T / V) * E
        - 2 * Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) / (Real.pi ^ 2 * V * T)
      ≤ ∫ t in (0 : ℝ)..(T / V), φ t * Real.cos (Real.pi * θ * t) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := hpi.ne'
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
  -- (b) the interval integral of the Gaussian as a difference of half-line integrals
  have hb2 : (∫ t in (0 : ℝ)..t₁, Real.exp (-(A * t ^ 2)) * Real.cos (Real.pi * θ * t))
      = (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u))
        - ∫ u in Set.Ioi t₁, Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u) :=
    (intervalIntegral.integral_Ioi_sub_Ioi hgint.integrableOn ht₁.le).symm
  -- (c),(d),(e) the main term
  have hsqrt : Real.sqrt (Real.pi / A) = Real.sqrt (2 / Real.pi) / V := by
    have hnn : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) / V := div_nonneg (Real.sqrt_nonneg _) hV.le
    have hkey : Real.pi / A = (Real.sqrt (2 / Real.pi) / V) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity), hAdef]
      field_simp
    rw [hkey, Real.sqrt_sq hnn]
  have hexpge : Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-((Real.pi * θ) ^ 2 / (4 * A))) := by
    refine Real.exp_le_exp.mpr ?_
    have hq : (Real.pi * θ) ^ 2 / (4 * A) = θ ^ 2 / (2 * V ^ 2) := by
      rw [hAdef]; field_simp; ring
    rw [hq]
    have h2 : θ ^ 2 / (2 * V ^ 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hθ]
    linarith
  have hmain : Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / (2 * V)
      ≤ ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u) := by
    rw [gauss_half_line hA (Real.pi * θ), hsqrt]
    have hc : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) / V / 2 :=
      div_nonneg (div_nonneg (Real.sqrt_nonneg _) hV.le) (by norm_num)
    calc Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / (2 * V)
        = Real.sqrt (2 / Real.pi) / V / 2 * Real.exp (-(1 / 2)) := by field_simp
      _ ≤ Real.sqrt (2 / Real.pi) / V / 2 * Real.exp (-((Real.pi * θ) ^ 2 / (4 * A))) :=
          mul_le_mul_of_nonneg_left hexpge hc
      _ = Real.sqrt (2 / Real.pi) / V * Real.exp (-((Real.pi * θ) ^ 2 / (4 * A))) / 2 := by
          ring
  -- (f) the Gaussian tail
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
  -- (g) the quartic error
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
  rw [hsplit, hb2]
  have hA1 := abs_le.mp herr
  have hA2 := abs_le.mp htail
  linarith [hmain, hA1.1, hA2.2]

/-! ## Step 2 — the cutoff `T = (log x)^{1/4}` -/

lemma gT_nonneg (x : ℕ) : 0 ≤ gT x := Real.sqrt_nonneg _

lemma gT_pow_four {x : ℕ} (hx : 1 ≤ x) : gT x ^ 4 = Real.log x := by
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
  simp only [gT]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
    Real.sq_sqrt hL]

/-- `T = (log x)^{1/4} → ∞`. -/
lemma gT_eventually_ge (M : ℝ) : ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → M ≤ gT x := by
  by_cases hM : M ≤ 0
  · exact ⟨0, fun x _ => hM.trans (gT_nonneg x)⟩
  push_neg at hM
  refine ⟨Nat.ceil (Real.exp (M ^ 4)) + 1, fun x hx => ?_⟩
  have hxR : Real.exp (M ^ 4) ≤ (x : ℝ) := by
    have h1 : (Nat.ceil (Real.exp (M ^ 4)) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (Real.exp (M ^ 4)) ≤ x)
    exact le_trans (Nat.le_ceil _) h1
  have hlog : M ^ 4 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos (M ^ 4)) hxR
    rwa [Real.log_exp] at h
  have h1 : M ^ 2 ≤ Real.sqrt (Real.log x) := by
    have he : Real.sqrt (M ^ 4) = M ^ 2 := by
      rw [show M ^ 4 = (M ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    calc M ^ 2 = Real.sqrt (M ^ 4) := he.symm
      _ ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt hlog
  calc M = Real.sqrt (M ^ 2) := (Real.sqrt_sq hM.le).symm
    _ ≤ Real.sqrt (Real.sqrt (Real.log x)) := Real.sqrt_le_sqrt h1

/-! ## Step 3 — numeric facts -/

/-- `√(2/π)·e^{−1/2}/2 ≥ 0.23` (the true value is `0.2419707…`). -/
lemma gauss_const_ge : (23 / 100 : ℝ) ≤ Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / 2 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hs : (79 / 100 : ℝ) ≤ Real.sqrt (2 / Real.pi) := by
    have hrw : Real.sqrt ((79 / 100 : ℝ) ^ 2) = (79 / 100 : ℝ) := Real.sqrt_sq (by norm_num)
    calc (79 / 100 : ℝ) = Real.sqrt ((79 / 100 : ℝ) ^ 2) := hrw.symm
      _ ≤ Real.sqrt (2 / Real.pi) := by
          refine Real.sqrt_le_sqrt ?_
          rw [le_div_iff₀ Real.pi_pos]
          nlinarith [hpi]
  have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have hehalf : Real.exp (1 / 2 : ℝ) < 5 / 3 := by
    nlinarith [hsq, Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]
  have hmul : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2 : ℝ) = 1 := by
    rw [← Real.exp_add]; norm_num
  have he : (3 / 5 : ℝ) ≤ Real.exp (-(1 / 2)) := by
    nlinarith [hmul, hehalf, Real.exp_pos (1 / 2 : ℝ), Real.exp_pos (-(1 / 2 : ℝ))]
  have hprod : (79 / 100 : ℝ) * (3 / 5 : ℝ)
      ≤ Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) :=
    mul_le_mul hs he (by norm_num) (Real.sqrt_nonneg _)
  linarith

/-- `e^{−4} ≤ 1/16`. -/
lemma exp_neg_four_le : Real.exp (-4 : ℝ) ≤ 1 / 16 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have e2 : Real.exp (1 : ℝ) * Real.exp (1 : ℝ) = Real.exp 2 := by
    rw [← Real.exp_add]; norm_num
  have e4 : Real.exp (2 : ℝ) * Real.exp (2 : ℝ) = Real.exp 4 := by
    rw [← Real.exp_add]; norm_num
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by nlinarith [h1, e2]
  have h4 : (16 : ℝ) ≤ Real.exp 4 := by nlinarith [h2, e4]
  have hmul : Real.exp (-4 : ℝ) * Real.exp (4 : ℝ) = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [hmul, h4, Real.exp_pos (-4 : ℝ), Real.exp_pos (4 : ℝ)]

/-! ## Step 4 — the principal-range lower bound -/

/-- **The principal range of the three-range split.**  Uniformly over the full central
window `(2n − S₁)² ≤ S₂`, the principal piece of the Fourier-inversion integral is at
least `1/(5√S₂)`. -/
theorem gprincipal_lower (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      (2 * (n : ℤ) - (GS1 a b c p q x : ℤ)) ^ 2 ≤ (GS2 a b c p q x : ℤ) →
        1 / (5 * Real.sqrt (GS2 a b c p q x))
          ≤ ∫ t in (0 : ℝ)..(gt₁ a b c p q x),
              (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
                * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) := by
  classical
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi9 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2, Real.pi_pos]
  obtain ⟨cV, hcV, X₁, hX₁⟩ := gV_lower a b c p q ha hb hc hco hq hqp hpd
  set M : ℝ := 5 + Real.pi * p / cV + 100 * Real.pi ^ 4 * (p : ℝ) ^ 2 / cV ^ 2 with hMdef
  obtain ⟨X₂, hX₂⟩ := gT_eventually_ge M
  refine ⟨max (max X₁ X₂) 2, fun x hx n hn => ?_⟩
  have hxX₁ : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxX₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  set T : ℝ := gT x with hTdef
  set V : ℝ := Real.sqrt (GS2 a b c p q x) with hVdef
  set L : ℝ := Real.log x with hLdef
  have hTM : M ≤ T := hX₂ x hxX₂
  have hMnn1 : (0 : ℝ) ≤ Real.pi * p / cV := div_nonneg (by positivity) hcV.le
  have hMnn2 : (0 : ℝ) ≤ 100 * Real.pi ^ 4 * (p : ℝ) ^ 2 / cV ^ 2 :=
    div_nonneg (by positivity) (sq_nonneg cV)
  have hT5 : (5 : ℝ) ≤ T := by rw [hMdef] at hTM; linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hTne : T ≠ 0 := hTpos.ne'
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
  -- `π p ≤ cV T³`
  have hcube1 : Real.pi * (p : ℝ) ≤ cV * T ^ 3 := by
    have h1 : Real.pi * (p : ℝ) / cV ≤ T := by rw [hMdef] at hTM; linarith
    have h2 : Real.pi * (p : ℝ) ≤ cV * T := by rw [div_le_iff₀ hcV] at h1; linarith
    calc Real.pi * (p : ℝ) ≤ cV * T := h2
      _ ≤ cV * T ^ 3 := mul_le_mul_of_nonneg_left hT3 hcV.le
  -- `100 π⁴ p² ≤ cV² T³`
  have hcube2 : 100 * Real.pi ^ 4 * (p : ℝ) ^ 2 ≤ cV ^ 2 * T ^ 3 := by
    have h1 : 100 * Real.pi ^ 4 * (p : ℝ) ^ 2 / cV ^ 2 ≤ T := by
      rw [hMdef] at hTM; linarith
    have h2 : 100 * Real.pi ^ 4 * (p : ℝ) ^ 2 ≤ cV ^ 2 * T := by
      rw [div_le_iff₀ (pow_pos hcV 2)] at h1; linarith
    calc 100 * Real.pi ^ 4 * (p : ℝ) ^ 2 ≤ cV ^ 2 * T := h2
      _ ≤ cV ^ 2 * T ^ 3 := mul_le_mul_of_nonneg_left hT3 (pow_pos hcV 2).le
  have hπT : (45 : ℝ) ≤ Real.pi ^ 2 * T := by nlinarith [hpi9, hT5]
  -- (A) the central window
  have hθ : ((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) ^ 2 ≤ V ^ 2 := by
    have hcast : (2 * (n : ℝ) - (GS1 a b c p q x : ℝ)) ^ 2
        ≤ ((GS2 a b c p q x : ℕ) : ℝ) := by exact_mod_cast hn
    rw [hS2eq] at hcast
    calc ((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) ^ 2
        = (2 * (n : ℝ) - (GS1 a b c p q x : ℝ)) ^ 2 := by ring
      _ ≤ V ^ 2 := hcast
  -- (B) smallness on the principal range
  have hsmall : ∀ t : ℝ, 0 ≤ t → t ≤ T / V → ∀ s ∈ GBand a b c p q x,
      |Real.pi * ((s : ℝ) * t)| ≤ 1 := by
    intro t ht0 htt s hs
    have hsle : (s : ℝ) ≤ (p : ℝ) * (x : ℝ) := by exact_mod_cast gband_le hq hs
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    rw [abs_of_nonneg (mul_nonneg hpi.le (mul_nonneg hs0 ht0))]
    have hkey : Real.pi * ((p : ℝ) * (x : ℝ)) * T ≤ V := by
      have h1 : Real.pi * ((p : ℝ) * (x : ℝ)) * T ≤ cV * (x : ℝ) * L := by
        rw [← hT4]
        nlinarith [mul_le_mul_of_nonneg_right hcube1
          (mul_nonneg hxpos.le hTpos.le)]
      linarith
    have h3 : Real.pi * ((p : ℝ) * (x : ℝ)) * (T / V) ≤ 1 := by
      rw [show Real.pi * ((p : ℝ) * (x : ℝ)) * (T / V)
          = (Real.pi * ((p : ℝ) * (x : ℝ)) * T) / V by ring, div_le_one hVpos]
      exact hkey
    have h2 : (s : ℝ) * t ≤ ((p : ℝ) * (x : ℝ)) * (T / V) :=
      mul_le_mul hsle htt ht0 (by positivity)
    calc Real.pi * ((s : ℝ) * t)
        ≤ Real.pi * (((p : ℝ) * (x : ℝ)) * (T / V)) :=
          mul_le_mul_of_nonneg_left h2 hpi.le
      _ ≤ 1 := by linarith [h3]
  -- (C) the uniform Gaussian error on the principal range
  set E : ℝ := Real.pi ^ 4 * (T / V) ^ 4
      * (((p : ℝ) * (x : ℝ)) ^ 2 * ((GS2 a b c p q x : ℕ) : ℝ)) with hEdef
  have hEnn : (0 : ℝ) ≤ E := by rw [hEdef]; positivity
  have hbnd : ∀ t ∈ Set.Icc (0 : ℝ) (T / V),
      |(∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
        - Real.exp (-(Real.pi ^ 2 * V ^ 2 / 2 * t ^ 2))| ≤ E := by
    intro t ht
    obtain ⟨ht0, htt⟩ := ht
    -- the type ascription forces the beta-reduced form (defeq, so it always typechecks)
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
  -- (D) the quartic error is `≤ 1/(100 V)`
  have hkey2 : 100 * (Real.pi ^ 4 * T ^ 5 * ((p : ℝ) * (x : ℝ)) ^ 2) ≤ V ^ 2 := by
    calc 100 * (Real.pi ^ 4 * T ^ 5 * ((p : ℝ) * (x : ℝ)) ^ 2)
        = (100 * Real.pi ^ 4 * (p : ℝ) ^ 2) * (T ^ 5 * (x : ℝ) ^ 2) := by ring
      _ ≤ (cV ^ 2 * T ^ 3) * (T ^ 5 * (x : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hcube2
            (mul_nonneg (pow_nonneg hTpos.le 5) (sq_nonneg _))
      _ = cV ^ 2 * (x : ℝ) ^ 2 * T ^ 8 := by ring
      _ = (cV * (x : ℝ) * L) ^ 2 := by rw [← hT4]; ring
      _ ≤ V ^ 2 := pow_le_pow_left₀ hWpos.le hVlow 2
  have hDerr : (T / V) * E ≤ (1 / 100) * (1 / V) := by
    have hE' : (T / V) * E = (Real.pi ^ 4 * T ^ 5 * ((p : ℝ) * (x : ℝ)) ^ 2) / V ^ 3 := by
      rw [hEdef, hS2eq]; field_simp; try ring
    rw [hE', div_le_iff₀ (pow_pos hVpos 3)]
    have hrw : (1 / 100 : ℝ) * (1 / V) * V ^ 3 = V ^ 2 / 100 := by field_simp; try ring
    rw [hrw]
    linarith [hkey2]
  -- (E) the Gaussian tail is `≤ 1/(100 V)`
  have hTail : 2 * Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) / (Real.pi ^ 2 * V * T)
      ≤ (1 / 100) * (1 / V) := by
    have h1 : Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) ≤ 1 / 16 := by
      refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_four_le
      nlinarith [hpi9, hT5]
    rw [div_le_iff₀ (mul_pos (mul_pos (pow_pos hpi 2) hVpos) hTpos)]
    have hrw : (1 / 100 : ℝ) * (1 / V) * (Real.pi ^ 2 * V * T) = Real.pi ^ 2 * T / 100 := by
      field_simp; try ring
    rw [hrw]
    linarith [h1, hπT]
  -- (F) apply the abstract estimate
  have habs := gprincipal_abstract
    (φ := fun t => ∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
    (V := V) (θ := (GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) (T := T) (E := E)
    (by fun_prop) hVpos hTpos hθ hEnn hbnd
  have hgt : gt₁ a b c p q x = T / V := by simp only [gt₁, hTdef, hVdef]
  have hgoal_eq : (∫ t in (0 : ℝ)..(gt₁ a b c p q x),
        (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)))
      = ∫ t in (0 : ℝ)..(T / V),
        (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * ((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t) := by
    rw [hgt]
    exact intervalIntegral.integral_congr (fun t _ => by rw [mul_assoc])
  rw [hgoal_eq]
  refine le_trans ?_ habs
  have hconst : (23 / 100 : ℝ) * (1 / V)
      ≤ Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / (2 * V) := by
    rw [show Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / (2 * V)
        = (Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / 2) * (1 / V) by ring]
    exact mul_le_mul_of_nonneg_right gauss_const_ge (one_div_nonneg.mpr hVpos.le)
  have hfin : (1 : ℝ) / (5 * V) = (1 / 5) * (1 / V) := by field_simp; try ring
  rw [hfin]
  linarith [hconst, hDerr, hTail, one_div_pos.mpr hVpos]

end

end Erdos123Band
