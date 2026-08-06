import Mathlib
import SendovNSigma
import SendovNJBound
import SendovNMidChain

set_option maxHeartbeats 4000000

/-!
# P9: `SplitChain11` — the τ-split error bound (degree 11 only)

The unsplit majorant is too lossy at `N = 10`, so `split_cert` in
`certificates/degree11_verify.py` (and `emit_boxes11v2.py`) splits the error
integral at `v = τ`:

* head `[0, τ]`: the termwise centred-esp estimate (the P8 machinery, with the
  integrals stopped at `τ`);
* tail `[τ, 1]`: `|G(t)| ≤ q₁(a; t/a)⁵` by AM–GM over the 10 factors
  (`q₁(a;v) = 1 − (2(10−S+Sa²)/10)v + a²v²`, using `u ≥ L_S(a)` and
  `|Yⱼ| ≤ 1`), plus `|(1−tμ)¹⁰| ≤ q₀⁵`, so the tail integrand is bounded by
  `q₀⁵ + q₁⁵`.

Main statements:

* `G_tail_bound` — the new AM–GM bound (the `H_bound` shape of `SendovNEsymm`,
  reused on the uncentred family);
* `EmajTau` — the split majorant
  `∑ₘ cₘηᵐ a^{m+1}∫₀^τ vᵐq₀^{ℓₘ}dv + a∫_τ¹ (q₀⁵+q₁⁵)dv`;
* `norm_I_sub_J_le_EmajTau` — `|I − J| ≤ EmajTau` at feasible points;
* `split_row_nonpos` — the τ-split Proposition 4.1, reshaped: the boxes'
  `principal + split_cert` closed form is nonpositive at the counterexample:
  `(1−a)/11 + η²/22 − hh⁵/(11λ) − EmajTau ≤ 0`.

`τ = 1` degenerates to the unsplit form (the tail integral is empty), so this
file also serves the τ = 1 boxes; the per-box τ comes from the box headers.
-/

namespace SendovN.Split11

open Finset intervalIntegral MidChainN

/-- The verifiers' `q₁(a;v) = 1 − (2(10−S+Sa²)/10)v + a²v²` (the `y`-free
second majorant; `unit_second=True` in `q_poly`). -/
noncomputable def q1 (S a v : ℝ) : ℝ :=
  1 - (2 * (10 - S + S * a ^ 2) / 10) * v + a ^ 2 * v ^ 2

/-- `q₁` in the variable `t` (before the substitution `t = av`). -/
noncomputable def qt1 (S a t : ℝ) : ℝ :=
  1 - (2 * (10 - S + S * a ^ 2) / (10 * a)) * t + t ^ 2

theorem continuous_qt1 (S a : ℝ) : Continuous (qt1 S a) := by
  unfold qt1
  fun_prop

/-- The substitution, pointwise: `qt1(av) = q₁(v)`. -/
theorem qt1_at (S a v : ℝ) (ha : a ≠ 0) : qt1 S a (a * v) = q1 S a v := by
  unfold qt1 q1
  field_simp

/-- `∫_(a·t0)^(a·t1) f = a ∫_(t0)^(t1) f(a·)`. -/
theorem integral_scale_ab (a t0 t1 : ℝ) (f : ℝ → ℝ) :
    (∫ t in (a * t0)..(a * t1), f t) = a * ∫ v in t0..t1, f (a * v) := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := t0) (b := t1)
    (f := f) a
  simp only [smul_eq_mul] at h
  exact h.symm

/-- The head change of variables: `∫₀^{aτ} tᵐ qt^ℓ dt = a^{m+1}∫₀^τ vᵐ q₀^ℓ dv`. -/
theorem integral_term_tau {N : ℕ} (hN : 0 < N) (S a eta tau : ℝ) (ha : 0 < a)
    (m l : ℕ) :
    (∫ t in (0:ℝ)..(a * tau), t ^ m * qt N S a eta t ^ l)
      = a ^ (m + 1) * ∫ v in (0:ℝ)..tau, v ^ m * q0 N S a eta v ^ l := by
  have h := integral_scale_ab a 0 tau (fun t => t ^ m * qt N S a eta t ^ l)
  rw [mul_zero] at h
  rw [h]
  have hcongr : ∀ v : ℝ, (a * v) ^ m * qt N S a eta (a * v) ^ l
      = a ^ m * (v ^ m * q0 N S a eta v ^ l) := by
    intro v
    rw [qt_at hN S a eta v (ne_of_gt ha), mul_pow]
    ring
  simp only [hcongr]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- **The tail AM–GM bound** (the `H_bound` shape on the uncentred family):
`‖∏ⱼ(1 − t(μ+Dⱼ))‖ ≤ qt1(t)⁵` for `t ≥ 0`, using `∑Dⱼ = 0`, `‖μ+Dⱼ‖ ≤ 1` and
the key inequality `10 − S + Sa² ≤ 10au`. -/
theorem G_tail_bound {S a : ℝ} (ha : 0 < a) (mu : ℂ) (D : Fin 10 → ℂ) {t : ℝ}
    (ht0 : 0 ≤ t) (hz : ∑ j, D j = 0) (hY1 : ∀ j, ‖mu + D j‖ ≤ 1)
    (hkey : (10:ℝ) - S + S * a ^ 2 ≤ 10 * a * mu.re) :
    ‖∏ j, ((1:ℂ) - (t:ℂ) * (mu + D j))‖ ≤ qt1 S a t ^ 5 := by
  -- pointwise expansion of the squared factor norms
  have hx : ∀ j : Fin 10, ‖(1:ℂ) - (t:ℂ) * (mu + D j)‖ ^ 2
      = 1 - 2 * t * (mu + D j).re + t ^ 2 * ‖mu + D j‖ ^ 2 := by
    intro j
    rw [← Complex.normSq_eq_norm_sq, normSq_one_sub, Complex.normSq_eq_norm_sq]
  -- `∑ Re(μ+Dⱼ) = 10u`
  have hsumY : ∑ j : Fin 10, (mu + D j) = 10 * mu := by
    rw [Finset.sum_add_distrib, hz, add_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hre : ∑ j : Fin 10, (mu + D j).re = 10 * mu.re := by
    calc ∑ j : Fin 10, (mu + D j).re = (∑ j : Fin 10, (mu + D j)).re :=
          (Complex.re_sum _ _).symm
      _ = 10 * mu.re := by rw [hsumY]; simp [Complex.mul_re]
  -- `∑‖μ+Dⱼ‖² ≤ 10`
  have hsumnorm : ∑ j : Fin 10, ‖mu + D j‖ ^ 2 ≤ 10 := by
    calc ∑ j : Fin 10, ‖mu + D j‖ ^ 2 ≤ ∑ _j : Fin 10, (1:ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          nlinarith [hY1 j, norm_nonneg (mu + D j)]
      _ = 10 := by simp
  -- the arithmetic mean is at most `qt1`
  have h10a : (0:ℝ) < 10 * a := by linarith
  have hdiv : 2 * ((10:ℝ) - S + S * a ^ 2) / (10 * a) ≤ 2 * mu.re := by
    rw [div_le_iff₀ h10a]
    nlinarith [hkey]
  have hsum : ∑ j : Fin 10, ‖(1:ℂ) - (t:ℂ) * (mu + D j)‖ ^ 2
      ≤ 10 * qt1 S a t := by
    have hexp : ∑ j : Fin 10, ‖(1:ℂ) - (t:ℂ) * (mu + D j)‖ ^ 2
        = 10 - 2 * t * (10 * mu.re) + t ^ 2 * ∑ j : Fin 10, ‖mu + D j‖ ^ 2 := by
      rw [Finset.sum_congr rfl fun j _ => hx j, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hre]
      simp
    rw [hexp]
    unfold qt1
    nlinarith [mul_le_mul_of_nonneg_right hdiv ht0, sq_nonneg t,
      mul_le_mul_of_nonneg_left hsumnorm (sq_nonneg t)]
  -- `qt1 ≥ 0` (it dominates a mean of squares)
  have hmean0 : (0:ℝ) ≤ ∑ j : Fin 10, ‖(1:ℂ) - (t:ℂ) * (mu + D j)‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hq1nn : 0 ≤ qt1 S a t := by nlinarith [hsum, hmean0]
  -- AM–GM with uniform weights `1/10`
  have hxnn : ∀ j ∈ (univ : Finset (Fin 10)),
      (0:ℝ) ≤ ‖(1:ℂ) - (t:ℂ) * (mu + D j)‖ ^ 2 := fun j _ => sq_nonneg _
  have hw' : ∀ j ∈ (univ : Finset (Fin 10)), (0:ℝ) ≤ 1 / (10:ℝ) := fun j _ => by
    norm_num
  have hw1 : ∑ _j : Fin 10, (1 / (10:ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hamgm := Real.geom_mean_le_arith_mean_weighted univ (fun _ => 1 / (10:ℝ))
    (fun j => ‖(1:ℂ) - (t:ℂ) * (mu + D j)‖ ^ 2) hw' hw1 hxnn
  set X : ℝ := ∏ j : Fin 10, ‖(1:ℂ) - (t:ℂ) * (mu + D j)‖ ^ 2 with hX
  have hX0 : 0 ≤ X := Finset.prod_nonneg fun j _ => sq_nonneg _
  have hlhs : ∏ j : Fin 10, (‖(1:ℂ) - (t:ℂ) * (mu + D j)‖ ^ 2) ^ (1 / (10:ℝ) : ℝ)
      = X ^ (1 / (10:ℝ) : ℝ) := by
    rw [hX, ← Real.finsetProd_rpow univ _ (fun j _ => sq_nonneg _) _]
  have hrhs : ∑ j : Fin 10, (1 / (10:ℝ)) * ‖(1:ℂ) - (t:ℂ) * (mu + D j)‖ ^ 2
      ≤ qt1 S a t := by
    rw [← Finset.mul_sum]
    calc (1 / (10:ℝ)) * ∑ j : Fin 10, ‖(1:ℂ) - (t:ℂ) * (mu + D j)‖ ^ 2
        ≤ (1 / (10:ℝ)) * (10 * qt1 S a t) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = qt1 S a t := by ring
  have h1 : X ^ (1 / (10:ℝ) : ℝ) ≤ qt1 S a t := by
    rw [← hlhs]
    exact le_trans hamgm hrhs
  have h2 : X ≤ qt1 S a t ^ 10 := by
    have h3 : (X ^ (1 / (10:ℝ) : ℝ)) ^ (10:ℕ) ≤ qt1 S a t ^ (10:ℕ) :=
      pow_le_pow_left₀ (Real.rpow_nonneg hX0 _) h1 10
    rwa [← Real.rpow_natCast (X ^ (1 / (10:ℝ) : ℝ)) 10, ← Real.rpow_mul hX0,
      show (1 / (10:ℝ)) * ((10:ℕ):ℝ) = 1 by norm_num, Real.rpow_one] at h3
  -- conclude on the norm of the product
  have hnorm2 : ‖∏ j, ((1:ℂ) - (t:ℂ) * (mu + D j))‖ ^ 2 = X := by
    rw [hX, Complex.norm_prod, ← Finset.prod_pow]
  have hfin : ‖∏ j, ((1:ℂ) - (t:ℂ) * (mu + D j))‖ ^ 2 ≤ (qt1 S a t ^ 5) ^ 2 := by
    rw [hnorm2]
    calc X ≤ qt1 S a t ^ 10 := h2
      _ = (qt1 S a t ^ 5) ^ 2 := by ring
  have h5 := Real.sqrt_le_sqrt hfin
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h5

/-- The `μ`-power tail bound: `‖(1−tμ)¹⁰‖ ≤ qt(t)⁵` for `t ≥ 0`. -/
theorem J_pow_tail_le {S a eta t : ℝ} (mu : ℂ) (ha : 0 < a) (ht0 : 0 ≤ t)
    (hnormSq : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : (10:ℝ) - S + S * a ^ 2 ≤ 10 * a * mu.re) :
    ‖((1:ℂ) - (t:ℂ) * mu) ^ 10‖ ≤ qt 10 S a eta t ^ 5 := by
  have hN : 0 < (10:ℕ) := by norm_num
  have hkey' : ((10:ℕ):ℝ) - S + S * a ^ 2 ≤ ((10:ℕ):ℝ) * a * mu.re := by
    exact_mod_cast hkey
  have hwsq : ‖(1:ℂ) - (t:ℂ) * mu‖ ^ 2 ≤ qt 10 S a eta t := by
    have h := normSq_le_qt (a := a) (eta := eta) (S := S) (t := t) hN mu ha ht0
      hnormSq hkey'
    rwa [Complex.normSq_eq_norm_sq] at h
  rw [norm_pow]
  calc ‖(1:ℂ) - (t:ℂ) * mu‖ ^ 10 = (‖(1:ℂ) - (t:ℂ) * mu‖ ^ 2) ^ 5 := by ring
    _ ≤ qt 10 S a eta t ^ 5 := pow_le_pow_left₀ (by positivity) hwsq 5

/-- **The split majorant** — the verifiers' `split_cert` error term:
head `∑ₘ cₘηᵐ a^{m+1}∫₀^τ vᵐq₀^{ℓₘ}dv` plus tail `a∫_τ¹(q₀⁵+q₁⁵)dv`. -/
noncomputable def EmajTau (c : ℕ → ℝ) (S a eta tau : ℝ) : ℝ :=
  (∑ m ∈ Finset.Icc 2 10, c m * eta ^ m * (a ^ (m + 1)
    * ∫ v in (0:ℝ)..tau, v ^ m * q0 10 S a eta v ^ ell 10 m))
  + a * ∫ v in tau..(1:ℝ), (q0 10 S a eta v ^ 5 + q1 S a v ^ 5)

/-- Norm-vs-majorant bound on a general interval `[b, a]`. -/
theorem norm_integral_le_of_norm_le_on {b a : ℝ} (hba : b ≤ a) (H : ℝ → ℂ)
    (bb : ℝ → ℝ)
    (hH : IntervalIntegrable H MeasureTheory.volume b a)
    (hb : IntervalIntegrable bb MeasureTheory.volume b a)
    (hle : ∀ t ∈ Set.Icc b a, ‖H t‖ ≤ bb t) :
    ‖∫ t in b..a, H t‖ ≤ ∫ t in b..a, bb t := by
  have h1 : ‖∫ t in b..a, H t‖ ≤ ∫ t in b..a, ‖H t‖ :=
    norm_integral_le_integral_norm hba
  have h2 : (∫ t in b..a, ‖H t‖) ≤ ∫ t in b..a, bb t := by
    apply integral_mono_on hba hH.norm hb
    intro t ht
    exact hle t ht
  linarith

/-- **`|I − J| ≤ EmajTau`** at feasible points of a degree-11 row. -/
theorem norm_I_sub_J_le_EmajTau (c : ℕ → ℝ)
    (hcnn : ∀ m ∈ Finset.Icc 2 10, 0 ≤ c m)
    (mu : ℂ) (D : Fin 10 → ℂ) {a eta S lam beta tau : ℝ}
    (ha : 0 < a) (hab : a ≤ beta) (hbeta : 0 ≤ beta) (heta0 : 0 ≤ eta)
    (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1)
    (hnormSq : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : (10:ℝ) - S + S * a ^ 2 ≤ 10 * a * mu.re)
    (hL : (10:ℝ) * a * lam ≤ 10 - S + S * a ^ 2) (h2lb : beta ≤ 2 * lam)
    (hz : ∑ j, D j = 0) (hY1 : ∀ j, ‖mu + D j‖ ≤ 1)
    (hc : ∀ m ∈ Finset.Icc 2 10, ‖esD D m‖ ≤ c m * eta ^ m) :
    ‖(∫ t in (0:ℝ)..a, ∏ j, ((1:ℂ) - (t:ℂ) * (mu + D j)))
        - (∫ t in (0:ℝ)..a, ((1:ℂ) - (t:ℂ) * mu) ^ 10)‖
      ≤ EmajTau c S a eta tau := by
  have hN : 0 < (10:ℕ) := by norm_num
  have hkey' : ((10:ℕ):ℝ) - S + S * a ^ 2 ≤ ((10:ℕ):ℝ) * a * mu.re := by
    exact_mod_cast hkey
  have hL' : ((10:ℕ):ℝ) * a * lam ≤ ((10:ℕ):ℝ) - S + S * a ^ 2 := by
    exact_mod_cast hL
  set F : ℝ → ℂ := fun t => ∏ j, ((1:ℂ) - (t:ℂ) * (mu + D j)) with hF
  set G : ℝ → ℂ := fun t => ((1:ℂ) - (t:ℂ) * mu) ^ 10 with hG
  have hFcont : Continuous F := by rw [hF]; fun_prop
  have hGcont : Continuous G := by rw [hG]; fun_prop
  have hcontqt := continuous_qt 10 S a eta
  have hcontqt1 := continuous_qt1 S a
  -- the two majorants
  set bhead : ℝ → ℝ := fun t => ∑ m ∈ Finset.Icc 2 10,
    c m * eta ^ m * (t ^ m * qt 10 S a eta t ^ ell 10 m) with hbhead
  set btail : ℝ → ℝ := fun t => qt 10 S a eta t ^ 5 + qt1 S a t ^ 5 with hbtail
  have hbheadcont : Continuous bhead := by
    rw [hbhead]
    apply continuous_finset_sum
    intro m _
    exact ((continuous_pow m).mul (hcontqt.pow (ell 10 m))).const_mul
      (c m * eta ^ m)
  have hbtailcont : Continuous btail := by
    rw [hbtail]
    fun_prop
  have hatau0 : 0 ≤ a * tau := mul_nonneg ha.le htau0
  have hataua : a * tau ≤ a := by nlinarith
  -- split both integrals at `t = aτ`
  have hsplitF : (∫ t in (0:ℝ)..(a * tau), F t) + (∫ t in (a * tau)..a, F t)
      = ∫ t in (0:ℝ)..a, F t :=
    integral_add_adjacent_intervals (hFcont.intervalIntegrable _ _)
      (hFcont.intervalIntegrable _ _)
  have hsplitG : (∫ t in (0:ℝ)..(a * tau), G t) + (∫ t in (a * tau)..a, G t)
      = ∫ t in (0:ℝ)..a, G t :=
    integral_add_adjacent_intervals (hGcont.intervalIntegrable _ _)
      (hGcont.intervalIntegrable _ _)
  -- head piece: the P8 termwise estimate on `[0, aτ]`
  have hhead : ‖(∫ t in (0:ℝ)..(a * tau), F t) - (∫ t in (0:ℝ)..(a * tau), G t)‖
      ≤ ∫ t in (0:ℝ)..(a * tau), bhead t := by
    apply norm_I_sub_J_le hatau0 F G bhead (hFcont.intervalIntegrable _ _)
      (hGcont.intervalIntegrable _ _) (hbheadcont.intervalIntegrable _ _)
    intro t ht
    exact pointwise hN c hcnn mu D ha hab hbeta heta0 hnormSq hkey' hL' h2lb hz hc
      t ht.1 (le_trans ht.2 hataua)
  -- tail piece: the AM–GM bound on `[aτ, a]`
  have htail : ‖(∫ t in (a * tau)..a, F t) - (∫ t in (a * tau)..a, G t)‖
      ≤ ∫ t in (a * tau)..a, btail t := by
    rw [← intervalIntegral.integral_sub (hFcont.intervalIntegrable _ _)
      (hGcont.intervalIntegrable _ _)]
    apply norm_integral_le_of_norm_le_on hataua (fun t => F t - G t) btail
      ((hFcont.sub hGcont).intervalIntegrable _ _)
      (hbtailcont.intervalIntegrable _ _)
    intro t ht
    have ht0 : 0 ≤ t := le_trans hatau0 ht.1
    calc ‖F t - G t‖ ≤ ‖F t‖ + ‖G t‖ := norm_sub_le _ _
      _ ≤ qt1 S a t ^ 5 + qt 10 S a eta t ^ 5 := by
          have h1 := G_tail_bound ha mu D ht0 hz hY1 hkey
          have h2 := J_pow_tail_le mu ha ht0 hnormSq hkey
          exact add_le_add h1 h2
      _ = btail t := by simp only [hbtail]; ring
  -- the head integral in closed `v`-form
  have hheadeq : (∫ t in (0:ℝ)..(a * tau), bhead t)
      = ∑ m ∈ Finset.Icc 2 10, c m * eta ^ m * (a ^ (m + 1)
          * ∫ v in (0:ℝ)..tau, v ^ m * q0 10 S a eta v ^ ell 10 m) := by
    simp only [hbhead]
    rw [integral_majorant 10 (a * tau) c eta (qt 10 S a eta) (ell 10) hcontqt]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_term_tau hN S a eta tau ha m (ell 10 m)]
  -- the tail integral in `v`-form
  have htaileq : (∫ t in (a * tau)..a, btail t)
      = a * ∫ v in tau..(1:ℝ), (q0 10 S a eta v ^ 5 + q1 S a v ^ 5) := by
    have h := integral_scale_ab a tau 1 btail
    rw [mul_one] at h
    rw [h]
    have hcongr : ∀ v : ℝ, btail (a * v)
        = q0 10 S a eta v ^ 5 + q1 S a v ^ 5 := by
      intro v
      simp only [hbtail]
      rw [qt_at hN S a eta v (ne_of_gt ha), qt1_at S a v (ne_of_gt ha)]
    simp only [hcongr]
  -- assemble
  calc ‖(∫ t in (0:ℝ)..a, F t) - (∫ t in (0:ℝ)..a, G t)‖
      = ‖((∫ t in (0:ℝ)..(a * tau), F t) - (∫ t in (0:ℝ)..(a * tau), G t))
          + ((∫ t in (a * tau)..a, F t) - (∫ t in (a * tau)..a, G t))‖ := by
        rw [← hsplitF, ← hsplitG]
        congr 1
        ring
    _ ≤ ‖(∫ t in (0:ℝ)..(a * tau), F t) - (∫ t in (0:ℝ)..(a * tau), G t)‖
        + ‖(∫ t in (a * tau)..a, F t) - (∫ t in (a * tau)..a, G t)‖ :=
        norm_add_le _ _
    _ ≤ (∫ t in (0:ℝ)..(a * tau), bhead t) + ∫ t in (a * tau)..a, btail t :=
        add_le_add hhead htail
    _ = EmajTau c S a eta tau := by
        rw [hheadeq, htaileq]
        rfl

/-- **The τ-split Proposition 4.1, reshaped** (`split_row_to_nonpos`): at a
feasible degree-11 counterexample point, the `split_cert` closed form is
nonpositive: `(1−a)/11 + η²/22 − hh⁵/(11λ) − EmajTau ≤ 0`. -/
theorem split_row_nonpos {alpha beta S lam sigma tau : ℝ} (c : ℕ → ℝ)
    (hcnn : ∀ m ∈ Finset.Icc 2 10, 0 ≤ c m)
    (mu : ℂ) (D : Fin 10 → ℂ) (a eta : ℝ)
    (halpha0 : 0 < alpha) (hbeta1 : beta ≤ 1) (hlam0 : 0 < lam)
    (h2lb : beta ≤ 2 * lam) (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1)
    (h0 : alpha ≤ a) (h1 : a ≤ beta)
    (heta0 : 0 ≤ eta) (hnormSq : Complex.normSq mu = 1 - eta ^ 2)
    (hloc : (10:ℝ) ≤ 10 * a * mu.re + (1 - a ^ 2) * sigma)
    (hsig : sigma ≤ S)
    (hL : 0 ≤ S * a ^ 2 - 10 * lam * a + 10 - S)
    (hz : ∑ j, D j = 0) (hY1 : ∀ j, ‖mu + D j‖ ≤ 1)
    (hc : ∀ m ∈ Finset.Icc 2 10, ‖esD D m‖ ≤ c m * eta ^ m)
    (hI : ‖∫ t in (0:ℝ)..a, ∏ j, ((1:ℂ) - (t:ℂ) * (mu + D j))‖ < a / 11) :
    (1 - a) / 11 + eta ^ 2 / 22 - hh 10 S a eta ^ 5 / (11 * lam)
      - EmajTau c S a eta tau ≤ 0 := by
  have hN : 0 < (10:ℕ) := by norm_num
  have ha0 : 0 < a := lt_of_lt_of_le halpha0 h0
  have ha1 : a ≤ 1 := le_trans h1 hbeta1
  have hbeta0 : (0:ℝ) ≤ beta := by linarith
  -- key + `u ≥ λ`
  have hloc' : ((10:ℕ):ℝ) ≤ ((10:ℕ):ℝ) * a * mu.re + (1 - a ^ 2) * sigma := by
    exact_mod_cast hloc
  have hkey' : ((10:ℕ):ℝ) - S + S * a ^ 2 ≤ ((10:ℕ):ℝ) * a * mu.re :=
    key_of_loc ha1 ha0.le hloc' hsig
  have hkey : (10:ℝ) - S + S * a ^ 2 ≤ 10 * a * mu.re := by exact_mod_cast hkey'
  have hL' : 0 ≤ S * a ^ 2 - ((10:ℕ):ℝ) * lam * a + ((10:ℕ):ℝ) - S := by
    exact_mod_cast hL
  have hLkey : (10:ℝ) * a * lam ≤ 10 - S + S * a ^ 2 := by nlinarith [hL]
  have hlamu : lam ≤ mu.re := lam_le_u hN ha0 hkey' hL'
  have hmunorm : lam ≤ ‖mu‖ := lam_le_norm mu hlamu
  have hmu0 : mu ≠ 0 := by
    intro hcon
    rw [hcon] at hmunorm
    simp at hmunorm
    linarith
  -- `η < 1`
  have hetale : eta ^ 2 ≤ 1 - lam ^ 2 := eta_sq_le mu hlam0.le hnormSq hmunorm
  have heta1 : eta < 1 := by nlinarith
  -- `|I − J| ≤ EmajTau`
  have hIJ := norm_I_sub_J_le_EmajTau c hcnn mu D ha0 h1 hbeta0 heta0 htau0 htau1
    hnormSq hkey hLkey h2lb hz hY1 hc
  -- `|J| ≥ 1/11 + η²/22 − hh⁵/(11λ)`
  have hnormsq' : ‖mu‖ ^ 2 = 1 - eta ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; exact hnormSq
  have hJ0 := JBoundN.norm_J_ge hmu0 (n := 11) (by norm_num) a eta hnormsq'
    heta0 heta1
  have hRsq : ‖1 - (a : ℂ) * mu‖ ^ 2 ≤ hh 10 S a eta :=
    R_sq_le_h hN mu hnormSq hkey'
  have hh0 : 0 ≤ hh 10 S a eta := h_nonneg hN mu hnormSq hkey'
  have hLkey' : ((10:ℕ):ℝ) * a * lam ≤ ((10:ℕ):ℝ) - S + S * a ^ 2 := by
    exact_mod_cast hLkey
  have hh1 : hh 10 S a eta ≤ 1 := h_le_one hN ha0.le h1 hbeta0 hLkey' h2lb
  have hterm := J_term_le (R := ‖1 - (a : ℂ) * mu‖) (h := hh 10 S a eta)
    (lam := lam) (n := 11) (by norm_num) mu hlam0 (norm_nonneg _) hh0 hh1 hRsq
    hmunorm
  have hJcf := JBoundN.J_closed_form_deg11 hmu0 a
  have hJ : 1 / 11 + eta ^ 2 / 22 - hh 10 S a eta ^ 5 / (11 * lam)
      ≤ ‖∫ t in (0:ℝ)..a, ((1:ℂ) - (t:ℂ) * mu) ^ 10‖ := by
    rw [hJcf]
    push_cast at hJ0 hterm ⊢
    linarith [hJ0, hterm]
  -- triangle
  have htri : ‖∫ t in (0:ℝ)..a, ((1:ℂ) - (t:ℂ) * mu) ^ 10‖
      - ‖(∫ t in (0:ℝ)..a, ∏ j, ((1:ℂ) - (t:ℂ) * (mu + D j)))
          - (∫ t in (0:ℝ)..a, ((1:ℂ) - (t:ℂ) * mu) ^ 10)‖
      ≤ ‖∫ t in (0:ℝ)..a, ∏ j, ((1:ℂ) - (t:ℂ) * (mu + D j))‖ := by
    have h := norm_sub_norm_le
      (∫ t in (0:ℝ)..a, ((1:ℂ) - (t:ℂ) * mu) ^ 10)
      (∫ t in (0:ℝ)..a, ∏ j, ((1:ℂ) - (t:ℂ) * (mu + D j)))
    rw [norm_sub_rev] at h
    linarith
  -- close
  have hchain := chain_nonpos (n := 11) (by norm_num)
    (a := a) (eta := eta)
    (nI := ‖∫ t in (0:ℝ)..a, ∏ j, ((1:ℂ) - (t:ℂ) * (mu + D j))‖)
    (nJ := ‖∫ t in (0:ℝ)..a, ((1:ℂ) - (t:ℂ) * mu) ^ 10‖)
    (nIJ := ‖(∫ t in (0:ℝ)..a, ∏ j, ((1:ℂ) - (t:ℂ) * (mu + D j)))
      - (∫ t in (0:ℝ)..a, ((1:ℂ) - (t:ℂ) * mu) ^ 10)‖)
    (E := EmajTau c S a eta tau) (lam := lam) (h := hh 10 S a eta)
    htri (by push_cast; exact hI) hIJ
    (by push_cast; push_cast at hJ; linarith [hJ])
  push_cast at hchain
  linarith [hchain]

end SendovN.Split11

#print axioms SendovN.Split11.qt1_at
#print axioms SendovN.Split11.integral_scale_ab
#print axioms SendovN.Split11.integral_term_tau
#print axioms SendovN.Split11.G_tail_bound
#print axioms SendovN.Split11.J_pow_tail_le
#print axioms SendovN.Split11.norm_integral_le_of_norm_le_on
#print axioms SendovN.Split11.norm_I_sub_J_le_EmajTau
#print axioms SendovN.Split11.split_row_nonpos
