import Mathlib
import SendovNSigma
import SendovNJBound

set_option maxHeartbeats 4000000

/-!
# P8: `MidChainN` — the parametric row chain for degrees 10 and 11

Port of `Sendov9/{MidAnalytic, MidMajorant, MidPointwise, MidRow, MidWiring,
IminusJ}` in one file, parametric in `N` (= n − 1 ∈ {9, 10}) and in the constant
table `c : ℕ → ℝ` (supplied per degree by `SendovNEsp10/11`).  Division-free
forms throughout: the key inequality is `N − S + Sa² ≤ Nau` (that is
`u ≥ L_S(a)` with denominators cleared), the row `L`-bound is
`0 ≤ Sa² − Nλa + N − S`.

Main definitions/statements (`n = N + 1`, `k = n/2 = 5`, `ℓₘ = ⌊(N−m)/2⌋`):

* `q0 N S a η v = 1 − (2(N−S+Sa²)/N)v + a²(1−η²)v²` — the interior majorant;
* `hh N S a η = (2S/N − 1)(1−a²) − a²η²` — its value at `v = 1`;
* `Emaj N c S a η = ∑_{m=2}^{N} cₘ ηᵐ a^{m+1} ∫₀¹ vᵐ q0^{ℓₘ} dv`;
* `norm_I_sub_J_le_E` — `|I − J| ≤ Emaj` at feasible points;
* `row_nonpos` — **the reshaped Proposition 4.1**: instead of certificate ⟹
  `False`, conclude `P(a,η) ≤ 0` where
  `P a η = (1−a)/n + η²/(2n) − hh⁵/(nλ) − Emaj` — exactly the closed form the
  boxes' `principal + full_cert` polynomial dominates (`CertificateReduction`
  shape).  The `J` closed form is carried as a hypothesis `hJcf` (supplied per
  degree by `JBoundN.J_closed_form_deg10/11`).

`R^n ≤ h⁵` needs `10 ≤ n`, i.e. `9 ≤ N` — both target degrees qualify; no
fractional powers appear anywhere.
-/

namespace SendovN.MidChainN

open Finset intervalIntegral

/-- `q_S(a,η;v)` at degree `n = N+1` — the verifiers' `q_poly`. -/
noncomputable def q0 (N : ℕ) (S a eta v : ℝ) : ℝ :=
  1 - (2 * ((N : ℝ) - S + S * a ^ 2) / (N : ℝ)) * v + a ^ 2 * (1 - eta ^ 2) * v ^ 2

/-- `h_S(a,η)` at degree `n = N+1` — the verifiers' `h`. -/
noncomputable def hh (N : ℕ) (S a eta : ℝ) : ℝ :=
  (2 * S / (N : ℝ) - 1) * (1 - a ^ 2) - a ^ 2 * eta ^ 2

/-- The exponent table `ℓₘ = ⌊(N−m)/2⌋` (the paper's rounding-down of
half-integral powers). -/
def ell (N m : ℕ) : ℕ := (N - m) / 2

/-- `2ℓₘ ≤ N − m` always: the surplus `‖w‖` factors can be discarded. -/
theorem ell_ok (N : ℕ) : ∀ m ∈ Finset.Icc 2 N, 2 * ell N m ≤ N - m := by
  intro m _
  unfold ell
  omega

/-- The majorant in `t` (before the substitution `t = av`). -/
noncomputable def qt (N : ℕ) (S a eta t : ℝ) : ℝ :=
  1 - (2 * ((N : ℝ) - S + S * a ^ 2) / ((N : ℝ) * a)) * t + (1 - eta ^ 2) * t ^ 2

/-- `E_S(a,η)`: the integrated majorant, in the shape the certificates use. -/
noncomputable def Emaj (N : ℕ) (c : ℕ → ℝ) (S a eta : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 N, c m * eta ^ m * (a ^ (m + 1)
    * ∫ v in (0:ℝ)..1, v ^ m * q0 N S a eta v ^ ell N m)

/-! ### The scalar layer (port of `MidAnalytic`) -/

/-- `h` is `q0` at `v = 1` (needs `N ≠ 0` for the division). -/
theorem h_eq_q0_one {N : ℕ} (hN : 0 < N) (S a eta : ℝ) :
    hh N S a eta = q0 N S a eta 1 := by
  have hNne : ((N : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hN
  unfold hh q0
  field_simp
  ring

/-- `‖1 - tμ‖² = 1 - 2tu + t²‖μ‖²`, with `u = μ.re`. -/
theorem normSq_one_sub (mu : ℂ) (t : ℝ) :
    Complex.normSq (1 - (t : ℂ) * mu)
      = 1 - 2 * t * mu.re + t ^ 2 * Complex.normSq mu := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- Localization + `σ ≤ S` gives the division-free key `N − S + Sa² ≤ Nau`. -/
theorem key_of_loc {N : ℕ} {a u sigma S : ℝ} (ha1 : a ≤ 1) (ha0 : 0 ≤ a)
    (hloc : (N : ℝ) ≤ (N : ℝ) * a * u + (1 - a ^ 2) * sigma) (hsig : sigma ≤ S) :
    (N : ℝ) - S + S * a ^ 2 ≤ (N : ℝ) * a * u := by
  have hsq : (0:ℝ) ≤ 1 - a ^ 2 := by nlinarith
  nlinarith [mul_nonneg hsq (sub_nonneg.mpr hsig)]

/-- `u ≥ λ` from the row's `L`-bound `0 ≤ Sa² − Nλa + N − S`. -/
theorem lam_le_u {N : ℕ} (hN : 0 < N) {a u S lam : ℝ} (ha0 : 0 < a)
    (hkey : (N : ℝ) - S + S * a ^ 2 ≤ (N : ℝ) * a * u)
    (hL : 0 ≤ S * a ^ 2 - (N : ℝ) * lam * a + (N : ℝ) - S) : lam ≤ u := by
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNa : (0:ℝ) < (N : ℝ) * a := mul_pos hNpos ha0
  have h : (N : ℝ) * a * lam ≤ (N : ℝ) * a * u := by nlinarith [hL, hkey]
  exact le_of_mul_le_mul_left h hNa

/-- **The pointwise majorant.**  At `t = av`, `|1 − tμ|² ≤ q0(v)`. -/
theorem normSq_le_q {N : ℕ} (hN : 0 < N) {a eta S v : ℝ} (mu : ℂ) (hv0 : 0 ≤ v)
    (heta : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : (N : ℝ) - S + S * a ^ 2 ≤ (N : ℝ) * a * mu.re) :
    Complex.normSq (1 - ((a * v : ℝ) : ℂ) * mu) ≤ q0 N S a eta v := by
  rw [normSq_one_sub, heta]
  unfold q0
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdiv : 2 * ((N : ℝ) - S + S * a ^ 2) / (N : ℝ) ≤ 2 * (a * mu.re) := by
    rw [div_le_iff₀ hNpos]
    nlinarith [hkey]
  nlinarith [mul_le_mul_of_nonneg_right hdiv hv0]

/-- `0 ≤ q0` — because it dominates a square (needs a feasible `μ`). -/
theorem q0_nonneg {N : ℕ} (hN : 0 < N) {a eta S v : ℝ} (mu : ℂ) (hv0 : 0 ≤ v)
    (heta : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : (N : ℝ) - S + S * a ^ 2 ≤ (N : ℝ) * a * mu.re) :
    0 ≤ q0 N S a eta v :=
  le_trans (Complex.normSq_nonneg _) (normSq_le_q hN mu hv0 heta hkey)

/-- `q0 ≤ 1` at feasible points, driven by the row's `L`-bound. -/
theorem q0_le_one {N : ℕ} (hN : 0 < N) {a eta S lam beta v : ℝ} (ha0 : 0 ≤ a)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hab : a ≤ beta) (hbeta : 0 ≤ beta)
    (hL : (N : ℝ) * a * lam ≤ (N : ℝ) - S + S * a ^ 2) (h2lb : beta ≤ 2 * lam) :
    q0 N S a eta v ≤ 1 := by
  unfold q0
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hav : a * v ≤ beta := by nlinarith
  have hprod : (0:ℝ) ≤ a * v := mul_nonneg ha0 hv0
  have e1 : a ^ 2 * (1 - eta ^ 2) * v ^ 2 ≤ a ^ 2 * v ^ 2 := by
    nlinarith [sq_nonneg (a * v * eta)]
  have e2 : a ^ 2 * v ^ 2 ≤ a * beta * v := by
    nlinarith [mul_le_mul_of_nonneg_left hav hprod]
  have e3 : a * beta * v ≤ 2 * a * lam * v := by
    nlinarith [mul_le_mul_of_nonneg_left h2lb hprod]
  have e4 : 2 * a * lam * v ≤ (2 * ((N : ℝ) - S + S * a ^ 2) / (N : ℝ)) * v := by
    have hd : 2 * a * lam ≤ 2 * ((N : ℝ) - S + S * a ^ 2) / (N : ℝ) := by
      rw [le_div_iff₀ hNpos]
      nlinarith [hL]
    exact mul_le_mul_of_nonneg_right hd hv0
  linarith

/-- `R² ≤ h_S(a,η)` where `R = ‖1 − aμ‖`. -/
theorem R_sq_le_h {N : ℕ} (hN : 0 < N) {a eta S : ℝ} (mu : ℂ)
    (heta : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : (N : ℝ) - S + S * a ^ 2 ≤ (N : ℝ) * a * mu.re) :
    ‖1 - (a : ℂ) * mu‖ ^ 2 ≤ hh N S a eta := by
  have h1 := normSq_le_q (a := a) (eta := eta) (S := S) (v := 1) hN mu zero_le_one
    heta hkey
  rw [← h_eq_q0_one hN] at h1
  have h2 : ((a * 1 : ℝ) : ℂ) = (a : ℂ) := by push_cast; ring
  rw [h2] at h1
  rwa [Complex.normSq_eq_norm_sq] at h1

theorem h_nonneg {N : ℕ} (hN : 0 < N) {a eta S : ℝ} (mu : ℂ)
    (heta : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : (N : ℝ) - S + S * a ^ 2 ≤ (N : ℝ) * a * mu.re) :
    0 ≤ hh N S a eta :=
  le_trans (sq_nonneg _) (R_sq_le_h hN mu heta hkey)

theorem h_le_one {N : ℕ} (hN : 0 < N) {a eta S lam beta : ℝ} (ha0 : 0 ≤ a)
    (hab : a ≤ beta) (hbeta : 0 ≤ beta)
    (hL : (N : ℝ) * a * lam ≤ (N : ℝ) - S + S * a ^ 2) (h2lb : beta ≤ 2 * lam) :
    hh N S a eta ≤ 1 := by
  rw [h_eq_q0_one hN]
  exact q0_le_one hN ha0 zero_le_one le_rfl hab hbeta hL h2lb

/-- **`Rⁿ ≤ h⁵`** for `n ≥ 10`, via `R ≤ 1`: `Rⁿ ≤ R¹⁰ = (R²)⁵ ≤ h⁵`. -/
theorem Rn_le_h5 {R h : ℝ} {n : ℕ} (hn : 10 ≤ n) (hR0 : 0 ≤ R) (h0 : 0 ≤ h)
    (h1 : h ≤ 1) (hRh : R ^ 2 ≤ h) : R ^ n ≤ h ^ 5 := by
  have hR1 : R ≤ 1 := by nlinarith
  have hstep : R ^ n ≤ R ^ 10 := pow_le_pow_of_le_one hR0 hR1 hn
  have h10 : R ^ 10 = (R ^ 2) ^ 5 := by ring
  have hpow : (R ^ 2) ^ 5 ≤ h ^ 5 := pow_le_pow_left₀ (by positivity) hRh 5
  linarith

/-- **The term the certificate subtracts.**  `Rⁿ/(n‖μ‖) ≤ h⁵/(nλ)`. -/
theorem J_term_le {R h lam : ℝ} {n : ℕ} (hn : 10 ≤ n) (mu : ℂ) (hlam0 : 0 < lam)
    (hR0 : 0 ≤ R) (h0 : 0 ≤ h) (h1 : h ≤ 1) (hRh : R ^ 2 ≤ h)
    (hmu : lam ≤ ‖mu‖) :
    R ^ n / ((n : ℝ) * ‖mu‖) ≤ h ^ 5 / ((n : ℝ) * lam) := by
  have hRn : R ^ n ≤ h ^ 5 := Rn_le_h5 hn hR0 h0 h1 hRh
  have hnpos : (0:ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hlamn : (0:ℝ) < (n : ℝ) * lam := mul_pos hnpos hlam0
  have hmun : (0:ℝ) < (n : ℝ) * ‖mu‖ := mul_pos hnpos (lt_of_lt_of_le hlam0 hmu)
  calc R ^ n / ((n : ℝ) * ‖mu‖) ≤ h ^ 5 / ((n : ℝ) * ‖mu‖) :=
        div_le_div_of_nonneg_right hRn hmun.le
    _ ≤ h ^ 5 / ((n : ℝ) * lam) := by
        apply div_le_div_of_nonneg_left (by positivity) hlamn
        exact mul_le_mul_of_nonneg_left hmu hnpos.le

/-- `λ ≤ ‖μ‖`, from `λ ≤ Re μ ≤ ‖μ‖`. -/
theorem lam_le_norm {lam : ℝ} (mu : ℂ) (h : lam ≤ mu.re) : lam ≤ ‖mu‖ :=
  le_trans h (Complex.re_le_norm mu)

/-- `η ≤ Y` from `η² ≤ 1 − λ²` and `Y² ≥ 1 − λ²` (the certificate's `V`-range). -/
theorem eta_le_Y {eta Y lam : ℝ} (hY0 : 0 ≤ Y) (he0 : 0 ≤ eta)
    (heta : eta ^ 2 ≤ 1 - lam ^ 2) (hYc : 1 - lam ^ 2 ≤ Y ^ 2) : eta ≤ Y := by
  nlinarith

/-- `η² ≤ 1 − λ²`, from `η² = 1 − ‖μ‖²` and `λ ≤ ‖μ‖`. -/
theorem eta_sq_le {eta lam : ℝ} (mu : ℂ) (hlam0 : 0 ≤ lam)
    (heta : Complex.normSq mu = 1 - eta ^ 2) (hmu : lam ≤ ‖mu‖) :
    eta ^ 2 ≤ 1 - lam ^ 2 := by
  rw [Complex.normSq_eq_norm_sq] at heta
  nlinarith [heta, hmu, hlam0, norm_nonneg mu]

/-! ### The substitution `t = av` (port of `MidMajorant`) -/

theorem continuous_qt (N : ℕ) (S a eta : ℝ) : Continuous (qt N S a eta) := by
  unfold qt
  fun_prop

/-- **The substitution, pointwise.**  `qt(av) = q0(v)`. -/
theorem qt_at {N : ℕ} (hN : 0 < N) (S a eta v : ℝ) (ha : a ≠ 0) :
    qt N S a eta (a * v) = q0 N S a eta v := by
  have hNne : ((N : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hN
  unfold qt q0
  field_simp

/-- `∫₀ᵃ f = a ∫₀¹ f(a·)`. -/
theorem integral_scale (a : ℝ) (f : ℝ → ℝ) :
    (∫ t in (0:ℝ)..a, f t) = a * ∫ v in (0:ℝ)..1, f (a * v) := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := (1:ℝ))
    (f := f) a
  simp only [smul_eq_mul, mul_zero, mul_one] at h
  exact h.symm

/-- **The change of variables that produces `Emaj`'s `a^{m+1}`.** -/
theorem integral_term {N : ℕ} (hN : 0 < N) (S a eta : ℝ) (ha : 0 < a) (m l : ℕ) :
    (∫ t in (0:ℝ)..a, t ^ m * qt N S a eta t ^ l)
      = a ^ (m + 1) * ∫ v in (0:ℝ)..1, v ^ m * q0 N S a eta v ^ l := by
  rw [integral_scale a (fun t => t ^ m * qt N S a eta t ^ l)]
  have hcongr : ∀ v : ℝ, (a * v) ^ m * qt N S a eta (a * v) ^ l
      = a ^ m * (v ^ m * q0 N S a eta v ^ l) := by
    intro v
    rw [qt_at hN S a eta v (ne_of_gt ha), mul_pow]
    ring
  simp only [hcongr]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- `‖1 − tμ‖² ≤ qt(t)` for `t ≥ 0`. -/
theorem normSq_le_qt {N : ℕ} (hN : 0 < N) {a eta S t : ℝ} (mu : ℂ) (ha : 0 < a)
    (ht0 : 0 ≤ t) (heta : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : (N : ℝ) - S + S * a ^ 2 ≤ (N : ℝ) * a * mu.re) :
    Complex.normSq (1 - (t : ℂ) * mu) ≤ qt N S a eta t := by
  rw [normSq_one_sub, heta]
  unfold qt
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNa : (0:ℝ) < (N : ℝ) * a := mul_pos hNpos ha
  have hdiv : 2 * ((N : ℝ) - S + S * a ^ 2) / ((N : ℝ) * a) ≤ 2 * mu.re := by
    rw [div_le_iff₀ hNa]
    nlinarith [hkey]
  nlinarith [mul_le_mul_of_nonneg_right hdiv ht0]

/-- `qt(t) ≤ 1` on `[0,a]`, inherited from `q0 ≤ 1` through `t = av`. -/
theorem qt_le_one {N : ℕ} (hN : 0 < N) {a eta S lam beta t : ℝ} (ha : 0 < a)
    (ht0 : 0 ≤ t) (hta : t ≤ a) (hab : a ≤ beta) (hbeta : 0 ≤ beta)
    (hL : (N : ℝ) * a * lam ≤ (N : ℝ) - S + S * a ^ 2) (h2lb : beta ≤ 2 * lam) :
    qt N S a eta t ≤ 1 := by
  have hv0 : 0 ≤ t / a := div_nonneg ht0 (le_of_lt ha)
  have hv1 : t / a ≤ 1 := by
    rw [div_le_one ha]
    exact hta
  have hback : a * (t / a) = t := by field_simp
  have h := q0_le_one (a := a) (eta := eta) (S := S) (lam := lam) (beta := beta)
    (v := t / a) hN ha.le hv0 hv1 hab hbeta hL h2lb
  rw [← qt_at hN S a eta (t / a) (ne_of_gt ha), hback] at h
  exact h

/-- `0 ≤ qt(t)` for `t ≥ 0`. -/
theorem qt_nonneg {N : ℕ} (hN : 0 < N) {a eta S t : ℝ} (mu : ℂ) (ha : 0 < a)
    (ht0 : 0 ≤ t) (heta : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : (N : ℝ) - S + S * a ^ 2 ≤ (N : ℝ) * a * mu.re) :
    0 ≤ qt N S a eta t :=
  le_trans (Complex.normSq_nonneg _) (normSq_le_qt hN mu ha ht0 heta hkey)

/-! ### The integral layer (port of `IminusJ`, generic in `N`) -/

/-- `I − J` is the integral of the pointwise difference. -/
theorem sub_eq_integral_sub (a : ℝ) (F G : ℝ → ℂ)
    (hF : IntervalIntegrable F MeasureTheory.volume 0 a)
    (hG : IntervalIntegrable G MeasureTheory.volume 0 a) :
    (∫ t in (0:ℝ)..a, F t) - (∫ t in (0:ℝ)..a, G t)
      = ∫ t in (0:ℝ)..a, (F t - G t) := (integral_sub hF hG).symm

/-- Bounding a ℂ-valued integral by the integral of a real majorant of its norm. -/
theorem norm_integral_le_of_norm_le {a : ℝ} (ha : 0 ≤ a) (H : ℝ → ℂ) (b : ℝ → ℝ)
    (hH : IntervalIntegrable H MeasureTheory.volume 0 a)
    (hb : IntervalIntegrable b MeasureTheory.volume 0 a)
    (hle : ∀ t ∈ Set.Icc (0:ℝ) a, ‖H t‖ ≤ b t) :
    ‖∫ t in (0:ℝ)..a, H t‖ ≤ ∫ t in (0:ℝ)..a, b t := by
  have h1 : ‖∫ t in (0:ℝ)..a, H t‖ ≤ ∫ t in (0:ℝ)..a, ‖H t‖ :=
    norm_integral_le_integral_norm ha
  have h2 : (∫ t in (0:ℝ)..a, ‖H t‖) ≤ ∫ t in (0:ℝ)..a, b t := by
    apply integral_mono_on ha hH.norm hb
    intro t ht
    exact hle t ht
  linarith

/-- The majorant `∑_{m=2}^{N} cₘ ηᵐ tᵐ q(t)^{ℓₘ}` integrates termwise. -/
theorem integral_majorant (N : ℕ) (a : ℝ) (c : ℕ → ℝ) (eta : ℝ) (q : ℝ → ℝ)
    (l : ℕ → ℕ) (hq : Continuous q) :
    (∫ t in (0:ℝ)..a, ∑ m ∈ Finset.Icc 2 N, c m * eta ^ m * (t ^ m * q t ^ (l m)))
      = ∑ m ∈ Finset.Icc 2 N,
          c m * eta ^ m * ∫ t in (0:ℝ)..a, (t ^ m * q t ^ (l m)) := by
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun m _ => by
      rw [← integral_const_mul]
  · intro m _
    apply Continuous.intervalIntegrable
    fun_prop

/-- Given the pointwise tail bound, `|I − J|` is bounded by the integrated
majorant. -/
theorem norm_I_sub_J_le {a : ℝ} (ha : 0 ≤ a) (F G : ℝ → ℂ) (b : ℝ → ℝ)
    (hF : IntervalIntegrable F MeasureTheory.volume 0 a)
    (hG : IntervalIntegrable G MeasureTheory.volume 0 a)
    (hb : IntervalIntegrable b MeasureTheory.volume 0 a)
    (hle : ∀ t ∈ Set.Icc (0:ℝ) a, ‖F t - G t‖ ≤ b t) :
    ‖(∫ t in (0:ℝ)..a, F t) - (∫ t in (0:ℝ)..a, G t)‖ ≤ ∫ t in (0:ℝ)..a, b t := by
  rw [sub_eq_integral_sub a F G hF hG]
  exact norm_integral_le_of_norm_le ha (fun t => F t - G t) b (hF.sub hG) hb hle

/-- `‖w‖^e ≤ q^l` whenever `‖w‖² ≤ q ≤ 1` and `2l ≤ e` (rounding down
half-integral powers). -/
theorem pow_le_q_pow {w q : ℝ} {e l : ℕ} (hw : 0 ≤ w) (hwq : w ^ 2 ≤ q)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hle : 2 * l ≤ e) :
    w ^ e ≤ q ^ l := by
  have hw1 : w ≤ 1 := by nlinarith
  calc w ^ e ≤ w ^ (2 * l) := pow_le_pow_of_le_one hw hw1 hle
    _ = (w ^ 2) ^ l := pow_mul w 2 l
    _ ≤ q ^ l := pow_le_pow_left₀ (by positivity) hwq l

/-! ### The pointwise estimate and its integral (port of `MidPointwise`) -/

/-- **The pointwise estimate.**  For `0 ≤ t ≤ a`, the two integrands differ by at
most `∑ₘ cₘ ηᵐ tᵐ qt(t)^{ℓₘ}` — with the `c`-table carried as a hypothesis. -/
theorem pointwise {N : ℕ} (hN : 0 < N) {a eta S lam beta : ℝ} (c : ℕ → ℝ)
    (hcnn : ∀ m ∈ Finset.Icc 2 N, 0 ≤ c m)
    (mu : ℂ) (D : Fin N → ℂ)
    (ha : 0 < a) (hab : a ≤ beta) (hbeta : 0 ≤ beta) (heta0 : 0 ≤ eta)
    (hnormSq : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : (N : ℝ) - S + S * a ^ 2 ≤ (N : ℝ) * a * mu.re)
    (hL : (N : ℝ) * a * lam ≤ (N : ℝ) - S + S * a ^ 2) (h2lb : beta ≤ 2 * lam)
    (hz : ∑ j, D j = 0)
    (hc : ∀ m ∈ Finset.Icc 2 N, ‖esD D m‖ ≤ c m * eta ^ m)
    (t : ℝ) (ht0 : 0 ≤ t) (hta : t ≤ a) :
    ‖(∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j))) - ((1 : ℂ) - (t : ℂ) * mu) ^ N‖
      ≤ ∑ m ∈ Finset.Icc 2 N,
          c m * eta ^ m * (t ^ m * qt N S a eta t ^ ell N m) := by
  -- rewrite the product about the centre `w = 1 − tμ`
  have hfac : ∀ j : Fin N, (1 : ℂ) - (t : ℂ) * (mu + D j)
      = ((1 : ℂ) - (t : ℂ) * mu) - (t : ℂ) * D j := by
    intro j; ring
  rw [Finset.prod_congr rfl (fun j _ => hfac j),
    prod_sub_eq_head_add_tail hN ((1 : ℂ) - (t : ℂ) * mu) (t : ℂ) D hz]
  simp only [add_sub_cancel_left]
  -- the tail, bounded termwise by the `c`-table
  refine le_trans (norm_tail_le ((1 : ℂ) - (t : ℂ) * mu) (t : ℂ) D c eta hc) ?_
  have hnt : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_of_nonneg ht0]
  have hq0 : 0 ≤ qt N S a eta t := qt_nonneg hN mu ha ht0 hnormSq hkey
  have hq1 : qt N S a eta t ≤ 1 := qt_le_one hN ha ht0 hta hab hbeta hL h2lb
  have hwsq : ‖(1 : ℂ) - (t : ℂ) * mu‖ ^ 2 ≤ qt N S a eta t := by
    have h := normSq_le_qt (a := a) (eta := eta) (S := S) (t := t) hN mu ha ht0
      hnormSq hkey
    rwa [Complex.normSq_eq_norm_sq] at h
  refine Finset.sum_le_sum fun m hm => ?_
  have hle : 2 * ell N m ≤ N - m := ell_ok N m hm
  have hpow : ‖(1 : ℂ) - (t : ℂ) * mu‖ ^ (N - m) ≤ qt N S a eta t ^ ell N m :=
    pow_le_q_pow (norm_nonneg _) hwsq hq0 hq1 hle
  have hcc : 0 ≤ c m * eta ^ m := mul_nonneg (hcnn m hm) (by positivity)
  rw [hnt]
  have hstep : t ^ m * ‖(1 : ℂ) - (t : ℂ) * mu‖ ^ (N - m) * (c m * eta ^ m)
      ≤ t ^ m * qt N S a eta t ^ ell N m * (c m * eta ^ m) := by
    apply mul_le_mul_of_nonneg_right _ hcc
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  calc t ^ m * ‖(1 : ℂ) - (t : ℂ) * mu‖ ^ (N - m) * (c m * eta ^ m)
      ≤ t ^ m * qt N S a eta t ^ ell N m * (c m * eta ^ m) := hstep
    _ = c m * eta ^ m * (t ^ m * qt N S a eta t ^ ell N m) := by ring

/-- **`|I − J| ≤ Emaj N c S a η`** at feasible points. -/
theorem norm_I_sub_J_le_E {N : ℕ} (hN : 0 < N) {a eta S lam beta : ℝ} (c : ℕ → ℝ)
    (hcnn : ∀ m ∈ Finset.Icc 2 N, 0 ≤ c m)
    (mu : ℂ) (D : Fin N → ℂ)
    (ha : 0 < a) (hab : a ≤ beta) (hbeta : 0 ≤ beta) (heta0 : 0 ≤ eta)
    (hnormSq : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : (N : ℝ) - S + S * a ^ 2 ≤ (N : ℝ) * a * mu.re)
    (hL : (N : ℝ) * a * lam ≤ (N : ℝ) - S + S * a ^ 2) (h2lb : beta ≤ 2 * lam)
    (hz : ∑ j, D j = 0)
    (hc : ∀ m ∈ Finset.Icc 2 N, ‖esD D m‖ ≤ c m * eta ^ m) :
    ‖(∫ t in (0:ℝ)..a, ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j)))
        - (∫ t in (0:ℝ)..a, ((1 : ℂ) - (t : ℂ) * mu) ^ N)‖
      ≤ Emaj N c S a eta := by
  have hcontq := continuous_qt N S a eta
  have hbcont : Continuous (fun t : ℝ =>
      ∑ m ∈ Finset.Icc 2 N, c m * eta ^ m * (t ^ m * qt N S a eta t ^ ell N m)) := by
    apply continuous_finset_sum
    intro m _
    exact ((continuous_pow m).mul (hcontq.pow (ell N m))).const_mul (c m * eta ^ m)
  have hFcont : Continuous (fun t : ℝ => ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j))) := by
    fun_prop
  have hGcont : Continuous (fun t : ℝ => ((1 : ℂ) - (t : ℂ) * mu) ^ N) := by
    fun_prop
  have hbound := norm_I_sub_J_le (le_of_lt ha)
    (fun t : ℝ => ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j)))
    (fun t : ℝ => ((1 : ℂ) - (t : ℂ) * mu) ^ N)
    (fun t : ℝ => ∑ m ∈ Finset.Icc 2 N,
      c m * eta ^ m * (t ^ m * qt N S a eta t ^ ell N m))
    (hFcont.intervalIntegrable _ _) (hGcont.intervalIntegrable _ _)
    (hbcont.intervalIntegrable _ _)
    (fun t ht => pointwise hN c hcnn mu D ha hab hbeta heta0 hnormSq hkey hL h2lb
      hz hc t ht.1 ht.2)
  refine le_trans hbound (le_of_eq ?_)
  rw [integral_majorant N a c eta (qt N S a eta) (ell N) hcontq]
  unfold Emaj
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_term hN S a eta ha m (ell N m)]

/-! ### The closing chain (port of `MidWiring` + `MidRow`, reshaped to `P ≤ 0`) -/

/-- The pure-arithmetic close: the analytic bounds force `P(a,η) ≤ 0`. -/
theorem chain_nonpos {n : ℕ} (hn : 0 < n) {a eta nI nJ nIJ E lam h : ℝ}
    (htri : nJ - nIJ ≤ nI) (hI : nI < a / n) (hIJ : nIJ ≤ E)
    (hJ : 1 / n + eta ^ 2 / (2 * n) - h ^ 5 / (n * lam) ≤ nJ) :
    (1 - a) / n + eta ^ 2 / (2 * n) - h ^ 5 / (n * lam) - E ≤ 0 := by
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsplit : (1 - a) / (n : ℝ) = 1 / n - a / n := by ring
  linarith [htri, hI, hIJ, hJ]

/-- **The reshaped Proposition 4.1** (`row_excluded_to_nonpos`): at a feasible
counterexample point of the row, the certificate's closed form is nonpositive:
`(1−a)/n + η²/(2n) − hh⁵/(nλ) − Emaj ≤ 0`, `n = N + 1`.

The `J` closed form is carried as `hJcf` (per-degree:
`JBoundN.J_closed_form_deg10/11`); `|I| < a/n` is carried as `hI`
(from `BridgeN`/`DataN.norm_I_lt` at the counterexample). -/
theorem row_nonpos {N : ℕ} (hN9 : 9 ≤ N) {alpha beta S lam sigma : ℝ}
    (c : ℕ → ℝ) (hcnn : ∀ m ∈ Finset.Icc 2 N, 0 ≤ c m)
    (mu : ℂ) (D : Fin N → ℂ) (a eta : ℝ)
    (halpha0 : 0 < alpha) (hbeta1 : beta ≤ 1) (hlam0 : 0 < lam)
    (h2lb : beta ≤ 2 * lam)
    (h0 : alpha ≤ a) (h1 : a ≤ beta)
    (heta0 : 0 ≤ eta) (hnormSq : Complex.normSq mu = 1 - eta ^ 2)
    (hloc : (N : ℝ) ≤ (N : ℝ) * a * mu.re + (1 - a ^ 2) * sigma)
    (hsig : sigma ≤ S)
    (hL : 0 ≤ S * a ^ 2 - (N : ℝ) * lam * a + (N : ℝ) - S)
    (hz : ∑ j, D j = 0)
    (hc : ∀ m ∈ Finset.Icc 2 N, ‖esD D m‖ ≤ c m * eta ^ m)
    (hJcf : (∫ t in (0:ℝ)..a, ((1 : ℂ) - (t : ℂ) * mu) ^ N)
      = (1 - (1 - (a : ℂ) * mu) ^ (N + 1)) / (((N + 1 : ℕ) : ℂ) * mu))
    (hI : ‖∫ t in (0:ℝ)..a, ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j))‖
      < a / ((N : ℝ) + 1)) :
    (1 - a) / ((N : ℝ) + 1) + eta ^ 2 / (2 * ((N : ℝ) + 1))
      - hh N S a eta ^ 5 / (((N : ℝ) + 1) * lam) - Emaj N c S a eta ≤ 0 := by
  have hN : 0 < N := by omega
  have ha0 : 0 < a := lt_of_lt_of_le halpha0 h0
  have ha1 : a ≤ 1 := le_trans h1 hbeta1
  have hbeta0 : (0:ℝ) ≤ beta := by linarith
  -- localization ⇒ key; the row's `L`-bound ⇒ `u ≥ λ`
  have hkey : (N : ℝ) - S + S * a ^ 2 ≤ (N : ℝ) * a * mu.re :=
    key_of_loc ha1 ha0.le hloc hsig
  have hLkey : (N : ℝ) * a * lam ≤ (N : ℝ) - S + S * a ^ 2 := by nlinarith [hL]
  have hlamu : lam ≤ mu.re := lam_le_u hN ha0 hkey hL
  have hmunorm : lam ≤ ‖mu‖ := lam_le_norm mu hlamu
  have hmu0 : mu ≠ 0 := by
    intro hcon
    rw [hcon] at hmunorm
    simp at hmunorm
    linarith
  -- `η < 1`
  have hetale : eta ^ 2 ≤ 1 - lam ^ 2 := eta_sq_le mu hlam0.le hnormSq hmunorm
  have heta1 : eta < 1 := by nlinarith
  -- `|I − J| ≤ Emaj`
  have hIJ := norm_I_sub_J_le_E (a := a) (eta := eta) (S := S) (lam := lam)
    (beta := beta) hN c hcnn mu D ha0 h1 hbeta0 heta0 hnormSq hkey hLkey h2lb hz hc
  -- `|J| ≥ 1/n + η²/(2n) − hh⁵/(nλ)`
  have hnormsq' : ‖mu‖ ^ 2 = 1 - eta ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; exact hnormSq
  have hJ0 := JBoundN.norm_J_ge hmu0 (n := N + 1) (by omega) a eta hnormsq'
    heta0 heta1
  have hRsq : ‖1 - (a : ℂ) * mu‖ ^ 2 ≤ hh N S a eta :=
    R_sq_le_h hN mu hnormSq hkey
  have hh0 : 0 ≤ hh N S a eta := h_nonneg hN mu hnormSq hkey
  have hh1 : hh N S a eta ≤ 1 := h_le_one hN ha0.le h1 hbeta0 hLkey h2lb
  have hterm := J_term_le (R := ‖1 - (a : ℂ) * mu‖) (h := hh N S a eta)
    (lam := lam) (n := N + 1) (by omega) mu hlam0 (norm_nonneg _) hh0 hh1 hRsq
    hmunorm
  have hJ : 1 / ((N : ℝ) + 1) + eta ^ 2 / (2 * ((N : ℝ) + 1))
      - hh N S a eta ^ 5 / (((N : ℝ) + 1) * lam)
      ≤ ‖∫ t in (0:ℝ)..a, ((1 : ℂ) - (t : ℂ) * mu) ^ N‖ := by
    rw [hJcf]
    push_cast at hJ0 hterm ⊢
    linarith [hJ0, hterm]
  -- triangle inequality
  have htri : ‖∫ t in (0:ℝ)..a, ((1 : ℂ) - (t : ℂ) * mu) ^ N‖
      - ‖(∫ t in (0:ℝ)..a, ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j)))
          - (∫ t in (0:ℝ)..a, ((1 : ℂ) - (t : ℂ) * mu) ^ N)‖
      ≤ ‖∫ t in (0:ℝ)..a, ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j))‖ := by
    have h := norm_sub_norm_le
      (∫ t in (0:ℝ)..a, ((1 : ℂ) - (t : ℂ) * mu) ^ N)
      (∫ t in (0:ℝ)..a, ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j)))
    rw [norm_sub_rev] at h
    linarith
  -- close with the pure-arithmetic chain at `n = N + 1`
  have hchain := chain_nonpos (n := N + 1) (by omega)
    (a := a) (eta := eta)
    (nI := ‖∫ t in (0:ℝ)..a, ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j))‖)
    (nJ := ‖∫ t in (0:ℝ)..a, ((1 : ℂ) - (t : ℂ) * mu) ^ N‖)
    (nIJ := ‖(∫ t in (0:ℝ)..a, ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j)))
      - (∫ t in (0:ℝ)..a, ((1 : ℂ) - (t : ℂ) * mu) ^ N)‖)
    (E := Emaj N c S a eta) (lam := lam) (h := hh N S a eta)
    htri (by push_cast; exact hI) hIJ (by push_cast; exact hJ)
  push_cast at hchain
  linarith [hchain]

end SendovN.MidChainN

#print axioms SendovN.MidChainN.ell_ok
#print axioms SendovN.MidChainN.h_eq_q0_one
#print axioms SendovN.MidChainN.key_of_loc
#print axioms SendovN.MidChainN.lam_le_u
#print axioms SendovN.MidChainN.normSq_le_q
#print axioms SendovN.MidChainN.q0_nonneg
#print axioms SendovN.MidChainN.q0_le_one
#print axioms SendovN.MidChainN.R_sq_le_h
#print axioms SendovN.MidChainN.h_nonneg
#print axioms SendovN.MidChainN.h_le_one
#print axioms SendovN.MidChainN.Rn_le_h5
#print axioms SendovN.MidChainN.J_term_le
#print axioms SendovN.MidChainN.qt_at
#print axioms SendovN.MidChainN.integral_term
#print axioms SendovN.MidChainN.normSq_le_qt
#print axioms SendovN.MidChainN.qt_le_one
#print axioms SendovN.MidChainN.qt_nonneg
#print axioms SendovN.MidChainN.integral_majorant
#print axioms SendovN.MidChainN.norm_I_sub_J_le
#print axioms SendovN.MidChainN.pow_le_q_pow
#print axioms SendovN.MidChainN.pointwise
#print axioms SendovN.MidChainN.norm_I_sub_J_le_E
#print axioms SendovN.MidChainN.chain_nonpos
#print axioms SendovN.MidChainN.row_nonpos
