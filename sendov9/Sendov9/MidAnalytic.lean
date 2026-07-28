import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.MidAn

open Finset

/-!
# The `q` / `h` / `R` inequalities behind Proposition 4.1

Everything here is stated in the *division-free* form `8 - S + S a² ≤ 8 a u`, which is
`u ≥ L_S(a)` with the denominator cleared.  That is not cosmetic: `linarith` reads
`L_S(a) = (8 - S(1-a²))/(8a)` as an opaque atom, and every downstream step multiplies
through by `8a` anyway.

## What is proved

* `key_of_loc` — the localization inequality plus `σ ≤ S` gives `8 - S + Sa² ≤ 8au`.
* `lam_le_u` — with the row's `L`-bound `0 ≤ Sa² - 8λa + 8 - S`, that gives `u ≥ λ`.
* `normSq_le_q` — at `t = av`, `|1 - tμ|² ≤ q_S(a,η;v)`.  This is the whole point of
  `q`: it is the pointwise majorant of the integrand, uniform in the unknown `μ`.
* `q_nonneg` / `q_le_one` — **only at feasible points.**
* `h_eq_q_one` — `h_S(a,η) = q_S(a,η;1)`, so the `h` bounds are the `q` bounds at `v = 1`
  and need no separate argument.
* `R9_le_h4` — `R⁹ ≤ h⁴`, via `R ≤ 1` rather than the paper's half-integral
  `R⁹ ≤ h^{9/2} ≤ h⁴`.  Since `R⁹ ≤ R⁸ = (R²)⁴ ≤ h⁴`, no fractional power is needed
  anywhere in the formalization.
* `J_term_le` — `R⁹/(9‖μ‖) ≤ h⁴/(9λ)`, the term the certificate subtracts.

## The trap

`0 ≤ q ≤ 1` is **false on the box** `[α,β] × [0,Y]` — it was checked during refereeing
that `q(0.1, 1.4; 0.99) ≈ -3·10⁻⁴`, because `η ≤ Y` rounds up the true feasible bound
`η² ≤ 1 - λ²`.  So `q_nonneg` is derived *from* `|1-tμ|² ≤ q` (a square is nonnegative),
which only makes sense where a `μ` exists, and `q_le_one` carries the feasibility
hypotheses explicitly.  The certificate, correspondingly, asserts positivity of `P` on
the box — never anything about `q` there.

Sendov's conjecture in degree nine remains unproven.
-/

/-- `q_S(a,η;v)` — equation (4.2). -/
noncomputable def q (S a eta v : ℝ) : ℝ :=
  1 - ((8 - S + S * a ^ 2) / 4) * v + a ^ 2 * (1 - eta ^ 2) * v ^ 2

/-- `h_S(a,η)` — equation (4.3). -/
noncomputable def hh (S a eta : ℝ) : ℝ := (S / 4 - 1) * (1 - a ^ 2) - a ^ 2 * eta ^ 2

/-- **`h_S` is `q_S` at `v = 1`.**  This one line removes the need for any separate
argument about `h`: its lower and upper bounds are the `q` bounds specialized. -/
theorem h_eq_q_one (S a eta : ℝ) : hh S a eta = q S a eta 1 := by
  unfold hh q
  ring

/-- `‖1 - tμ‖² = 1 - 2tu + t²‖μ‖²`, with `u = μ.re`. -/
theorem normSq_one_sub (mu : ℂ) (t : ℝ) :
    Complex.normSq (1 - (t : ℂ) * mu) = 1 - 2 * t * mu.re + t ^ 2 * Complex.normSq mu := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The localization inequality, with the σ bound substituted.**

`8au + (1-a²)σ ≥ 8` and `σ ≤ S` give `8 - S + Sa² ≤ 8au` — which is `u ≥ L_S(a)` with
the denominator cleared. -/
theorem key_of_loc {a u sigma S : ℝ} (ha1 : a ≤ 1) (ha0 : 0 ≤ a)
    (hloc : 8 ≤ 8 * a * u + (1 - a ^ 2) * sigma) (hsig : sigma ≤ S) :
    8 - S + S * a ^ 2 ≤ 8 * a * u := by
  have hsq : (0:ℝ) ≤ 1 - a ^ 2 := by nlinarith
  nlinarith [hloc, hsig, hsq]

/-- **`u ≥ λ`**, from the row's `L`-bound `0 ≤ Sa² - 8λa + 8 - S`. -/
theorem lam_le_u {a u S lam : ℝ} (ha0 : 0 < a)
    (hkey : 8 - S + S * a ^ 2 ≤ 8 * a * u)
    (hL : 0 ≤ S * a ^ 2 - 8 * lam * a + 8 - S) : lam ≤ u := by
  have h8a : (0:ℝ) < 8 * a := by linarith
  have : 8 * a * lam ≤ 8 * a * u := by nlinarith
  exact le_of_mul_le_mul_left (by linarith) h8a

/-- **The pointwise majorant.**  At `t = av`, `|1 - tμ|² ≤ q_S(a,η;v)`.

This is the inequality the whole `|I - J|` estimate rests on: `q` is an explicit
polynomial dominating the integrand uniformly in the unknown `μ`. -/
theorem normSq_le_q {a eta S v : ℝ} (mu : ℂ) (hv0 : 0 ≤ v)
    (heta : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : 8 - S + S * a ^ 2 ≤ 8 * a * mu.re) :
    Complex.normSq (1 - ((a * v : ℝ) : ℂ) * mu) ≤ q S a eta v := by
  rw [normSq_one_sub, heta]
  unfold q
  nlinarith [hkey, hv0]

/-- `0 ≤ q_S(a,η;v)` — because it dominates a square.  Needs a `μ`, hence the
hypotheses; the statement is **false** on the certificate's box without them. -/
theorem q_nonneg {a eta S v : ℝ} (mu : ℂ) (hv0 : 0 ≤ v)
    (heta : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : 8 - S + S * a ^ 2 ≤ 8 * a * mu.re) :
    0 ≤ q S a eta v :=
  le_trans (Complex.normSq_nonneg _) (normSq_le_q mu hv0 heta hkey)

/-- `q_S(a,η;v) ≤ 1` at feasible points.

The chain is `a²(1-η²)v² ≤ a²v² ≤ aβv ≤ 2aλv ≤ ((8-S+Sa²)/4)v`, which is the paper's
`q - 1 ≤ av(-2λ + β) ≤ 0` written out.  Note the driving hypothesis is the **row's
`L`-bound** `8aλ ≤ 8 - S + Sa²` (i.e. `L_S(a) ≥ λ`), not the localization inequality —
the two point in opposite directions and only the former bounds `q` above. -/
theorem q_le_one {a eta S lam beta v : ℝ} (ha0 : 0 ≤ a)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hab : a ≤ beta) (hbeta : 0 ≤ beta)
    (hL : 8 * a * lam ≤ 8 - S + S * a ^ 2) (h2lb : beta ≤ 2 * lam) :
    q S a eta v ≤ 1 := by
  unfold q
  have hav : a * v ≤ beta := by nlinarith
  have hprod : (0:ℝ) ≤ a * v := mul_nonneg ha0 hv0
  have e1 : a ^ 2 * (1 - eta ^ 2) * v ^ 2 ≤ a ^ 2 * v ^ 2 := by
    have hnn : (0:ℝ) ≤ a ^ 2 * v ^ 2 * eta ^ 2 := by positivity
    nlinarith [hnn]
  have e2 : a ^ 2 * v ^ 2 ≤ a * beta * v := by nlinarith [hprod, hav]
  have e3 : a * beta * v ≤ 2 * a * lam * v := by nlinarith [hprod, h2lb]
  have e4 : 2 * a * lam * v ≤ ((8 - S + S * a ^ 2) / 4) * v := by nlinarith [hL, hv0]
  linarith

/-! ### The `h` corollaries, all specializations at `v = 1` -/

/-- `R² ≤ h_S(a,η)` where `R = ‖1 - aμ‖`. -/
theorem R_sq_le_h {a eta S : ℝ} (mu : ℂ)
    (heta : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : 8 - S + S * a ^ 2 ≤ 8 * a * mu.re) :
    ‖1 - (a : ℂ) * mu‖ ^ 2 ≤ hh S a eta := by
  have h1 := normSq_le_q (a := a) (eta := eta) (S := S) (v := 1) mu zero_le_one heta hkey
  rw [← h_eq_q_one] at h1
  have h2 : ((a * 1 : ℝ) : ℂ) = (a : ℂ) := by push_cast; ring
  rw [h2] at h1
  rwa [Complex.normSq_eq_norm_sq] at h1

theorem h_nonneg {a eta S : ℝ} (mu : ℂ)
    (heta : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : 8 - S + S * a ^ 2 ≤ 8 * a * mu.re) :
    0 ≤ hh S a eta :=
  le_trans (sq_nonneg _) (R_sq_le_h mu heta hkey)

theorem h_le_one {a eta S lam beta : ℝ} (ha0 : 0 ≤ a)
    (hab : a ≤ beta) (hbeta : 0 ≤ beta)
    (hL : 8 * a * lam ≤ 8 - S + S * a ^ 2) (h2lb : beta ≤ 2 * lam) :
    hh S a eta ≤ 1 := by
  rw [h_eq_q_one]
  exact q_le_one ha0 zero_le_one le_rfl hab hbeta hL h2lb

/-- **`R⁹ ≤ h⁴`.**  The paper rounds `R⁹ ≤ h^{9/2} ≤ h⁴`; here `R ≤ 1` gives
`R⁹ ≤ R⁸ = (R²)⁴ ≤ h⁴` with no fractional power anywhere. -/
theorem R9_le_h4 {R h : ℝ} (hR0 : 0 ≤ R) (h0 : 0 ≤ h) (h1 : h ≤ 1) (hRh : R ^ 2 ≤ h) :
    R ^ 9 ≤ h ^ 4 := by
  have hR1 : R ≤ 1 := by nlinarith
  have hstep : R ^ 9 ≤ R ^ 8 := by
    calc R ^ 9 = R ^ 8 * R := by ring
      _ ≤ R ^ 8 * 1 := by
          exact mul_le_mul_of_nonneg_left hR1 (by positivity)
      _ = R ^ 8 := by ring
  have h8 : R ^ 8 = (R ^ 2) ^ 4 := by ring
  have hpow : (R ^ 2) ^ 4 ≤ h ^ 4 := pow_le_pow_left₀ (by positivity) hRh 4
  linarith [hstep, h8.le, h8.ge, hpow]

/-- **The term the certificate subtracts.**  `R⁹/(9‖μ‖) ≤ h⁴/(9λ)`, using `‖μ‖ ≥ u ≥ λ`. -/
theorem J_term_le {R h lam : ℝ} (mu : ℂ) (hlam0 : 0 < lam) (hR0 : 0 ≤ R)
    (h0 : 0 ≤ h) (h1 : h ≤ 1) (hRh : R ^ 2 ≤ h) (hmu : lam ≤ ‖mu‖) :
    R ^ 9 / (9 * ‖mu‖) ≤ h ^ 4 / (9 * lam) := by
  have hR9 : R ^ 9 ≤ h ^ 4 := R9_le_h4 hR0 h0 h1 hRh
  have hlam9 : (0:ℝ) < 9 * lam := by linarith
  have hmu9 : (0:ℝ) < 9 * ‖mu‖ := by linarith
  have hnum : (0:ℝ) ≤ R ^ 9 := by positivity
  calc R ^ 9 / (9 * ‖mu‖) ≤ h ^ 4 / (9 * ‖mu‖) := by
        exact div_le_div_of_nonneg_right hR9 hmu9.le
    _ ≤ h ^ 4 / (9 * lam) := by
        apply div_le_div_of_nonneg_left (by positivity) hlam9
        linarith

/-- `λ ≤ ‖μ‖`, from `λ ≤ μ.re ≤ ‖μ‖`. -/
theorem lam_le_norm {lam : ℝ} (mu : ℂ) (h : lam ≤ mu.re) : lam ≤ ‖mu‖ :=
  le_trans h (Complex.re_le_norm mu)

/-- `η ≤ Y` from `η² ≤ 1 - λ²` and `Y² ≥ 1 - λ²` — the `V`-range of the certificate. -/
theorem eta_le_Y {eta Y lam : ℝ} (hY0 : 0 ≤ Y) (he0 : 0 ≤ eta)
    (heta : eta ^ 2 ≤ 1 - lam ^ 2) (hYc : 1 - lam ^ 2 ≤ Y ^ 2) : eta ≤ Y := by
  nlinarith

/-- `η² ≤ 1 - λ²`, from `η² = 1 - ‖μ‖²` and `λ ≤ ‖μ‖`. -/
theorem eta_sq_le {eta lam : ℝ} (mu : ℂ) (hlam0 : 0 ≤ lam)
    (heta : Complex.normSq mu = 1 - eta ^ 2) (hmu : lam ≤ ‖mu‖) :
    eta ^ 2 ≤ 1 - lam ^ 2 := by
  rw [Complex.normSq_eq_norm_sq] at heta
  nlinarith [heta, hmu, hlam0, norm_nonneg mu]

end Sendov9.MidAn

#print axioms Sendov9.MidAn.h_eq_q_one
#print axioms Sendov9.MidAn.normSq_one_sub
#print axioms Sendov9.MidAn.key_of_loc
#print axioms Sendov9.MidAn.lam_le_u
#print axioms Sendov9.MidAn.normSq_le_q
#print axioms Sendov9.MidAn.q_nonneg
#print axioms Sendov9.MidAn.q_le_one
#print axioms Sendov9.MidAn.R_sq_le_h
#print axioms Sendov9.MidAn.h_nonneg
#print axioms Sendov9.MidAn.h_le_one
#print axioms Sendov9.MidAn.R9_le_h4
#print axioms Sendov9.MidAn.J_term_le
#print axioms Sendov9.MidAn.lam_le_norm
#print axioms Sendov9.MidAn.eta_le_Y
#print axioms Sendov9.MidAn.eta_sq_le
