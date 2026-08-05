import Mathlib
import Sendov9.MidAnalytic

set_option maxHeartbeats 4000000

namespace Sendov9.TopJ

open Finset

/-!
# The boundary range's `|J|` bound

Section 5 of the paper needs `|J| ≥ 1/9 + η²/18 - δ/1000`.  `Sigma22.norm_J_ge` already
supplies `|J| ≥ 1/9 + η²/18 - R⁹/(9|μ|)`, so what is left is

    R⁹/(9|μ|) ≤ δ/1000,      R = |1 - aμ|,  δ = 1 - a.

Two steps.

**`R_sq_le`** — `R² ≤ (19/10)δ`.  Expanding, `R² = δ² + (19/10)δ(1-δ) - (1-δ)²η²`, which
is the paper's display; dropping the (nonpositive) `η` term and using `δ² ≤ (19/10)δ²`
gives the bound.  This is where `Top.one_sub_u_le` is spent.

**`R9_le`** — the radical estimate, done **without fractional powers**.  The paper argues
`R⁹ ≤ ((19/10)δ)^{9/2}` and then checks `200²·19⁹ < 1629²·10¹⁰` after squaring.  Here the
squaring is the *only* step: `(1000R⁹)² = 10⁶(R²)⁹ ≤ 10⁶((19/10)δ)⁹` and
`(9|μ|δ)² ≥ 81(181/200)²δ²`, so the claim reduces to

    10⁶ (19/10)⁹ δ⁷ ≤ 81 (181/200)²      at δ ≤ 1/10,

i.e. `19⁹/10¹⁰ ≈ 32.27 ≤ 81·(181/200)² ≈ 66.34`.  That is `Top.radical_ineq` with room to
spare, and no `Real.rpow` appears anywhere.

`|μ| ≥ 181/200` is `Top.mu_ge` composed with `Complex.re_le_norm`.

Sendov's conjecture in degree nine remains unproven.
-/

/-- **`R² ≤ (19/10)δ`**, where `R = |1 - aμ|` and `a = 1 - δ`. -/
theorem R_sq_le {a delta eta u : ℝ} (mu : ℂ)
    (hdel : delta = 1 - a) (hd0 : 0 ≤ delta) (hd : delta ≤ 1/10)
    (hu : mu.re = u) (hnsq : Complex.normSq mu = 1 - eta ^ 2)
    (hone : 1 - u ≤ (19/20 : ℝ) * delta) :
    ‖1 - (a : ℂ) * mu‖ ^ 2 ≤ (19/10 : ℝ) * delta := by
  have hexp : Complex.normSq (1 - (a : ℂ) * mu)
      = 1 - 2 * a * mu.re + a ^ 2 * Complex.normSq mu := MidAn.normSq_one_sub mu a
  have hnorm : ‖1 - (a : ℂ) * mu‖ ^ 2 = Complex.normSq (1 - (a : ℂ) * mu) := by
    rw [Complex.normSq_eq_norm_sq]
  rw [hnorm, hexp, hnsq, hu]
  have ha : a = 1 - delta := by linarith
  subst ha
  nlinarith [sq_nonneg eta, sq_nonneg delta, sq_nonneg ((1 - delta) * eta), hone, hd0, hd]

/-- **`R⁹/(9|μ|) ≤ δ/1000`.**  Squared once; no fractional power appears. -/
theorem R9_le {delta R nmu : ℝ} (hd0 : 0 ≤ delta) (hd : delta ≤ 1/10)
    (hR0 : 0 ≤ R) (hRsq : R ^ 2 ≤ (19/10 : ℝ) * delta)
    (hmu : (181/200 : ℝ) ≤ nmu) :
    R ^ 9 / (9 * nmu) ≤ delta / 1000 := by
  have hmu0 : (0:ℝ) < nmu := by linarith
  have h9mu : (0:ℝ) < 9 * nmu := by linarith
  rw [div_le_div_iff₀ h9mu (by norm_num : (0:ℝ) < 1000)]
  -- goal: `R^9 * 1000 ≤ delta * (9 * nmu)`
  have hR2nn : (0:ℝ) ≤ R ^ 2 := sq_nonneg R
  have hpow9 : (R ^ 2) ^ 9 ≤ ((19/10 : ℝ) * delta) ^ 9 :=
    pow_le_pow_left₀ hR2nn hRsq 9
  have hlhs : (R ^ 9 * 1000) ^ 2 = 1000000 * (R ^ 2) ^ 9 := by ring
  have hd7 : delta ^ 7 ≤ (1/10 : ℝ) ^ 7 := pow_le_pow_left₀ hd0 hd 7
  -- `10^6 (19/10)^9 δ^9 ≤ 81 (181/200)^2 δ^2`, which is the squared claim
  have hkey : (R ^ 9 * 1000) ^ 2 ≤ (delta * (9 * nmu)) ^ 2 := by
    have h1 : 1000000 * ((19/10 : ℝ) * delta) ^ 9
        = 1000000 * (19/10 : ℝ) ^ 9 * delta ^ 7 * delta ^ 2 := by ring
    have h2 : (0:ℝ) ≤ delta ^ 2 := sq_nonneg delta
    -- `19⁹/10¹⁰ ≈ 32.27 ≤ 81(181/200)² ≈ 66.34` — hand it to `norm_num` as a closed
    -- rational comparison; `nlinarith` will not evaluate powers this large.
    have h3 : 1000000 * (19/10 : ℝ) ^ 9 * delta ^ 7 ≤ 81 * (181/200 : ℝ) ^ 2 := by
      have hc : (0:ℝ) ≤ 1000000 * (19/10 : ℝ) ^ 9 := by norm_num
      refine le_trans (mul_le_mul_of_nonneg_left hd7 hc) ?_
      norm_num
    have hnmu2 : (181/200 : ℝ) ^ 2 ≤ nmu ^ 2 := by nlinarith [hmu, hmu0]
    have h4 : (81 : ℝ) * (181/200) ^ 2 * delta ^ 2 ≤ (delta * (9 * nmu)) ^ 2 := by
      have hstep : (81 : ℝ) * (181/200) ^ 2 ≤ 81 * nmu ^ 2 := by linarith
      calc (81 : ℝ) * (181/200) ^ 2 * delta ^ 2
          = ((81 : ℝ) * (181/200) ^ 2) * delta ^ 2 := by ring
        _ ≤ ((81 : ℝ) * nmu ^ 2) * delta ^ 2 := mul_le_mul_of_nonneg_right hstep h2
        _ = (delta * (9 * nmu)) ^ 2 := by ring
    calc (R ^ 9 * 1000) ^ 2 = 1000000 * (R ^ 2) ^ 9 := hlhs
      _ ≤ 1000000 * ((19/10 : ℝ) * delta) ^ 9 :=
          mul_le_mul_of_nonneg_left hpow9 (by norm_num)
      _ = 1000000 * (19/10 : ℝ) ^ 9 * delta ^ 7 * delta ^ 2 := h1
      _ ≤ 81 * (181/200 : ℝ) ^ 2 * delta ^ 2 := mul_le_mul_of_nonneg_right h3 h2
      _ ≤ (delta * (9 * nmu)) ^ 2 := h4
  have hlhs0 : (0:ℝ) ≤ R ^ 9 * 1000 := by positivity
  have hrhs0 : (0:ℝ) ≤ delta * (9 * nmu) := by positivity
  nlinarith [hkey, hlhs0, hrhs0]

/-- `|μ| ≥ 181/200`, from `Top.mu_ge` through `Complex.re_le_norm`. -/
theorem norm_mu_ge {u delta : ℝ} (mu : ℂ) (hu : mu.re = u)
    (hd0 : 0 ≤ delta) (hd : delta ≤ 1/10) (hone : 1 - u ≤ (19/20 : ℝ) * delta) :
    (181/200 : ℝ) ≤ ‖mu‖ := by
  have h : (181/200 : ℝ) ≤ u := by nlinarith
  calc (181/200 : ℝ) ≤ u := h
    _ = mu.re := hu.symm
    _ ≤ ‖mu‖ := Complex.re_le_norm mu

end Sendov9.TopJ

#print axioms Sendov9.TopJ.R_sq_le
#print axioms Sendov9.TopJ.R9_le
#print axioms Sendov9.TopJ.norm_mu_ge
