import Mathlib
import SendovNSigma

set_option maxHeartbeats 1000000

/-!
# D10-3: the degree-10 small range `0 ≤ a ≤ 2/5` (two pieces)

Adapts `Sendov9/RangeSmall.lean` to degree 10 per the plan:

* **Piece (i), `0 ≤ a ≤ 29/100`** — the product bound: `∏ rₖ ≤ (1+a)⁹ ≤ (129/100)⁹ < 10`
  against `10 < ∏ rₖ` (`degree10_verify.py`'s `F(129,100)**9 < 10`).  This also
  disposes of `a = 0` (no separate `zero_excluded` needed).
* **Piece (ii), `29/100 ≤ a ≤ 2/5`** — Lemma σ with `M = 7/5` (`ν = 9`,
  exact `S₀ = 8·(5/7)² + ((7/5)⁸/10)² = 6.2595…`, dominated here by `63/10`),
  then localization forces `u > 1` through the quadratic
  `S₀a² − 9a + 9 − S₀ > 0`, contradicting `u ≤ ‖μ‖ < 1`.

Stated over the real quantities with plain numerals (`9`, `10`); the assembly
agent bridges `((n−1:ℕ):ℝ)` casts by `exact_mod_cast`/`push_cast`, as in
`SendovNSplit11.lean`.
-/

namespace SendovN.Small10

open Finset

/-- **Piece (i).**  `0 ≤ a ≤ 29/100` is impossible: the product of the root
distances is at most `(1+a)⁹ ≤ (129/100)⁹ < 10`. -/
theorem product_excluded {a : ℝ} {r : Fin 9 → ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 29/100)
    (hr0 : ∀ k, 0 ≤ r k) (hr : ∀ k, r k ≤ 1 + a) (hprod : 10 < ∏ k, r k) :
    False := by
  have h1 : ∏ k, r k ≤ (1 + a) ^ 9 := by
    calc ∏ k, r k ≤ ∏ _k : Fin 9, (1 + a) :=
          Finset.prod_le_prod (fun k _ => hr0 k) (fun k _ => hr k)
      _ = (1 + a) ^ 9 := by simp
  have h2 : (1 + a : ℝ) ^ 9 ≤ (129/100) ^ 9 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 9
  have h3 : ((129/100 : ℝ)) ^ 9 < 10 := by norm_num
  linarith

/-- Lemma σ at `M = 7/5` (`ν = 9`): on `a ≤ 2/5`, `σ ≤ 63/10`. -/
theorem sigma_small (r : Fin 9 → ℝ) (hlo : ∀ k, (309/500 : ℝ) ≤ r k)
    (hhi : ∀ k, r k ≤ 7/5) (hprod : (10:ℝ) ≤ ∏ k, r k) :
    ∑ k, 1 / r k ^ 2 ≤ 63/10 := by
  refine SigmaGen.sigma_le_of (m := (309/500 : ℝ)) (M := (7/5 : ℝ)) (C := 10) (nu := 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_ (by norm_num) r hlo hhi hprod
  intro j hj
  interval_cases j <;> norm_num

/-- The quadratic `S₀a² − 9a + 9 − S₀` with `S₀ = 63/10` is positive up to `2/5`
(its value at the right endpoint is `27/250`). -/
theorem quadratic_pos {a : ℝ} (h1 : a ≤ 2/5) :
    0 < (63/10 : ℝ) * a ^ 2 - 9 * a + 9 - 63/10 := by
  nlinarith [sq_nonneg (a - 2/5)]

/-- **The small-range contradiction** (steps 2–4 of the degree-9 pattern):
`σ ≤ S₀` + localization + the quadratic force `u > 1`. -/
theorem contradiction {a u sigma S0 : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hS : sigma ≤ S0)
    (hloc : 9 ≤ 9 * a * u + (1 - a ^ 2) * sigma)
    (hquad : 0 < S0 * a ^ 2 - 9 * a + 9 - S0)
    (hu : u < 1) : False := by
  have hsq : (0:ℝ) ≤ 1 - a ^ 2 := by nlinarith
  have h1 : 9 ≤ 9 * a * u + (1 - a ^ 2) * S0 := by nlinarith
  nlinarith

/-- **Piece (ii), packaged**: no configuration with `29/100 ≤ a ≤ 2/5` survives. -/
theorem quad_excluded {a u sigma : ℝ} (h0 : 29/100 ≤ a) (h1 : a ≤ 2/5)
    (hS : sigma ≤ 63/10)
    (hloc : 9 ≤ 9 * a * u + (1 - a ^ 2) * sigma)
    (hu : u < 1) : False :=
  contradiction (by linarith) (by linarith) hS hloc (quadratic_pos h1) hu

end SendovN.Small10

#print axioms SendovN.Small10.product_excluded
#print axioms SendovN.Small10.sigma_small
#print axioms SendovN.Small10.quadratic_pos
#print axioms SendovN.Small10.contradiction
#print axioms SendovN.Small10.quad_excluded
