import Mathlib
import SendovNSigma

set_option maxHeartbeats 1000000

/-!
# D11-3: the degree-11 small range `0 ≤ a ≤ 37/100` (two pieces)

As `SendovNSmall10.lean`, with the degree-11 constants of the plan and
`degree11_verify.py`:

* **Piece (i), `0 ≤ a ≤ 27/100`** — `∏ rₖ ≤ (1+a)¹⁰ ≤ (127/100)¹⁰ < 11`.
* **Piece (ii), `27/100 ≤ a ≤ 37/100`** — Lemma σ with `M = 137/100` (`ν = 10`,
  exact `S₀ = 9·(100/137)² + ((137/100)⁹/11)² = 7.1839…`, dominated by `36/5`),
  then the quadratic `S₀a² − 10a + 10 − S₀ > 0` forces `u > 1`.

Plain numerals (`10`, `11`); cast bridging is the assembly agent's job.
-/

namespace SendovN.Small11

open Finset

/-- **Piece (i).**  `0 ≤ a ≤ 27/100` is impossible:
`∏ rₖ ≤ (1+a)¹⁰ ≤ (127/100)¹⁰ < 11`. -/
theorem product_excluded {a : ℝ} {r : Fin 10 → ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 27/100)
    (hr0 : ∀ k, 0 ≤ r k) (hr : ∀ k, r k ≤ 1 + a) (hprod : 11 < ∏ k, r k) :
    False := by
  have h1 : ∏ k, r k ≤ (1 + a) ^ 10 := by
    calc ∏ k, r k ≤ ∏ _k : Fin 10, (1 + a) :=
          Finset.prod_le_prod (fun k _ => hr0 k) (fun k _ => hr k)
      _ = (1 + a) ^ 10 := by simp
  have h2 : (1 + a : ℝ) ^ 10 ≤ (127/100) ^ 10 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 10
  have h3 : ((127/100 : ℝ)) ^ 10 < 11 := by norm_num
  linarith

/-- Lemma σ at `M = 137/100` (`ν = 10`): on `a ≤ 37/100`, `σ ≤ 36/5`. -/
theorem sigma_small (r : Fin 10 → ℝ) (hlo : ∀ k, (563/1000 : ℝ) ≤ r k)
    (hhi : ∀ k, r k ≤ 137/100) (hprod : (11:ℝ) ≤ ∏ k, r k) :
    ∑ k, 1 / r k ^ 2 ≤ 36/5 := by
  refine SigmaGen.sigma_le_of (m := (563/1000 : ℝ)) (M := (137/100 : ℝ)) (C := 11)
    (nu := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_ (by norm_num) r hlo hhi hprod
  intro j hj
  interval_cases j <;> norm_num

/-- The quadratic `S₀a² − 10a + 10 − S₀` with `S₀ = 36/5` is positive up to
`37/100` (its value at the right endpoint is `1071/12500`). -/
theorem quadratic_pos {a : ℝ} (h1 : a ≤ 37/100) :
    0 < (36/5 : ℝ) * a ^ 2 - 10 * a + 10 - 36/5 := by
  nlinarith [sq_nonneg (a - 37/100)]

/-- **The small-range contradiction** at degree 11. -/
theorem contradiction {a u sigma S0 : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hS : sigma ≤ S0)
    (hloc : 10 ≤ 10 * a * u + (1 - a ^ 2) * sigma)
    (hquad : 0 < S0 * a ^ 2 - 10 * a + 10 - S0)
    (hu : u < 1) : False := by
  have hsq : (0:ℝ) ≤ 1 - a ^ 2 := by nlinarith
  have h1 : 10 ≤ 10 * a * u + (1 - a ^ 2) * S0 := by nlinarith
  nlinarith

/-- **Piece (ii), packaged**: no configuration with `27/100 ≤ a ≤ 37/100`
survives. -/
theorem quad_excluded {a u sigma : ℝ} (h0 : 27/100 ≤ a) (h1 : a ≤ 37/100)
    (hS : sigma ≤ 36/5)
    (hloc : 10 ≤ 10 * a * u + (1 - a ^ 2) * sigma)
    (hu : u < 1) : False :=
  contradiction (by linarith) (by linarith) hS hloc (quadratic_pos h1) hu

end SendovN.Small11

#print axioms SendovN.Small11.product_excluded
#print axioms SendovN.Small11.sigma_small
#print axioms SendovN.Small11.quadratic_pos
#print axioms SendovN.Small11.contradiction
#print axioms SendovN.Small11.quad_excluded
