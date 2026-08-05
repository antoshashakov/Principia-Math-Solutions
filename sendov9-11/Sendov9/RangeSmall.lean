import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.Small

/-!
# The range `0 ≤ a ≤ 9/20` (§4 of the paper)

This is the one range that needs no certificate.  The chain is:

1. Lemma 2.2 with `M = 29/20`, `ν = 7` gives `σ ≤ S₀ = 1101/200`.
2. Localization `8au + (1-a²)σ ≥ 8` then forces `u ≥ (8 - S₀(1-a²))/(8a)`.
3. That right-hand side exceeds `1` exactly when `S₀a² - 8a + 8 - S₀ > 0`, which holds
   on `[0, 9/20]` (the quadratic is decreasing there and equals `781/80000` at the
   right endpoint).
4. So `u > 1`, contradicting `|μ| < 1`.

`a = 0` is separately impossible: `∏ rₖ > 9` cannot hold with every `rₖ = |zₖ| ≤ 1`.

Everything below is stated over the real quantities, so it composes with the bounds
already verified (`Stage2Probe.lean` for localization and `|μ| < 1`, `Sigma22.lean` +
`BaseNumerics.lean` for the σ bound) without re-deriving them.
-/

/-- **The small-range contradiction.**  Steps 2–4 above. -/
theorem contradiction {a u sigma S0 : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hS : sigma ≤ S0)
    (hloc : 8 ≤ 8 * a * u + (1 - a ^ 2) * sigma)
    (hquad : 0 < S0 * a ^ 2 - 8 * a + 8 - S0)
    (hu : u < 1) : False := by
  have hsq : (0:ℝ) ≤ 1 - a ^ 2 := by nlinarith
  -- σ ≤ S₀ weakens localization to 8 ≤ 8au + (1-a²)S₀
  have h1 : 8 ≤ 8 * a * u + (1 - a ^ 2) * S0 := by nlinarith
  -- the quadratic says 8 - S₀(1-a²) > 8a, so 8au > 8a, so u > 1
  nlinarith

/-- The quadratic is positive on `[0, 9/20]` with `S₀ = 1101/200`; its value at the
right endpoint is exactly `781/80000`. -/
theorem quadratic_pos {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 9 / 20) :
    0 < (1101 / 200 : ℝ) * a ^ 2 - 8 * a + 8 - 1101 / 200 := by
  nlinarith [sq_nonneg a, sq_nonneg (a - 9 / 20)]

theorem quadratic_endpoint :
    (1101 / 200 : ℝ) * (9 / 20) ^ 2 - 8 * (9 / 20) + 8 - 1101 / 200 = 781 / 80000 := by
  norm_num

/-- **The range is excluded**, packaged: given the σ bound and localization, no
configuration with `0 < a ≤ 9/20` survives. -/
theorem range_excluded {a u sigma : ℝ}
    (ha0 : 0 < a) (ha : a ≤ 9 / 20)
    (hS : sigma ≤ 1101 / 200)
    (hloc : 8 ≤ 8 * a * u + (1 - a ^ 2) * sigma)
    (hu : u < 1) : False :=
  contradiction ha0 (by linarith) hS hloc (quadratic_pos (le_of_lt ha0) ha) hu

/-- `a = 0` is impossible: `∏ rₖ > 9` with every `rₖ ≤ 1`. -/
theorem zero_excluded {r : Fin 8 → ℝ} (hr0 : ∀ k, 0 ≤ r k) (hr : ∀ k, r k ≤ 1)
    (hprod : 9 < ∏ k, r k) : False := by
  have h1 : ∏ k, r k ≤ 1 := by
    calc ∏ k, r k ≤ ∏ _k : Fin 8, (1:ℝ) :=
          Finset.prod_le_prod (fun k _ => hr0 k) (fun k _ => hr k)
      _ = 1 := by simp
  linarith

end Sendov9.Small

#print axioms Sendov9.Small.contradiction
#print axioms Sendov9.Small.quadratic_pos
#print axioms Sendov9.Small.quadratic_endpoint
#print axioms Sendov9.Small.range_excluded
#print axioms Sendov9.Small.zero_excluded
