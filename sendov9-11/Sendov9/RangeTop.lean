import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.Top

/-!
# The boundary range `9/10 ≤ a ≤ 1` (§5 of the paper)

Write `δ = 1 - a`.  The chain is:

1. Lemma 2.2 with `M = 2`, `ν = 5` gives `σ ≤ 39/5`.
2. Localization then forces `1 - u ≤ δ(39a-1)/(40a) ≤ (19/20)δ`, the last step because
   `(39a-1)/(40a)` is increasing and equals `19/20` at `a = 1` (`one_sub_u_le`).
3. Hence `η² ≤ (19/10)δ - (361/400)δ²` (`eta_sq_le`), and `|μ| ≥ 181/200` (`mu_ge`).
4. Substituting `δ = x²`, `η = xy` puts the feasible set inside the box
   `0 ≤ x ≤ 8/25`, `0 ≤ y ≤ 7/5` (`box_bounds`) — the box the 19th certificate
   (`Sendov9.Cert.bdry_pos`) is proved positive on.
5. `R² ≤ (19/10)δ` and the integer inequality `200²·19⁹ < 1629²·10¹⁰` give
   `R⁹/(9|μ|) ≤ δ/1000`, so `|I| - a/9 ≥ δ·𝒫(x,y)` with `𝒫 > 1/100`.
6. That contradicts `|I| < a/9`.

`a = 1` is separate and immediate: localization gives `u ≥ 1` against `|μ| < 1`.
-/

/-- **Step 2.**  `1 - u ≤ (19/20)δ`.  The coefficient `(39a-1)/(40a)` is increasing in
`a`, so `a ≤ 1` is exactly what caps it at `19/20`. -/
theorem one_sub_u_le {a u sigma : ℝ} (ha : 9 / 10 ≤ a) (ha1 : a ≤ 1)
    (hS : sigma ≤ 39 / 5) (hloc : 8 ≤ 8 * a * u + (1 - a ^ 2) * sigma) :
    1 - u ≤ 19 / 20 * (1 - a) := by
  have ha0 : (0:ℝ) < a := by linarith
  have hsq : (0:ℝ) ≤ 1 - a ^ 2 := by nlinarith
  have h1 : 8 ≤ 8 * a * u + (1 - a ^ 2) * (39 / 5) := by nlinarith
  nlinarith

/-- **Step 3a.**  `η² ≤ (19/10)δ - (361/400)δ²`.  With `s = 1-u ∈ [0, (19/20)δ]` and
`s(2-s)` increasing on `[0,1]`. -/
theorem eta_sq_le {u eta delta : ℝ} (hd0 : 0 ≤ delta) (hd : delta ≤ 1 / 10)
    (hs : 1 - u ≤ 19 / 20 * delta) (hu : u ≤ 1)
    (heta : eta ^ 2 ≤ 1 - u ^ 2) :
    eta ^ 2 ≤ 19 / 10 * delta - 361 / 400 * delta ^ 2 := by
  nlinarith [sq_nonneg (1 - u), sq_nonneg delta]

/-- **Step 3b.**  `|μ| ≥ u ≥ 1 - (19/20)δ ≥ 181/200`. -/
theorem mu_ge {u delta : ℝ} (hd0 : 0 ≤ delta) (hd : delta ≤ 1 / 10)
    (hs : 1 - u ≤ 19 / 20 * delta) : 181 / 200 ≤ u := by
  nlinarith

/-- **Step 4.**  With `δ = x²` and `η = xy`, the feasible set sits inside the
certificate's box `[0, 8/25] × [0, 7/5]`. -/
theorem box_bounds {x y delta eta : ℝ} (hx0 : 0 < x) (hy0 : 0 ≤ y)
    (hdx : delta = x ^ 2) (hey : eta = x * y) (hd0 : 0 < delta) (hd : delta ≤ 1 / 10)
    (heta : eta ^ 2 ≤ 19 / 10 * delta - 361 / 400 * delta ^ 2) :
    x ≤ 8 / 25 ∧ y ≤ 7 / 5 := by
  have hx2 : (0:ℝ) < x ^ 2 := by positivity
  have hxsq : x ^ 2 ≤ 1 / 10 := by rw [← hdx]; exact hd
  -- (8/25)² = 64/625 = 0.1024 > 1/10, so x² ≤ 1/10 forces x ≤ 8/25
  have hxle : x ≤ 8 / 25 := by nlinarith [hxsq, hx0]
  refine ⟨hxle, ?_⟩
  rw [hey, hdx] at heta
  -- drop the -(361/400)x⁴ term, which is ≤ 0
  have hsub : x ^ 2 * (y ^ 2) ≤ x ^ 2 * (19 / 10) := by
    nlinarith [heta, sq_nonneg (x ^ 2)]
  have hy2 : y ^ 2 ≤ 19 / 10 := le_of_mul_le_mul_left hsub hx2
  -- (7/5)² = 1.96 > 1.9
  nlinarith [hy2, hy0]

/-- **Step 5, the numeric core.**  `200²·19⁹ < 1629²·10¹⁰`, which is what makes
`R⁹/(9|μ|) ≤ δ/1000` at `δ ≤ 1/10`. -/
theorem radical_ineq : (200 : ℤ) ^ 2 * 19 ^ 9 < 1629 ^ 2 * 10 ^ 10 := by decide

/-- **Step 6.**  `|I| - a/9 ≥ δ·𝒫` with `𝒫 > 1/100` and `δ > 0` contradicts
`|I| < a/9`. -/
theorem contradiction {a nI delta P : ℝ} (hd : 0 < delta) (hP : 1 / 100 < P)
    (hlow : delta * P ≤ nI - a / 9) (hI : nI < a / 9) : False := by
  nlinarith

/-- `a = 1` is immediate. -/
theorem one_excluded {u sigma : ℝ}
    (hloc : 8 ≤ 8 * 1 * u + (1 - (1:ℝ) ^ 2) * sigma) (hu : u < 1) : False := by
  norm_num at hloc
  linarith

end Sendov9.Top

#print axioms Sendov9.Top.one_sub_u_le
#print axioms Sendov9.Top.eta_sq_le
#print axioms Sendov9.Top.mu_ge
#print axioms Sendov9.Top.box_bounds
#print axioms Sendov9.Top.radical_ineq
#print axioms Sendov9.Top.contradiction
#print axioms Sendov9.Top.one_excluded
