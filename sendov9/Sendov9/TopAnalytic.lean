import Mathlib
import Sendov9.MidAnalytic

set_option maxHeartbeats 4000000

namespace Sendov9.TopAn

open Finset

/-!
# The boundary range's majorant `q(x,y;t)`

Equation (5.4): `q(x,y;t) = (1-t)² + x²t(19/10 - y²t)`.  Expanded, that is

    q = 1 + (-2 + (19/10)x²)·t + (1 - x²y²)·t²,

i.e. exactly the `1 + Q1 t + Q2 t²` shape of the middle range with `Cert.bdry_pos`'s own
`Q1` and `Q2`.  So the boundary needs no new integral machinery — only the variable
upper limit `W = 1 - x²`, which `EIntegralsW.lean` supplies.

## What is proved

* `qb_eq_paper` — the two forms agree, so the paper's `(1-t)²+…` and the certificate's
  `1 + Q1t + Q2t²` are interchangeable.
* `normSq_le_qb` — `|1 - tμ|² ≤ q(x,y;t)` for `t ≥ 0`.  The constant `19/10` is exactly
  `2·(19/20)`, the doubled coefficient from `1 - u ≤ (19/20)δ`; this is where
  `Top.one_sub_u_le` is spent.
* `qb_nonneg` — from `q` dominating a square, as in the middle range.
* `qb_le_one` — on `0 ≤ t ≤ 1 - x²`.  The binding computation is
  `-2 + (19/10)x² + (1-x²y²)(1-x²) ≤ -1 + (9/10)x² ≤ 0`, so the upper limit `W` is not
  incidental: `q ≤ 1` can fail past it.

As in the middle range, the `q` bounds hold **only at feasible points**, and `qb_nonneg`
is derived from the square rather than asserted on the certificate's box.

Sendov's conjecture in degree nine remains unproven.
-/

/-- The boundary majorant, in the certificate's `1 + Q1 t + Q2 t²` form. -/
noncomputable def qb (x y t : ℝ) : ℝ :=
  1 + (-2 + (19/10 : ℝ) * x ^ 2) * t + (1 - x ^ 2 * y ^ 2) * t ^ 2

/-- **The two forms agree.**  `(1-t)² + x²t(19/10 - y²t)` is `1 + Q1t + Q2t²`. -/
theorem qb_eq_paper (x y t : ℝ) :
    qb x y t = (1 - t) ^ 2 + x ^ 2 * t * ((19/10 : ℝ) - y ^ 2 * t) := by
  unfold qb
  ring

/-- **The pointwise majorant.**  `|1 - tμ|² ≤ q(x,y;t)` for `t ≥ 0`.

`19/10 = 2·(19/20)` is exactly the doubling of the coefficient in `1 - u ≤ (19/20)δ`. -/
theorem normSq_le_qb {x y t u : ℝ} (mu : ℂ) (ht0 : 0 ≤ t)
    (hu : mu.re = u) (hdx : Complex.normSq mu = 1 - x ^ 2 * y ^ 2)
    (hone : 1 - u ≤ (19/20 : ℝ) * x ^ 2) :
    Complex.normSq (1 - (t : ℂ) * mu) ≤ qb x y t := by
  rw [MidAn.normSq_one_sub, hdx, hu]
  unfold qb
  nlinarith [ht0, hone]

/-- `0 ≤ q`, because it dominates a square. -/
theorem qb_nonneg {x y t u : ℝ} (mu : ℂ) (ht0 : 0 ≤ t)
    (hu : mu.re = u) (hdx : Complex.normSq mu = 1 - x ^ 2 * y ^ 2)
    (hone : 1 - u ≤ (19/20 : ℝ) * x ^ 2) :
    0 ≤ qb x y t :=
  le_trans (Complex.normSq_nonneg _) (normSq_le_qb mu ht0 hu hdx hone)

/-- **`q ≤ 1` on `[0, 1-x²]`.**

`q - 1 = t(-2 + (19/10)x² + (1-x²y²)t)`, and at the top of the range the bracket is
`≤ -1 + (9/10)x² ≤ 0`.  The upper limit is doing real work here — the bound fails past
`W = 1 - x²`. -/
theorem qb_le_one {x y t : ℝ} (ht0 : 0 ≤ t) (htW : t ≤ 1 - x ^ 2)
    (hx0 : 0 ≤ x) (hx : x ≤ 8/25) (hy0 : 0 ≤ y) (hy : y ^ 2 ≤ 19/10) :
    qb x y t ≤ 1 := by
  have hx2 : x ^ 2 ≤ 64/625 := by nlinarith
  -- `1 - x²y² ≥ 0`, so the `t²` coefficient is nonnegative and `t ≤ 1 - x²` binds
  have hQ2 : (0:ℝ) ≤ 1 - x ^ 2 * y ^ 2 := by nlinarith
  have hstep : (1 - x ^ 2 * y ^ 2) * t ≤ (1 - x ^ 2 * y ^ 2) * (1 - x ^ 2) :=
    mul_le_mul_of_nonneg_left htW hQ2
  -- the bracket at the top of the range
  have hbr : -2 + (19/10 : ℝ) * x ^ 2 + (1 - x ^ 2 * y ^ 2) * (1 - x ^ 2) ≤ 0 := by
    nlinarith [hx2, hQ2, sq_nonneg (x * y)]
  unfold qb
  nlinarith [ht0, hstep, hbr]

end Sendov9.TopAn

#print axioms Sendov9.TopAn.qb_eq_paper
#print axioms Sendov9.TopAn.normSq_le_qb
#print axioms Sendov9.TopAn.qb_nonneg
#print axioms Sendov9.TopAn.qb_le_one
