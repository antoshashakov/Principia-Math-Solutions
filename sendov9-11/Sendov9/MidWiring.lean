import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.Mid

/-!
# The middle range: wiring the certificates to Proposition 4.1

`CertData.lean` proves each certificate positive on `[0,1]²` in the variables `U, V`,
where `a = α + (β-α)U` and `η = Y·V`.  Proposition 4.1 consumes a positive value at
the counterexample's own `(a, η)`.  The only missing step is the change of variables,
which is what this file supplies.

Given `a ∈ [α,β]` and `η ∈ [0,Y]`, take `U = (a-α)/(β-α)` and `V = η/Y`.  Then
`U, V ∈ [0,1]` and the substitution round-trips: `α + (β-α)U = a` and `Y·V = η`.
`subst_ok` packages all six facts; `mid_row_excluded` then composes certificate +
analytic bounds into a contradiction, for an arbitrary certificate polynomial `P`.

With that, each of the 18 rows is: `row<i>_L` and `row<i>_side` (verified in
`MidTable.lean`), the σ bound, the certificate `i<i>_pos` (verified in `CertData.lean`),
and this wiring.
-/

/-- **The change of variables.**  `[α,β] × [0,Y] → [0,1]²` and back. -/
theorem subst_ok {alpha beta Y a eta : ℝ} (hab : alpha < beta) (hY : 0 < Y)
    (h0 : alpha ≤ a) (h1 : a ≤ beta) (he0 : 0 ≤ eta) (he1 : eta ≤ Y) :
    0 ≤ (a - alpha) / (beta - alpha) ∧ (a - alpha) / (beta - alpha) ≤ 1 ∧
    0 ≤ eta / Y ∧ eta / Y ≤ 1 ∧
    alpha + (beta - alpha) * ((a - alpha) / (beta - alpha)) = a ∧
    Y * (eta / Y) = eta := by
  have hba : 0 < beta - alpha := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (by linarith) (le_of_lt hba)
  · rw [div_le_one hba]; linarith
  · exact div_nonneg he0 (le_of_lt hY)
  · rw [div_le_one hY]; exact he1
  · field_simp
    ring
  · field_simp

/-- **The middle-range contradiction**, for an arbitrary certificate polynomial `P`.

`cert` is the shape `CertData.lean` proves: positivity on the unit square after the
affine push-forward.  Everything else is the analytic side, already verified. -/
theorem mid_row_excluded {alpha beta Y : ℝ} (hab : alpha < beta) (hY : 0 < Y)
    (P : ℝ → ℝ → ℝ)
    (cert : ∀ U V : ℝ, 0 ≤ U → U ≤ 1 → 0 ≤ V → V ≤ 1 →
      0 < P (alpha + (beta - alpha) * U) (Y * V))
    {a eta nI nJ nIJ E lam hh : ℝ}
    (h0 : alpha ≤ a) (h1 : a ≤ beta) (he0 : 0 ≤ eta) (he1 : eta ≤ Y)
    (hPdef : P a eta = (1 - a) / 9 + eta ^ 2 / 18 - hh ^ 4 / (9 * lam) - E)
    (htri : nJ - nIJ ≤ nI) (hI : nI < a / 9) (hIJ : nIJ ≤ E)
    (hJ : 1 / 9 + eta ^ 2 / 18 - hh ^ 4 / (9 * lam) ≤ nJ) : False := by
  obtain ⟨hU0, hU1, hV0, hV1, hUa, hVe⟩ := subst_ok hab hY h0 h1 he0 he1
  have hpos := cert _ _ hU0 hU1 hV0 hV1
  rw [hUa, hVe, hPdef] at hpos
  linarith

/-- The same, with the certificate's lower bound `c` made explicit (the form
`CertData.lean` actually states: `c ≤ P` with `c > 0`). -/
theorem mid_row_excluded' {alpha beta Y c : ℝ} (hab : alpha < beta) (hY : 0 < Y)
    (hc : 0 < c) (P : ℝ → ℝ → ℝ)
    (cert : ∀ U V : ℝ, 0 ≤ U → U ≤ 1 → 0 ≤ V → V ≤ 1 →
      c ≤ P (alpha + (beta - alpha) * U) (Y * V))
    {a eta nI nJ nIJ E lam hh : ℝ}
    (h0 : alpha ≤ a) (h1 : a ≤ beta) (he0 : 0 ≤ eta) (he1 : eta ≤ Y)
    (hPdef : P a eta = (1 - a) / 9 + eta ^ 2 / 18 - hh ^ 4 / (9 * lam) - E)
    (htri : nJ - nIJ ≤ nI) (hI : nI < a / 9) (hIJ : nIJ ≤ E)
    (hJ : 1 / 9 + eta ^ 2 / 18 - hh ^ 4 / (9 * lam) ≤ nJ) : False := by
  refine mid_row_excluded hab hY P (fun U V a1 a2 a3 a4 => ?_) h0 h1 he0 he1 hPdef
    htri hI hIJ hJ
  exact lt_of_lt_of_le hc (cert U V a1 a2 a3 a4)

/-- `η ≤ Y` follows from `η² ≤ 1 - λ²` and `Y² ≥ 1 - λ²`, which is how the paper
obtains the `V`-range. -/
theorem eta_le_Y {eta Y lam : ℝ} (hY0 : 0 ≤ Y) (he0 : 0 ≤ eta)
    (heta : eta ^ 2 ≤ 1 - lam ^ 2) (hYc : 1 - lam ^ 2 ≤ Y ^ 2) : eta ≤ Y := by
  nlinarith

end Sendov9.Mid

#print axioms Sendov9.Mid.subst_ok
#print axioms Sendov9.Mid.mid_row_excluded
#print axioms Sendov9.Mid.mid_row_excluded'
#print axioms Sendov9.Mid.eta_le_Y
