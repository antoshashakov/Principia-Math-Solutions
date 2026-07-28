import Mathlib
import Sendov9.Core
import Sendov9.MidRow
import Sendov9.EmajEq
import Sendov9.SigmaRows
import Sendov9.MidTable
import Sendov9.CertData

set_option maxHeartbeats 4000000

namespace Sendov9.RowPrep

open Finset

/-!
# Bookkeeping for the eighteen rows, and row 1 as the pattern

`MidRow.row_excluded` wants `C.sigma ≤ S`; `SigmaRows.sigma_row<i>` proves
`∑ 1/(rₖ)² ≤ S`.  `Counterexample.sigma` is written with `zpow (-2)`, so the two need
one bridge (`sigma_eq`), and the upper endpoint `rₖ ≤ 1 + a ≤ 1 + β` needs `r_le`.
Neither is in `Core` (they live in `Instantiate.lean`, which is written against the
*other* copy of `Counterexample`), so both are proved here for the canonical structure.

`row1` is then the whole pattern, and it is short: the certificate supplies `cert`,
`MidTable` supplies the `L`-bound and side conditions, `SigmaRows` supplies `σ ≤ S`, and
`hPdef` is `rfl` because `P` is *defined* to be the certificate's own expression.

The only step with any content is matching the certificate's `let`-expression against
`P`: `EmajEq.Emaj_eq` turns `MidRow.Emaj` into the evaluated bracket sum, after which
`ring` closes it.  That the two agree is not luck — the brackets were emitted from
`Sendov9Complete` verbatim precisely so this would hold.

`hsep` (the separation bound `rₖ > m₀`) is carried: it is the one place Grace–Walsh–Szegő
enters, and it is the campaign's last unproved input.

Sendov's conjecture in degree nine remains unproven.
-/

variable (C : Counterexample)

/-- `rₖ ≤ a + 1`, from the triangle inequality and `‖zₖ‖ ≤ 1`. -/
theorem r_le (k : Fin 8) : C.r k ≤ C.a + 1 := by
  have h := norm_sub_le ((C.a : ℂ)) (C.z k)
  have hre : ‖((C.a : ℝ) : ℂ)‖ = C.a := by
    rw [Complex.norm_real, Real.norm_of_nonneg C.ha0]
  rw [hre] at h
  have := C.hz k
  calc C.r k = ‖(C.a : ℂ) - C.z k‖ := rfl
    _ ≤ C.a + ‖C.z k‖ := h
    _ ≤ C.a + 1 := by linarith

/-- `σ` in the form `SigmaRows` proves a bound for. -/
theorem sigma_eq : C.sigma = ∑ k, 1 / (C.r k) ^ 2 := by
  show ∑ k, (C.r k) ^ (-2 : ℤ) = _
  exact Finset.sum_congr rfl fun k _ => zpow_neg_two (C.r k)

/-- **Row 1.**  `a ∈ [9/20, 19/40]`, `S = 11043/2000`, `λ = 49/50`, `Y = 199/1000`. -/
theorem row1
    (hsep : ∀ k, (681/1000 : ℝ) ≤ C.r k)
    (hprod : (9:ℝ) ≤ ∏ k, C.r k)
    (hI : ‖∫ t in (0:ℝ)..C.a, ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹)‖
      < C.a / 9)
    (h0 : (9/20 : ℝ) ≤ C.a) (h1 : C.a ≤ (19/40 : ℝ)) : False := by
  have hrle : ∀ k, C.r k ≤ (59/40 : ℝ) := fun k => le_trans (r_le C k) (by linarith)
  have hsig : C.sigma ≤ (11043/2000 : ℝ) := by
    rw [sigma_eq C]
    exact SigmaRows.sigma_row1 C.r hsep hrle hprod
  -- every one of `row_excluded`'s six implicit reals must be pinned by name: `Y` occurs
  -- only in `hY : 0 < Y` and in the `cert` hole, so otherwise it stays a metavariable
  -- and `hYc` shows up as `99/2500 ≤ ?m ^ 2`.
  refine MidRow.row_excluded (alpha := (9/20 : ℝ)) (beta := (19/40 : ℝ))
    (S := (11043/2000 : ℝ)) (lam := (49/50 : ℝ)) (Y := (199/1000 : ℝ))
    (cconst := (92577811623735141906142997/1610612736000000000000000000 : ℝ))
    C (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (fun x e => (1 - x) / 9 + e ^ 2 / 18
      - MidAn.hh (11043/2000 : ℝ) x e ^ 4 / (9 * (49/50 : ℝ))
      - MidRow.Emaj (11043/2000 : ℝ) x e)
    ?_ (fun _ _ => rfl) (by norm_num) (Mid.row1_L h0 h1) hsig h0 h1 hI
  intro U V hU0 hU1 hV0 hV1
  refine le_trans (Cert.i1_pos hU0 hU1 hV0 hV1) (le_of_eq ?_)
  -- NOT `MidRow.Emaj` in this set: unfolding it to the integral form first stops
  -- `Emaj_eq` from firing, and the integrals then never get evaluated.
  simp only [EmajEq.Emaj_eq, MidAn.hh, MidMaj.Q1, MidMaj.Q2]
  ring

end Sendov9.RowPrep

#print axioms Sendov9.RowPrep.r_le
#print axioms Sendov9.RowPrep.sigma_eq
#print axioms Sendov9.RowPrep.row1
