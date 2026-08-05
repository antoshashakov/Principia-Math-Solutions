import Mathlib
import Sendov9.Core
import Sendov9.MidPointwise
import Sendov9.MidWiring
import Sendov9.Sigma22

set_option maxHeartbeats 4000000

namespace Sendov9.MidRow

open Finset

/-!
# Proposition 4.1, instantiated at the counterexample — one lemma, eighteen uses

Everything the middle range needs is now banked; this file is the single place they
meet.  Given a `Counterexample` whose `a` lies in `[α,β]`, the row's constants
`(S,λ,Y)`, its σ bound, its `L`-bound, and its Bernstein certificate, there is no
counterexample.

The proof is exactly the paper's Proposition 4.1:

    u ≥ L_S(a) ≥ λ            `localization` + `MidAn.key_of_loc` + `lam_le_u`
    η² ≤ 1-λ² ≤ Y²            `MidAn.eta_sq_le` + `eta_le_Y`
    |I - J| ≤ E_S(a,η)        `MidPt.norm_I_sub_J_le_E`
    |J| ≥ 1/9 + η²/18 - h⁴/9λ `Sigma22.J_closed_form`/`norm_J_ge` + `MidAn.J_term_le`
    |I| < a/9                 carried (it is a fact about `p`, not about `C`)
    ⟹ 0 < P_{S,λ}(a,η) ≤ |I| - a/9 < 0

`hI` is carried rather than derived because `|I| < a/9` is **not** a consequence of the
`Counterexample` structure — that was the structural finding behind the `Data` refactor.
`INormFull.norm_I_lt` supplies it from the polynomial, and the caller passes it in.

`Emaj` is `E_S` written through `MidPt`'s tables, i.e. exactly the quantity
`MidPt.norm_I_sub_J_le_E` bounds; `MidMaj.term_*` rewrites it into the certificate's
closed rational form.

Sendov's conjecture in degree nine remains unproven.
-/

/-- `E_S(a,η)`, in the shape `MidPt.norm_I_sub_J_le_E` produces. -/
noncomputable def Emaj (S a eta : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 8, MidPt.cc m * eta ^ m * (a ^ (m + 1)
    * ∫ v in (0:ℝ)..1, v ^ m * MidAn.q S a eta v ^ MidPt.ell m)

/-- `μ + Dⱼ = Yⱼ = (a - ζⱼ)⁻¹`: the integrand of `I` is the centred product. -/
theorem mu_add_D (C : Counterexample) (j : Fin 8) :
    C.mu + C.D j = ((C.a : ℂ) - C.zeta j)⁻¹ := by
  show C.mu + (C.Y j - C.mu) = ((C.a : ℂ) - C.zeta j)⁻¹
  rw [Counterexample.Y]
  ring

/-- **Proposition 4.1 at the counterexample.** -/
theorem row_excluded {alpha beta S lam Y cconst : ℝ} (C : Counterexample)
    (hab : alpha < beta) (halpha0 : 0 < alpha) (hbeta1 : beta ≤ 1)
    (hY : 0 < Y) (hc : 0 < cconst) (hlam0 : 0 < lam) (h2lb : beta ≤ 2 * lam)
    (P : ℝ → ℝ → ℝ)
    (cert : ∀ U V : ℝ, 0 ≤ U → U ≤ 1 → 0 ≤ V → V ≤ 1 →
      cconst ≤ P (alpha + (beta - alpha) * U) (Y * V))
    (hPdef : ∀ x e : ℝ, P x e
      = (1 - x) / 9 + e ^ 2 / 18 - MidAn.hh S x e ^ 4 / (9 * lam) - Emaj S x e)
    (hYc : 1 - lam ^ 2 ≤ Y ^ 2)
    (hL : 0 ≤ S * C.a ^ 2 - 8 * lam * C.a + 8 - S)
    (hsig : C.sigma ≤ S)
    (h0 : alpha ≤ C.a) (h1 : C.a ≤ beta)
    (hI : ‖∫ t in (0:ℝ)..C.a, ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹)‖
      < C.a / 9) :
    False := by
  have ha0 : 0 < C.a := lt_of_lt_of_le halpha0 h0
  have ha1 : C.a ≤ 1 := le_trans h1 hbeta1
  have hbeta0 : (0:ℝ) ≤ beta := by linarith
  -- ### localization ⇒ `8 - S + Sa² ≤ 8au`, and the row's `L`-bound ⇒ `u ≥ λ`
  have hloc := localization C
  have hkey : 8 - S + S * C.a ^ 2 ≤ 8 * C.a * C.mu.re :=
    MidAn.key_of_loc ha1 ha0.le hloc hsig
  have hLkey : 8 * C.a * lam ≤ 8 - S + S * C.a ^ 2 := by linarith
  have hlamu : lam ≤ C.mu.re := MidAn.lam_le_u ha0 hkey hL
  have hmunorm : lam ≤ ‖C.mu‖ := MidAn.lam_le_norm C.mu hlamu
  have hmu0 : C.mu ≠ 0 := by
    intro hcon
    rw [hcon] at hmunorm
    simp at hmunorm
    linarith
  -- ### `η`
  have heta0 : 0 ≤ C.eta := eta_nonneg C
  have hetasq : Complex.normSq C.mu = 1 - C.eta ^ 2 := by
    have := eta_sq C
    linarith
  have hetale : C.eta ^ 2 ≤ 1 - lam ^ 2 :=
    MidAn.eta_sq_le C.mu hlam0.le hetasq hmunorm
  have hetaY : C.eta ≤ Y := MidAn.eta_le_Y hY.le heta0 hetale hYc
  have heta1 : C.eta < 1 := by nlinarith
  -- ### `|I - J| ≤ E_S`
  have hIJ0 := MidPt.norm_I_sub_J_le_E (a := C.a) (eta := C.eta) (S := S) (lam := lam)
    (beta := beta) C.mu C.D ha0 h1 hbeta0 heta0 hetasq hkey hLkey h2lb
    (sum_D_zero C) (sum_normSq_D_le C)
  have hprodrw : ∀ t : ℝ, (∏ j, ((1 : ℂ) - (t : ℂ) * (C.mu + C.D j)))
      = ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹) := by
    intro t
    exact Finset.prod_congr rfl fun j _ => by rw [mu_add_D C j]
  simp only [hprodrw] at hIJ0
  have hIJ : ‖(∫ t in (0:ℝ)..C.a, ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹))
      - (∫ t in (0:ℝ)..C.a, ((1 : ℂ) - (t : ℂ) * C.mu) ^ 8)‖ ≤ Emaj S C.a C.eta := hIJ0
  -- ### `|J| ≥ 1/9 + η²/18 - h⁴/(9λ)`
  have hnormsq : ‖C.mu‖ ^ 2 = 1 - C.eta ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; exact hetasq
  have hJ0 := norm_J_ge hmu0 C.a C.eta hnormsq heta0 heta1
  have hRsq : ‖1 - (C.a : ℂ) * C.mu‖ ^ 2 ≤ MidAn.hh S C.a C.eta :=
    MidAn.R_sq_le_h C.mu hetasq hkey
  have hh0 : 0 ≤ MidAn.hh S C.a C.eta := MidAn.h_nonneg C.mu hetasq hkey
  have hh1 : MidAn.hh S C.a C.eta ≤ 1 :=
    MidAn.h_le_one ha0.le h1 hbeta0 hLkey h2lb
  have hterm := MidAn.J_term_le (R := ‖1 - (C.a : ℂ) * C.mu‖)
    (h := MidAn.hh S C.a C.eta) (lam := lam) C.mu hlam0 (norm_nonneg _) hh0 hh1 hRsq
    hmunorm
  have hJcf := J_closed_form hmu0 C.a
  have hJ : 1 / 9 + C.eta ^ 2 / 18 - MidAn.hh S C.a C.eta ^ 4 / (9 * lam)
      ≤ ‖∫ t in (0:ℝ)..C.a, ((1 : ℂ) - (t : ℂ) * C.mu) ^ 8‖ := by
    rw [hJcf]
    linarith [hJ0, hterm]
  -- ### the triangle inequality
  have htri : ‖∫ t in (0:ℝ)..C.a, ((1 : ℂ) - (t : ℂ) * C.mu) ^ 8‖
      - ‖(∫ t in (0:ℝ)..C.a, ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹))
          - (∫ t in (0:ℝ)..C.a, ((1 : ℂ) - (t : ℂ) * C.mu) ^ 8)‖
      ≤ ‖∫ t in (0:ℝ)..C.a, ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹)‖ := by
    have := norm_sub_norm_le
      (∫ t in (0:ℝ)..C.a, ((1 : ℂ) - (t : ℂ) * C.mu) ^ 8)
      (∫ t in (0:ℝ)..C.a, ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹))
    rw [norm_sub_rev] at this
    linarith
  -- ### the certificate closes it
  exact Mid.mid_row_excluded' hab hY hc P cert h0 h1 heta0 hetaY
    (hPdef C.a C.eta) htri hI hIJ hJ

end Sendov9.MidRow

#print axioms Sendov9.MidRow.mu_add_D
#print axioms Sendov9.MidRow.row_excluded
