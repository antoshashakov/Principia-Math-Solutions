import Mathlib
import Sendov9.Sigma22
import Sendov9.IminusJ
import Sendov9.MidMajorant
import Sendov9.EmLadder
import Sendov9.NewtonWiring
-- NOT `Sendov9.Stage2bc`: it declares `Sendov9.sum_normSq_D_le`, which collides with
-- `Core`'s (from `Instantiate2`).  `e2_bound` below is proved from `NewtonWiring`'s
-- centred Newton instead, so nothing here needs it.

set_option maxHeartbeats 4000000

namespace Sendov9.MidPt

open Finset

/-!
# `|I - J| ≤ E_S(a,η)` — the pointwise estimate and its integral

This closes the analytic half of Proposition 4.1.  With `w = 1 - tμ` and `Yⱼ = μ + Dⱼ`,

    ∏ⱼ(1 - tYⱼ) = ∏ⱼ(w - tDⱼ) = w⁸ + ∑_{m=2}^{8} (-t)ᵐ w^{8-m} eₘ(D),

so `I`'s integrand differs from `J`'s by exactly the tail, and the tail is bounded
termwise by the `eₘ` constants.  Every piece is already banked:

| step | lemma |
|---|---|
| the centred expansion | `Sigma22.prod_sub_eq_head_add_tail` |
| `‖tail‖ ≤ ∑ tᵐ‖w‖^{8-m}cₘηᵐ` | `Sigma22.norm_tail_le` |
| the `cₘ` themselves | `e2_bound` here, `Em.e3_bound'`/`e4_bound'`, `EmLadder.e5..e8` |
| `‖w‖² ≤ qt(t) ≤ 1` | `MidMaj.normSq_le_qt`, `qt_le_one`, `qt_nonneg` |
| `‖w‖^{8-m} ≤ qt^{ℓₘ}` | `IJ.pow_le_q_pow` |
| integrating the majorant | `IJ.norm_I_sub_J_le`, `IJ.integral_majorant` |
| `t = av` | `MidMaj.integral_term` |

The `(cₘ)` are `(4, 264/35, 24, 56, 28, 8, 1)` and the `(ℓₘ)` are `(3,2,2,1,1,0,0)`.
Note the three sources of the `cₘ` are genuinely different: `c₂` is centred Newton at
order two, `c₃`/`c₄` are centred Newton at orders three and four, and `c₅…c₈` are
Maclaurin — and all three are now theorems rather than hypotheses.

`ell_ok` records that `2ℓₘ ≤ 8-m` throughout, which is what licenses discarding the
surplus factors of `‖w‖ ≤ 1` (the paper's rounding-down of half-integral powers).

Sendov's conjecture in degree nine remains unproven.
-/

/-- The exponent table `(ℓ₂,…,ℓ₈) = (3,2,2,1,1,0,0)`. -/
def ell (m : ℕ) : ℕ :=
  if m = 2 then 3 else if m = 3 then 2 else if m = 4 then 2
  else if m = 5 then 1 else if m = 6 then 1 else 0

/-- The constant table `(c₂,…,c₈) = (4, 264/35, 24, 56, 28, 8, 1)`. -/
noncomputable def cc (m : ℕ) : ℝ :=
  if m = 2 then 4 else if m = 3 then 264/35 else if m = 4 then 24
  else if m = 5 then 56 else if m = 6 then 28 else if m = 7 then 8 else 1

/-- `2ℓₘ ≤ 8 - m` on `2 ≤ m ≤ 8`: the surplus `‖w‖` factors can be discarded. -/
theorem ell_ok : ∀ m ∈ Finset.Icc 2 8, 2 * ell m ≤ 8 - m := by decide

/-! ### The three `esD` copies agree

`Sigma22`, `NewtonWiring` and `EmLadder` each carry the same definition verbatim (they
were written to gate standalone).  These are the `rfl`s that let their bounds be used
interchangeably. -/

theorem esD_em (D : Fin 8 → ℂ) (m : ℕ) : Em.esD D m = esD D m := rfl
theorem esD_ladder (D : Fin 8 → ℂ) (m : ℕ) : EmLadder.esD D m = esD D m := rfl
theorem esD_newton (D : Fin 8 → ℂ) (m : ℕ) : Newton.e D m = esD D m := rfl

/-- **`|e₂| ≤ 4η²`**, the paper's `c₂`, from centred Newton at order two (`2e₂ = -p₂`). -/
theorem e2_bound (D : Fin 8 → ℂ) (eta : ℝ) (hz : ∑ j, D j = 0)
    (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2) : ‖esD D 2‖ ≤ 4 * eta ^ 2 := by
  have h := Newton.e_two_centred (x := D) hz
  rw [esD_newton] at h
  have hp : Newton.p D 2 = ∑ j, (D j) ^ 2 := rfl
  rw [hp] at h
  have h1 : ‖∑ j, (D j) ^ 2‖ ≤ ∑ j, ‖D j‖ ^ 2 := Em.norm_power_sum_le D 2
  have h2 : (2:ℝ) * ‖esD D 2‖ = ‖∑ j, (D j) ^ 2‖ := by
    rw [← norm_neg (∑ j, (D j) ^ 2), ← h, norm_mul]
    norm_num
  linarith

/-- **The `eₘ` table**, `2 ≤ m ≤ 8`, assembled from its three different sources. -/
theorem em_table (D : Fin 8 → ℂ) (eta : ℝ) (heta : 0 ≤ eta) (hz : ∑ j, D j = 0)
    (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2) :
    ∀ m ∈ Finset.Icc 2 8, ‖esD D m‖ ≤ cc m * eta ^ m := by
  intro m hm
  simp only [Finset.mem_Icc] at hm
  obtain ⟨h2, h8⟩ := hm
  interval_cases m
  · have := e2_bound D eta hz hD
    simpa [cc] using this
  · have := Em.e3_bound' D eta heta hz hD
    rw [esD_em] at this
    simpa [cc] using this
  · have := Em.e4_bound' D eta heta hz hD
    rw [esD_em] at this
    simpa [cc] using this
  · have := EmLadder.e5_bound D eta heta hD
    rw [esD_ladder] at this
    simpa [cc] using this
  · have := EmLadder.e6_bound D eta heta hD
    rw [esD_ladder] at this
    simpa [cc] using this
  · have := EmLadder.e7_bound D eta heta hD
    rw [esD_ladder] at this
    simpa [cc] using this
  · have := EmLadder.e8_bound D eta heta hD
    rw [esD_ladder] at this
    simpa [cc] using this

/-- **The pointwise estimate.**  For `0 ≤ t ≤ a`, the two integrands differ by at most
the majorant `∑ₘ cₘ ηᵐ tᵐ qt(t)^{ℓₘ}`. -/
theorem pointwise {a eta S lam beta : ℝ} (mu : ℂ) (D : Fin 8 → ℂ)
    (ha : 0 < a) (hab : a ≤ beta) (hbeta : 0 ≤ beta) (heta0 : 0 ≤ eta)
    (hnormSq : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : 8 - S + S * a ^ 2 ≤ 8 * a * mu.re)
    (hL : 8 * a * lam ≤ 8 - S + S * a ^ 2) (h2lb : beta ≤ 2 * lam)
    (hz : ∑ j, D j = 0) (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2)
    (t : ℝ) (ht0 : 0 ≤ t) (hta : t ≤ a) :
    ‖(∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j))) - ((1 : ℂ) - (t : ℂ) * mu) ^ 8‖
      ≤ ∑ m ∈ Finset.Icc 2 8, cc m * eta ^ m * (t ^ m * MidMaj.qt S a eta t ^ ell m) := by
  -- rewrite the product about the centre `w = 1 - tμ`
  have hfac : ∀ j : Fin 8, (1 : ℂ) - (t : ℂ) * (mu + D j)
      = ((1 : ℂ) - (t : ℂ) * mu) - (t : ℂ) * D j := by
    intro j; ring
  rw [Finset.prod_congr rfl (fun j _ => hfac j),
    prod_sub_eq_head_add_tail ((1 : ℂ) - (t : ℂ) * mu) (t : ℂ) D hz]
  simp only [add_sub_cancel_left]
  -- the tail, bounded termwise by the `eₘ` table
  refine le_trans (norm_tail_le ((1 : ℂ) - (t : ℂ) * mu) (t : ℂ) D cc eta
    (em_table D eta heta0 hz hD)) ?_
  -- `‖t‖ = t`, and `‖w‖^{8-m} ≤ qt(t)^{ℓₘ}`
  have hnt : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_of_nonneg ht0]
  have hq0 : 0 ≤ MidMaj.qt S a eta t := MidMaj.qt_nonneg mu ha ht0 hnormSq hkey
  have hq1 : MidMaj.qt S a eta t ≤ 1 :=
    MidMaj.qt_le_one ha ht0 hta (le_of_lt ha) hab hbeta hL h2lb
  have hwsq : ‖(1 : ℂ) - (t : ℂ) * mu‖ ^ 2 ≤ MidMaj.qt S a eta t := by
    have h := MidMaj.normSq_le_qt (a := a) (eta := eta) (S := S) (t := t) mu ha ht0
      hnormSq hkey
    rwa [Complex.normSq_eq_norm_sq] at h
  refine Finset.sum_le_sum fun m hm => ?_
  have hle : 2 * ell m ≤ 8 - m := ell_ok m hm
  have hpow : ‖(1 : ℂ) - (t : ℂ) * mu‖ ^ (8 - m) ≤ MidMaj.qt S a eta t ^ ell m :=
    IJ.pow_le_q_pow (norm_nonneg _) hwsq hq0 hq1 hle
  have hcc : 0 ≤ cc m * eta ^ m := by
    simp only [Finset.mem_Icc] at hm
    obtain ⟨h2, h8⟩ := hm
    have : 0 ≤ cc m := by
      unfold cc
      split_ifs <;> norm_num
    positivity
  rw [hnt]
  have hstep : t ^ m * ‖(1 : ℂ) - (t : ℂ) * mu‖ ^ (8 - m) * (cc m * eta ^ m)
      ≤ t ^ m * MidMaj.qt S a eta t ^ ell m * (cc m * eta ^ m) := by
    apply mul_le_mul_of_nonneg_right _ hcc
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  calc t ^ m * ‖(1 : ℂ) - (t : ℂ) * mu‖ ^ (8 - m) * (cc m * eta ^ m)
      ≤ t ^ m * MidMaj.qt S a eta t ^ ell m * (cc m * eta ^ m) := hstep
    _ = cc m * eta ^ m * (t ^ m * MidMaj.qt S a eta t ^ ell m) := by ring

/-- **`|I - J| ≤ E_S(a,η)`** — equation (4.5), with `E_S` in the exact form the
certificates are stated against (`a^{m+1}` times a `[0,1]` integral in `v`). -/
theorem norm_I_sub_J_le_E {a eta S lam beta : ℝ} (mu : ℂ) (D : Fin 8 → ℂ)
    (ha : 0 < a) (hab : a ≤ beta) (hbeta : 0 ≤ beta) (heta0 : 0 ≤ eta)
    (hnormSq : Complex.normSq mu = 1 - eta ^ 2)
    (hkey : 8 - S + S * a ^ 2 ≤ 8 * a * mu.re)
    (hL : 8 * a * lam ≤ 8 - S + S * a ^ 2) (h2lb : beta ≤ 2 * lam)
    (hz : ∑ j, D j = 0) (hD : ∑ j, ‖D j‖ ^ 2 ≤ 8 * eta ^ 2) :
    ‖(∫ t in (0:ℝ)..a, ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j)))
        - (∫ t in (0:ℝ)..a, ((1 : ℂ) - (t : ℂ) * mu) ^ 8)‖
      ≤ ∑ m ∈ Finset.Icc 2 8,
          cc m * eta ^ m * (a ^ (m + 1)
            * ∫ v in (0:ℝ)..1, v ^ m * MidAn.q S a eta v ^ ell m) := by
  have hcontq := MidMaj.continuous_qt S a eta
  have hbcont : Continuous (fun t : ℝ =>
      ∑ m ∈ Finset.Icc 2 8, cc m * eta ^ m * (t ^ m * MidMaj.qt S a eta t ^ ell m)) := by
    apply continuous_finset_sum
    intro m _
    exact ((continuous_pow m).mul (hcontq.pow (ell m))).const_mul (cc m * eta ^ m)
  have hFcont : Continuous (fun t : ℝ => ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j))) := by
    fun_prop
  have hGcont : Continuous (fun t : ℝ => ((1 : ℂ) - (t : ℂ) * mu) ^ 8) := by
    fun_prop
  have hbound := IJ.norm_I_sub_J_le (le_of_lt ha)
    (fun t : ℝ => ∏ j, ((1 : ℂ) - (t : ℂ) * (mu + D j)))
    (fun t : ℝ => ((1 : ℂ) - (t : ℂ) * mu) ^ 8)
    (fun t : ℝ => ∑ m ∈ Finset.Icc 2 8,
      cc m * eta ^ m * (t ^ m * MidMaj.qt S a eta t ^ ell m))
    (hFcont.intervalIntegrable _ _) (hGcont.intervalIntegrable _ _)
    (hbcont.intervalIntegrable _ _)
    (fun t ht => pointwise mu D ha hab hbeta heta0 hnormSq hkey hL h2lb hz hD t ht.1 ht.2)
  refine le_trans hbound (le_of_eq ?_)
  rw [IJ.integral_majorant a cc eta (MidMaj.qt S a eta) ell hcontq]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MidMaj.integral_term S a eta ha m (ell m)]

end Sendov9.MidPt

#print axioms Sendov9.MidPt.ell_ok
#print axioms Sendov9.MidPt.esD_em
#print axioms Sendov9.MidPt.esD_ladder
#print axioms Sendov9.MidPt.esD_newton
#print axioms Sendov9.MidPt.e2_bound
#print axioms Sendov9.MidPt.em_table
#print axioms Sendov9.MidPt.pointwise
#print axioms Sendov9.MidPt.norm_I_sub_J_le_E
