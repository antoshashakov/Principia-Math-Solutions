import Mathlib
import Sendov9.GWS
import Sendov9.Segment
import Sendov9.RootUnity
import Sendov9.Bridge5
import Sendov9.INormFull
import Sendov9.CoreProd
import Sendov9.RangeSmall
import Sendov9.Sigma22Gen
import Sendov9.MidRows
import Sendov9.TopRow
import Sendov9.RotateData

set_option maxHeartbeats 4000000

namespace Sendov9.Final

open Polynomial Finset

/-!
# Sendov's conjecture in degree nine

The final assembly.  Every input below is proved elsewhere in this directory and gated
with `#print axioms`; nothing is carried as a hypothesis and nothing is an axiom.

**Lemma 2.1 (separation).**  `Segment.integral_uFam_zero` says the apolar integral at a
second zero vanishes; `Segment.norm_u_lt` says the family sits strictly inside the disk
of radius `‖a - zₖ‖`; `GWS.graceWalshSzegoPos` then produces a coincidence point `w`
inside that disk with `∫₀¹(1 - tw)⁸ dt = 0`; and `RootUnity.norm_gt_of_integral_zero`
puts `w` farther than `681/1000` from the origin.  Hence `‖a - zₖ‖ > 681/1000`.

**The three ranges.**  `a ≤ 9/20` is `RangeSmall`'s quadratic (with `a = 0` handled by
`∏rₖ ≤ 1 < 9`); `9/20 ≤ a ≤ 9/10` is `MidRows.mid_excluded`, the eighteen Bernstein rows;
`9/10 ≤ a ≤ 1` is `TopRow.top_excluded`.  All three consume the separation bound, the
product bound `∏rₖ > 9` (`CoreProd`), and `|I| < a/9` (`INormFull` fed by `Bridge5`).

**The rotation.**  `Data` normalizes the distinguished zero to be real and nonnegative;
`RotData.exists_data` performs that rotation on the polynomial, so the statement below
quantifies over a genuine `a : ℂ`.

Statement proved:

> for every monic `p : ℂ[X]` of degree nine with all zeros in the closed unit disk, and
> every zero `a`, some critical point lies within distance `1` of `a`.
-/

/-! ### Lemma 2.1 — the separation bound -/

/-- **Lemma 2.1.**  Every other zero is farther than `681/1000` from `a`.

This is where Grace–Walsh–Szegő is spent; `681/1000 < 2 sin(π/9)` is the paper's
constant, obtained here as a bound on the largest root of `t³ - 3t + 1`. -/
theorem separation (D : Data) (k : Fin 8) : (681/1000 : ℝ) < ‖(D.a : ℂ) - D.z k‖ := by
  obtain ⟨w, hw, heq⟩ := GWS.graceWalshSzegoPos 8 (Segment.uFam D k)
    ‖(D.a : ℂ) - D.z k‖ (by norm_num) (fun j => Segment.norm_u_lt D k j)
  rw [Segment.integral_uFam_zero D k] at heq
  exact lt_trans (RootUnity.norm_gt_of_integral_zero heq.symm) hw

/-- The separation bound, at the `Counterexample` derived from the data. -/
theorem sep_r (D : Data) (k : Fin 8) : (681/1000 : ℝ) ≤ (D.toCounterexample).r k :=
  (separation D k).le

/-! ### `|I| < a/9`, assembled -/

/-- **`|I| < a/9`** for the counterexample data.  `Bridge5.integral_prod_zeta` supplies
the anchor integral; `Extract.prod_map_ofMultiset` transfers both root families. -/
theorem norm_I_lt (D : Data) (ha0 : 0 < D.a) :
    ‖∫ t in (0:ℝ)..D.a, ∏ j, ((1 : ℂ) - (t : ℂ) * ((D.a : ℂ) - D.zeta j)⁻¹)‖ < D.a / 9 := by
  refine INormFull.norm_I_lt ha0 D.z D.zeta D.zeta_ne ?_ D.hprod D.hz ?_
  · exact Bridge5.integral_prod_zeta D.hmonic D.hdeg D.haroot D.z D.zeta
      (fun f => Extract.prod_map_ofMultiset _ D.zcard f)
      (fun f => Extract.prod_map_ofMultiset _ D.zetacard f)
  · exact CoreProd.prod_r_gt_nine D.toCounterexample

/-! ### The small range -/

/-- **`a ≤ 9/20` is excluded.**  At `a = 0` no separation bound is needed — every
`rₖ = ‖zₖ‖ ≤ 1`, so `∏rₖ ≤ 1`, against `∏rₖ > 9`.  Only `0 < a` spends Lemma 2.1. -/
theorem small_excluded (D : Data) (ha : D.toCounterexample.a ≤ 9/20) : False := by
  set C : Counterexample := D.toCounterexample with hC
  have hsep : ∀ k, (681/1000 : ℝ) ≤ C.r k := fun k => sep_r D k
  rcases eq_or_lt_of_le C.ha0 with ha0 | ha0
  · -- `a = 0`
    have hle : ∀ k, C.r k ≤ 1 := by
      intro k
      have h := RowPrep.r_le C k
      rw [← ha0] at h
      linarith
    have h1 : ∏ k, C.r k ≤ 1 := by
      calc ∏ k, C.r k ≤ ∏ _k : Fin 8, (1:ℝ) :=
            Finset.prod_le_prod (fun k _ => (CoreProd.r_pos C k).le) (fun k _ => hle k)
        _ = 1 := by simp
    linarith [CoreProd.prod_r_gt_nine C]
  · -- `0 < a ≤ 9/20`
    have hrle : ∀ k, C.r k ≤ 29/20 := fun k => le_trans (RowPrep.r_le C k) (by linarith)
    have hsigma' : ∑ k, 1 / (C.r k) ^ 2 ≤ 1101/200 :=
      SigmaGen.sigma_small C.r hsep hrle (CoreProd.prod_r_gt_nine C).le
    have hsigma : C.sigma ≤ 1101/200 := by
      rw [RowPrep.sigma_eq C]
      exact hsigma'
    have hu : C.u < 1 := lt_of_le_of_lt (Complex.re_le_norm C.mu) (mu_norm_lt_one C)
    have hloc := localization C
    have ha1 : C.a ≤ 1 := by linarith
    have hsq : (0:ℝ) ≤ 1 - C.a ^ 2 := by nlinarith
    have h1 : 8 ≤ 8 * C.a * C.u + (1 - C.a ^ 2) * (1101 / 200) := by nlinarith
    have hquad : 0 < (1101 / 200 : ℝ) * C.a ^ 2 - 8 * C.a + 8 - 1101 / 200 := by
      nlinarith [sq_nonneg C.a, sq_nonneg (C.a - 9 / 20)]
    nlinarith

/-! ### No counterexample data exists -/

/-- **The three ranges cover `[0,1]`, and each is excluded.** -/
theorem no_data (D : Data) : False := by
  by_cases hsmall : D.toCounterexample.a ≤ 9/20
  · exact small_excluded D hsmall
  push_neg at hsmall
  set C : Counterexample := D.toCounterexample with hC
  have hsep : ∀ k, (681/1000 : ℝ) ≤ C.r k := fun k => sep_r D k
  have hprod : (9:ℝ) ≤ ∏ k, C.r k := (CoreProd.prod_r_gt_nine C).le
  have ha0 : 0 < D.a := by
    -- `C.a` and `D.a` are the same real by construction, but `linarith` is syntactic,
    -- so bridge them explicitly rather than through `hC`.
    have h1 : (9:ℝ)/20 < C.a := hsmall
    have h2 : C.a = D.a := rfl
    rw [h2] at h1
    linarith
  have hI : ‖∫ t in (0:ℝ)..C.a, ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹)‖
      < C.a / 9 := norm_I_lt D ha0
  rcases le_total C.a (9/10) with h | h
  · exact MidRows.mid_excluded C hsep hprod hI hsmall.le h
  · exact TopRow.top_excluded C hsep hprod hI h C.ha1

/-! ### Sendov's conjecture in degree nine -/

/-- **Sendov's conjecture, degree nine.**

For a monic complex polynomial of degree nine all of whose zeros lie in the closed unit
disk, every zero has a critical point within distance one.

`#print axioms` on this theorem is the acceptance gate: it must show exactly
`[propext, Classical.choice, Quot.sound]`. -/
theorem sendov_degree_nine {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨D⟩ := RotData.exists_data hm hdeg hroots ha hcon
  exact no_data D

/-- **Sendov's conjecture in degree nine, without the monic normalization.**

Scaling by `1/leadingCoeff` changes neither the zeros of `p` nor those of `p'`, so the
monic case above is the general statement.  This is the form the conjecture is usually
quoted in: *every* complex polynomial of degree nine with all zeros in the closed unit
disk has, for each zero `a`, a critical point within distance one of `a`. -/
theorem sendov_degree_nine_general {p : ℂ[X]} (hdeg : p.natDegree = 9)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1 := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hc0 : p.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero hlc
  have hqm : (C p.leadingCoeff⁻¹ * p).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ hlc]
  have hqdeg : (C p.leadingCoeff⁻¹ * p).natDegree = 9 := by
    rw [Polynomial.natDegree_C_mul hc0]
    exact hdeg
  have hqroots : (C p.leadingCoeff⁻¹ * p).roots = p.roots := Polynomial.roots_C_mul p hc0
  have hdqroots : (derivative (C p.leadingCoeff⁻¹ * p)).roots = (derivative p).roots := by
    rw [derivative_C_mul, Polynomial.roots_C_mul _ hc0]
  have h := sendov_degree_nine hqm hqdeg (by rw [hqroots]; exact hroots)
    (by rw [hqroots]; exact ha)
  rwa [hdqroots] at h

end Sendov9.Final

#print axioms Sendov9.Final.separation
#print axioms Sendov9.Final.norm_I_lt
#print axioms Sendov9.Final.small_excluded
#print axioms Sendov9.Final.no_data
#print axioms Sendov9.Final.sendov_degree_nine
#print axioms Sendov9.Final.sendov_degree_nine_general
