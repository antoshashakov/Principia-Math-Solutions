import Mathlib
import Sendov9.Data

set_option maxHeartbeats 4000000

namespace Sendov9.Segment

open Polynomial Finset

/-!
# Lemma 2.1's input: the apolar integral vanishes at every other zero

Grace–Walsh–Szegő is applied in the paper to the family `uⱼ = (a - zₖ)·Yⱼ`, and what
makes the application legal is that the corresponding integral is **zero**.  That comes
from the fundamental theorem of calculus along the segment `[a, zₖ]`:

    (zₖ - a)·∫₀¹ p'(a + (zₖ - a)t) dt = p(zₖ) - p(a) = 0,

both endpoints being zeros of `p`.  Since `zₖ ≠ a` (`Anchor2.erase_ne_zero` — a repeated
root at `a` would make `p'(a) = 0`, but every critical point is at distance `> 1`), the
integral itself vanishes.

Substituting `p' = 9∏ⱼ(X - ζⱼ)` and pulling `∏ⱼ(a - ζⱼ)` out factor by factor,

    a + (zₖ - a)t - ζⱼ = (a - ζⱼ)·(1 - t·(a - zₖ)Yⱼ),      Yⱼ = (a - ζⱼ)⁻¹,

so the constant `9∏ⱼ(a - ζⱼ)` — nonzero, since no critical point is at `a` — divides
out and leaves exactly

    ∫₀¹ ∏ⱼ (1 - t uⱼ) dt = 0,       uⱼ = (a - zₖ)·Yⱼ.

`norm_u_lt` records the other half of the GWS hypothesis: `‖uⱼ‖ < ‖a - zₖ‖`, because
`‖a - ζⱼ‖ > 1` makes every `‖Yⱼ‖ < 1`.

The FTC step is done on the *polynomial* `q = p ∘ (a + (z-a)X)` rather than through a
general chain rule: `Polynomial.derivative_comp` gives `q' = (z-a)·p'∘(…)` outright, and
`HasDerivAt.comp_ofReal` restricts the ℂ-derivative to the real segment.

Sendov's conjecture in degree nine remains unproven.
-/

/-! ### The fundamental theorem of calculus for a polynomial on `[0,1] ⊆ ℝ` -/

/-- `∫₀¹ q'(t) dt = q(1) - q(0)`, along the real axis. -/
theorem integral_poly_deriv (q : ℂ[X]) :
    (∫ t in (0:ℝ)..1, (derivative q).eval (t : ℂ)) = q.eval 1 - q.eval 0 := by
  have hd : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y : ℝ => q.eval (y : ℂ)) ((derivative q).eval (s : ℂ)) s :=
    fun s _ => (q.hasDerivAt (s : ℂ)).comp_ofReal
  have hint : IntervalIntegrable (fun s : ℝ => (derivative q).eval (s : ℂ))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  simpa using h

/-- **FTC along the segment `[A, z]`.** -/
theorem integral_segment (p : ℂ[X]) (A z : ℂ) :
    (z - A) * (∫ t in (0:ℝ)..1, (derivative p).eval (A + (z - A) * (t : ℂ)))
      = p.eval z - p.eval A := by
  set q : ℂ[X] := p.comp (C A + C (z - A) * X) with hq
  have hqe : ∀ x : ℂ, q.eval x = p.eval (A + (z - A) * x) := by
    intro x
    rw [hq, eval_comp]
    simp
  have hdq : derivative q = C (z - A) * (derivative p).comp (C A + C (z - A) * X) := by
    rw [hq, derivative_comp]
    congr 1
    simp
  have hdqe : ∀ t : ℝ, (derivative q).eval (t : ℂ)
      = (z - A) * (derivative p).eval (A + (z - A) * (t : ℂ)) := by
    intro t
    rw [hdq, eval_mul, eval_C, eval_comp]
    simp
  have h := integral_poly_deriv q
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
    (z - A) * (derivative p).eval (A + (z - A) * (t : ℂ))) (fun t _ => hdqe t)] at h
  rw [intervalIntegral.integral_const_mul] at h
  rw [h, hqe, hqe]
  norm_num

/-! ### The apolar integral at a second zero -/

variable (D : Data)

/-- The GWS family attached to the `k`-th remaining zero: `uⱼ = (a - zₖ)·Yⱼ`. -/
noncomputable def uFam (k j : Fin 8) : ℂ :=
  ((D.a : ℂ) - D.z k) * ((D.a : ℂ) - D.zeta j)⁻¹

/-- `‖uⱼ‖ < ‖a - zₖ‖`, since every `‖a - ζⱼ‖ > 1`. -/
theorem norm_u_lt (k j : Fin 8) : ‖uFam D k j‖ < ‖(D.a : ℂ) - D.z k‖ := by
  have hz : (D.a : ℂ) - D.z k ≠ 0 := by
    have := Anchor2.erase_ne_zero D.hmonic D.hdeg D.haroot D.crit_ne _ (D.z_mem k)
    exact this
  have hpos : 0 < ‖(D.a : ℂ) - D.z k‖ := norm_pos_iff.mpr hz
  have hj := D.hzeta j
  have hjne : (D.a : ℂ) - D.zeta j ≠ 0 := D.zeta_ne j
  have hinv : ‖((D.a : ℂ) - D.zeta j)⁻¹‖ < 1 := by
    rw [norm_inv]
    rw [inv_lt_one_iff₀]
    right
    exact hj
  calc ‖uFam D k j‖ = ‖(D.a : ℂ) - D.z k‖ * ‖((D.a : ℂ) - D.zeta j)⁻¹‖ := by
        rw [uFam, norm_mul]
    _ < ‖(D.a : ℂ) - D.z k‖ * 1 := by
        -- `mul_lt_mul_left` needs a `MulRightStrictMono` instance that ℝ does not carry
        -- in this form; the explicit positivity lemma applies directly.
        exact mul_lt_mul_of_pos_left hinv hpos
    _ = ‖(D.a : ℂ) - D.z k‖ := mul_one _

/-- **The apolar integral vanishes.**  This is the hypothesis Grace–Walsh–Szegő is
applied to in Lemma 2.1. -/
theorem integral_uFam_zero (k : Fin 8) :
    (∫ t in (0:ℝ)..1, ∏ j, (1 - (t : ℂ) * uFam D k j)) = 0 := by
  have hzroot : D.p.eval (D.z k) = 0 := by
    have hmem : D.z k ∈ D.p.roots := Multiset.mem_of_mem_erase (D.z_mem k)
    exact Polynomial.isRoot_of_mem_roots hmem
  have haroot : D.p.eval ((D.a : ℂ)) = 0 := Polynomial.isRoot_of_mem_roots D.haroot
  have hzne : D.z k - (D.a : ℂ) ≠ 0 := by
    have h := Anchor2.erase_ne_zero D.hmonic D.hdeg D.haroot D.crit_ne _ (D.z_mem k)
    intro hc
    exact h (by linear_combination -hc)
  -- the segment integral vanishes
  have hseg : (∫ t in (0:ℝ)..1,
      (derivative D.p).eval ((D.a : ℂ) + (D.z k - (D.a : ℂ)) * (t : ℂ))) = 0 := by
    have h := integral_segment D.p ((D.a : ℂ)) (D.z k)
    rw [hzroot, haroot, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hzne
  -- and the integrand factors
  have hzetaprod : ∀ x : ℂ,
      (derivative D.p).eval x = 9 * ∏ j, (x - D.zeta j) := by
    intro x
    rw [Anchor2.derivative_eval_prod D.hmonic D.hdeg x]
    congr 1
    exact (Extract.prod_map_ofMultiset _ D.zetacard (fun w => x - w)).symm
  have hfac : ∀ t : ℝ,
      (derivative D.p).eval ((D.a : ℂ) + (D.z k - (D.a : ℂ)) * (t : ℂ))
        = (9 * ∏ j, ((D.a : ℂ) - D.zeta j)) * ∏ j, (1 - (t : ℂ) * uFam D k j) := by
    intro t
    rw [hzetaprod, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [uFam]
    field_simp [D.zeta_ne j]
    ring
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
    (9 * ∏ j, ((D.a : ℂ) - D.zeta j)) * ∏ j, (1 - (t : ℂ) * uFam D k j))
    (fun t _ => hfac t), intervalIntegral.integral_const_mul] at hseg
  have hne : (9 : ℂ) * ∏ j, ((D.a : ℂ) - D.zeta j) ≠ 0 := by
    refine mul_ne_zero (by norm_num) ?_
    exact Finset.prod_ne_zero_iff.mpr fun j _ => D.zeta_ne j
  exact (mul_eq_zero.mp hseg).resolve_left hne

end Sendov9.Segment

#print axioms Sendov9.Segment.integral_poly_deriv
#print axioms Sendov9.Segment.integral_segment
#print axioms Sendov9.Segment.norm_u_lt
#print axioms Sendov9.Segment.integral_uFam_zero
