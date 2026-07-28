import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.Rot

open Polynomial

/-!
# Rotating a counterexample so the distinguished zero is real

`Data` assumes `a : ℝ`; Sendov's statement has `a : ℂ`.  The reduction is the standard
"rotate so `a` is real and nonnegative", and it was the one `sorry` left in the
development (`Skeleton.exists_counterexample_of_not`).

Do it on the polynomial, via `f ↦ f.comp (C w * X)`.  Everything reduces to a single
fact about that map:

    (f.comp (C w · X)).roots = f.roots.map (· / w)          (`roots_comp_mul`)

which applies to `p` and to `p'` alike — that is why it is proved for a general nonzero
`f` rather than for a monic degree-9 polynomial.  Composition commutes with `derivative`
up to the constant `C w` (`derivative_comp`), and constants do not move roots, so the
critical points transform the same way as the zeros.

Then `|w| = 1` makes `· / w` an isometry, so "all roots in the closed disk" and "no
critical point within distance 1 of `a`" both transfer verbatim.  The reduction costs
nothing but bookkeeping — no inequality is weakened anywhere.

The proof of `roots_comp_mul` is: write `f = C (leadingCoeff f) · ∏(X - r)` over its own
root multiset (valid since ℂ is algebraically closed), push `comp` through the product,
and pull the `C w` out of each factor as `C w · (X - C (r/w))`.  The accumulated
`(C w)^n` is a nonzero constant, hence invisible to `roots`.

Sendov's conjecture in degree nine remains unproven.
-/

/-- Roots of a complex polynomial are counted by its degree. -/
theorem card_roots_eq (f : ℂ[X]) : Multiset.card f.roots = f.natDegree := by
  have h : (f.map (RingHom.id ℂ)).Splits := IsAlgClosed.splits_codomain f
  rw [Polynomial.map_id] at h
  exact splits_iff_card_roots.mp h

/-- `(X - C r).comp (C w * X) = C w * (X - C (r/w))`. -/
theorem factor_comp {w r : ℂ} (hw : w ≠ 0) :
    (X - C r).comp (C w * X) = C w * (X - C (r / w)) := by
  have hr : w * (r / w) = r := by field_simp
  rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, hr]

/-- **The core.**  Composing with `X ↦ wX` divides every root by `w`. -/
theorem roots_comp_mul {f : ℂ[X]} (hf : f ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    (f.comp (C w * X)).roots = f.roots.map (fun r => r / w) := by
  -- `f = C (leadingCoeff f) * ∏_{r ∈ roots} (X - C r)`
  have hsplit : C f.leadingCoeff * (f.roots.map fun r => X - C r).prod = f :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_eq f)
  -- collect the accumulated constant into ONE `C`, so `roots_C_mul` applies directly
  set k : ℂ := f.leadingCoeff * w ^ (Multiset.card f.roots) with hk
  have hcomp : f.comp (C w * X)
      = C k * (f.roots.map fun r => X - C (r / w)).prod := by
    conv_lhs => rw [← hsplit]
    rw [mul_comp, C_comp, multiset_prod_comp, Multiset.map_map]
    have hfac : ∀ r ∈ f.roots, ((fun q : ℂ[X] => q.comp (C w * X)) ∘ fun r => X - C r) r
        = C w * (X - C (r / w)) := by
      intro r _
      simpa using factor_comp (w := w) (r := r) hw
    rw [Multiset.map_congr rfl hfac]
    rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
    rw [hk, C_mul, C_pow]
    ring
  rw [hcomp]
  have hk0 : k ≠ 0 := by
    rw [hk]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hf) (pow_ne_zero _ hw)
  rw [roots_C_mul _ hk0]
  -- reassociate the map so `roots_multiset_prod_X_sub_C` matches on the nose
  have hmm : (f.roots.map fun r => X - C (r / w))
      = (f.roots.map fun r => r / w).map (fun a => X - C a) := by
    rw [Multiset.map_map]
    rfl
  rw [hmm]
  exact roots_multiset_prod_X_sub_C (f.roots.map fun r => r / w)

/-- The composition is nonzero. -/
theorem comp_mul_ne_zero {f : ℂ[X]} (hf : f ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    f.comp (C w * X) ≠ 0 := by
  intro hcon
  have h := roots_comp_mul hf hw
  rw [hcon] at h
  simp only [roots_zero] at h
  have hcard : Multiset.card f.roots = 0 := by
    have := congrArg Multiset.card h.symm
    simpa using this
  -- a nonzero polynomial with no roots over ℂ is a constant, so `f.comp` is that constant
  have hdeg : f.natDegree = 0 := by rw [← card_roots_eq f, hcard]
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hdeg
  rw [← hc] at hcon
  rw [C_comp] at hcon
  rw [← hc] at hf
  exact hf (by rw [hcon])

/-! ### `w` on the unit circle acts by isometry -/

theorem norm_div_unit {w : ℂ} (hw : ‖w‖ = 1) (r : ℂ) : ‖r / w‖ = ‖r‖ := by
  rw [norm_div, hw, div_one]

theorem norm_sub_div_unit {w : ℂ} (hw : ‖w‖ = 1) (a r : ℂ) :
    ‖a / w - r / w‖ = ‖a - r‖ := by
  rw [div_sub_div_same, norm_div, hw, div_one]

/-- **The rotation.**  For `a ≠ 0`, `w = a/‖a‖` has modulus one and sends `a` to `‖a‖`. -/
theorem rotator {a : ℂ} (ha : a ≠ 0) :
    ‖a / ‖a‖‖ = 1 ∧ a / (a / ‖a‖) = (‖a‖ : ℂ) := by
  have hn : (‖a‖ : ℂ) ≠ 0 := by
    simpa using (norm_ne_zero_iff.mpr ha)
  constructor
  · rw [norm_div]
    simp [norm_ne_zero_iff.mpr ha]
  · field_simp

/-- The derivative transforms the same way: `p'`'s roots are also divided by `w`.

`derivative_comp` contributes the factor `C w`, and a nonzero constant does not move
roots — which is exactly why the critical points rotate rigidly with the zeros. -/
theorem roots_derivative_comp {f : ℂ[X]} (hf : derivative f ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    (derivative (f.comp (C w * X))).roots = (derivative f).roots.map (fun r => r / w) := by
  rw [derivative_comp, derivative_mul, derivative_C, derivative_X]
  simp only [zero_mul, mul_one, zero_add]
  rw [roots_C_mul _ hw]
  exact roots_comp_mul hf hw

end Sendov9.Rot

#print axioms Sendov9.Rot.card_roots_eq
#print axioms Sendov9.Rot.factor_comp
#print axioms Sendov9.Rot.roots_comp_mul
#print axioms Sendov9.Rot.comp_mul_ne_zero
#print axioms Sendov9.Rot.norm_div_unit
#print axioms Sendov9.Rot.norm_sub_div_unit
#print axioms Sendov9.Rot.rotator
#print axioms Sendov9.Rot.roots_derivative_comp
