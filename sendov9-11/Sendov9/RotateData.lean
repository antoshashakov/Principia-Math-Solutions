import Mathlib
import Sendov9.Rotate
import Sendov9.Data

set_option maxHeartbeats 4000000

namespace Sendov9.RotData

open Polynomial

/-!
# The rotation bridge, assembled: a hypothetical counterexample yields a `Data`

`Rotate.lean` supplied the mathematics; this file spends it.  Given a monic degree-nine
`p` with all zeros in the closed unit disk, a zero `a : ℂ`, and the counterexample
assumption that no critical point lies within distance one of `a`, we produce a `Data` —
whose distinguished zero is the **real** number `‖a‖`.

The rotator is `w = a/‖a‖` (and `w = 1` when `a = 0`, where there is nothing to rotate),
and the rotated polynomial is

    q = C ((w⁹)⁻¹) · p.comp (C w · X).

`Rot.roots_comp_mul` and `Rot.roots_derivative_comp` say the zeros and the critical
points are both divided by `w`; the leading constant is there only to keep `q` monic and
is invisible to `roots`.  Since `‖w‖ = 1`, division by `w` is an isometry, so both the
disk hypothesis and the separation hypothesis transfer with no loss — which matters,
because the certificates downstream have no margin to spare.

With this, `Skeleton.exists_counterexample_of_not` is no longer a `sorry`:
`Data.toCounterexample` composed with `no_data` below is the whole bridge from a
polynomial to the `Counterexample` the analytic development consumes.

Sendov's conjecture in degree nine remains unproven.
-/

/-- The rotator: unit modulus, and it sends `a` to `‖a‖`. -/
noncomputable def wOf (a : ℂ) : ℂ := if a = 0 then 1 else a / (‖a‖ : ℂ)

theorem norm_wOf (a : ℂ) : ‖wOf a‖ = 1 := by
  unfold wOf
  split_ifs with h
  · simp
  · rw [norm_div]
    simp [norm_ne_zero_iff.mpr h]

theorem wOf_ne_zero (a : ℂ) : wOf a ≠ 0 := by
  intro hcon
  have := norm_wOf a
  rw [hcon] at this
  simp at this

/-- **The rotation sends `a` to the nonnegative real `‖a‖`.** -/
theorem div_wOf (a : ℂ) : a / wOf a = (‖a‖ : ℂ) := by
  unfold wOf
  split_ifs with h
  · simp [h]
  · have hn : (‖a‖ : ℂ) ≠ 0 := by simpa using (norm_ne_zero_iff.mpr h)
    field_simp

/-- The rotated polynomial. -/
noncomputable def rotP (p : ℂ[X]) (a : ℂ) : ℂ[X] :=
  C (((wOf a) ^ 9)⁻¹) * p.comp (C (wOf a) * X)

variable {p : ℂ[X]} {a : ℂ}

theorem rotP_roots (hp : p ≠ 0) :
    (rotP p a).roots = p.roots.map (fun r => r / wOf a) := by
  have hw := wOf_ne_zero a
  rw [rotP, roots_C_mul _ (inv_ne_zero (pow_ne_zero 9 hw))]
  exact Rot.roots_comp_mul hp hw

theorem rotP_deriv_roots (hp : derivative p ≠ 0) :
    (derivative (rotP p a)).roots = (derivative p).roots.map (fun r => r / wOf a) := by
  have hw := wOf_ne_zero a
  rw [rotP, derivative_mul, derivative_C, zero_mul, zero_add,
    roots_C_mul _ (inv_ne_zero (pow_ne_zero 9 hw))]
  exact Rot.roots_derivative_comp hp hw

theorem rotP_monic (hm : p.Monic) (hdeg : p.natDegree = 9) : (rotP p a).Monic := by
  have hw := wOf_ne_zero a
  have hlin : (C (wOf a) * X).natDegree = 1 := by
    rw [natDegree_C_mul hw, natDegree_X]
  have hlc : (p.comp (C (wOf a) * X)).leadingCoeff = (wOf a) ^ 9 := by
    rw [leadingCoeff_comp (by rw [hlin]; norm_num), hm.leadingCoeff, hdeg, one_mul]
    congr 1
    rw [leadingCoeff, hlin, coeff_C_mul, coeff_X_one, mul_one]
  unfold Monic leadingCoeff
  rw [rotP, ← leadingCoeff, leadingCoeff_mul, leadingCoeff_C, hlc]
  field_simp

theorem rotP_natDegree (hm : p.Monic) (hdeg : p.natDegree = 9) :
    (rotP p a).natDegree = 9 := by
  have hp : p ≠ 0 := hm.ne_zero
  have h1 : Multiset.card (rotP p a).roots = 9 := by
    rw [rotP_roots hp, Multiset.card_map, Rot.card_roots_eq p, hdeg]
  rw [← Rot.card_roots_eq (rotP p a), h1]

/-- **The bridge.**  A hypothetical degree-nine counterexample yields a `Data`. -/
theorem exists_data (hm : p.Monic) (hdeg : p.natDegree = 9)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (ha : a ∈ p.roots)
    (hno : ∀ z ∈ (derivative p).roots, 1 < ‖a - z‖) :
    Nonempty Data := by
  have hp : p ≠ 0 := hm.ne_zero
  have hw : ‖wOf a‖ = 1 := norm_wOf a
  have hdp : (derivative p).natDegree = 8 := Anchor2.derivative_natDegree hdeg
  have hdp0 : derivative p ≠ 0 := by
    intro hcon
    rw [hcon] at hdp
    simp at hdp
  refine ⟨{
    p := rotP p a
    hmonic := rotP_monic hm hdeg
    hdeg := rotP_natDegree hm hdeg
    a := ‖a‖
    ha0 := norm_nonneg a
    ha1 := hroots a ha
    haroot := ?_
    hroots := ?_
    hcrit := ?_ }⟩
  · -- `‖a‖` is a root of the rotated polynomial, because `a/w = ‖a‖`
    rw [rotP_roots hp]
    have : a / wOf a ∈ p.roots.map (fun r => r / wOf a) := Multiset.mem_map_of_mem _ ha
    rwa [div_wOf a] at this
  · -- the disk hypothesis transfers, since `‖·/w‖ = ‖·‖`
    intro z hz
    rw [rotP_roots hp] at hz
    obtain ⟨r, hr, hrz⟩ := Multiset.mem_map.mp hz
    rw [← hrz, Rot.norm_div_unit hw]
    exact hroots r hr
  · -- the separation hypothesis transfers, since `‖a/w - ζ/w‖ = ‖a - ζ‖`
    intro z hz
    rw [rotP_deriv_roots hdp0] at hz
    obtain ⟨zeta, hzeta, hzz⟩ := Multiset.mem_map.mp hz
    rw [← hzz, ← div_wOf a, Rot.norm_sub_div_unit hw]
    exact hno zeta hzeta

end Sendov9.RotData

#print axioms Sendov9.RotData.norm_wOf
#print axioms Sendov9.RotData.wOf_ne_zero
#print axioms Sendov9.RotData.div_wOf
#print axioms Sendov9.RotData.rotP_roots
#print axioms Sendov9.RotData.rotP_deriv_roots
#print axioms Sendov9.RotData.rotP_monic
#print axioms Sendov9.RotData.rotP_natDegree
#print axioms Sendov9.RotData.exists_data
