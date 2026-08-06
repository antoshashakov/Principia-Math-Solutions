import Mathlib
import Sendov9.Rotate
import SendovNData

set_option maxHeartbeats 4000000

/-!
# The rotation bridge, parametric in the degree (port of `Sendov9/RotateData.lean`)

Given a monic degree-`n` polynomial with all zeros in the closed unit disk, a
zero `a : ℂ`, and the counterexample assumption that no critical point lies
within distance one of `a`, produce a `DataN n` whose distinguished zero is the
**real** number `‖a‖`.  The generic rotation lemmas are consumed verbatim from
`Sendov9.Rot` (copied from the sendov9-11 repo at the same toolchain); the only
degree-9-specific content of the original — the numeral `9` in the monicity and
degree bookkeeping — becomes `n` with `2 ≤ n`.
-/

namespace SendovN.RotDataN

open Polynomial Sendov9

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

/-- The rotated polynomial (kept monic by the leading constant). -/
noncomputable def rotP (n : ℕ) (p : ℂ[X]) (a : ℂ) : ℂ[X] :=
  C (((wOf a) ^ n)⁻¹) * p.comp (C (wOf a) * X)

variable {n : ℕ} {p : ℂ[X]} {a : ℂ}

theorem rotP_roots (hp : p ≠ 0) :
    (rotP n p a).roots = p.roots.map (fun r => r / wOf a) := by
  have hw := wOf_ne_zero a
  rw [rotP, roots_C_mul _ (inv_ne_zero (pow_ne_zero n hw))]
  exact Rot.roots_comp_mul hp hw

theorem rotP_deriv_roots (hp : derivative p ≠ 0) :
    (derivative (rotP n p a)).roots = (derivative p).roots.map (fun r => r / wOf a) := by
  have hw := wOf_ne_zero a
  rw [rotP, derivative_mul, derivative_C, zero_mul, zero_add,
    roots_C_mul _ (inv_ne_zero (pow_ne_zero n hw))]
  exact Rot.roots_derivative_comp hp hw

theorem rotP_monic (hm : p.Monic) (hdeg : p.natDegree = n) : (rotP n p a).Monic := by
  have hw := wOf_ne_zero a
  have hlin : (C (wOf a) * X).natDegree = 1 := by
    rw [natDegree_C_mul hw, natDegree_X]
  have hlc : (p.comp (C (wOf a) * X)).leadingCoeff = (wOf a) ^ n := by
    rw [leadingCoeff_comp (by rw [hlin]; norm_num), hm.leadingCoeff, hdeg, one_mul]
    congr 1
    rw [leadingCoeff, hlin, coeff_C_mul, coeff_X_one, mul_one]
  unfold Monic leadingCoeff
  rw [rotP, ← leadingCoeff, leadingCoeff_mul, leadingCoeff_C, hlc]
  field_simp

theorem rotP_natDegree (hm : p.Monic) (hdeg : p.natDegree = n) :
    (rotP n p a).natDegree = n := by
  have hp : p ≠ 0 := hm.ne_zero
  have h1 : Multiset.card (rotP n p a).roots = n := by
    rw [rotP_roots hp, Multiset.card_map, Rot.card_roots_eq p, hdeg]
  rw [← Rot.card_roots_eq (rotP n p a), h1]

/-- **The bridge.**  A hypothetical degree-`n` counterexample yields a `DataN n`. -/
theorem exists_data (hn : 2 ≤ n) (hm : p.Monic) (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (ha : a ∈ p.roots)
    (hno : ∀ z ∈ (derivative p).roots, 1 < ‖a - z‖) :
    Nonempty (DataN n) := by
  have hp : p ≠ 0 := hm.ne_zero
  have hw : ‖wOf a‖ = 1 := norm_wOf a
  have hdlc : (derivative p).leadingCoeff = n :=
    Anchor2.derivative_leadingCoeff hm (by omega) hdeg
  have hdp0 : derivative p ≠ 0 := by
    intro hcon
    rw [hcon] at hdlc
    simp only [leadingCoeff_zero] at hdlc
    have hzero : n = 0 := by exact_mod_cast hdlc.symm
    omega
  refine ⟨{
    hn := hn
    p := rotP n p a
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

end SendovN.RotDataN

#print axioms SendovN.RotDataN.rotP_roots
#print axioms SendovN.RotDataN.rotP_deriv_roots
#print axioms SendovN.RotDataN.rotP_monic
#print axioms SendovN.RotDataN.rotP_natDegree
#print axioms SendovN.RotDataN.exists_data
