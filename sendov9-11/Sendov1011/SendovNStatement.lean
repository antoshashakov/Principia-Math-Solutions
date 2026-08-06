import Mathlib
import Sendov10Final
import Sendov11Final

/-!
# Sendov degrees 10/11 — the Mathlib-vocabulary statement layer

`SendovN.Final10.sendov10 : Sendov911Capstone.Sendov 10` and
`SendovN.Final11.sendov11 : Sendov911Capstone.Sendov 11` state the theorem
through the capstone's `Sendov` predicate (`(derivative p).IsRoot ζ`).  This
file restates both degrees in the exact shape of the degree-9 pair
(`Sendov9.Final.sendov_degree_nine{,_general}`): membership in
`(derivative p).roots`, pure Mathlib vocabulary, monic and general forms.

Two bridges, both elementary:
* `IsRoot → mem roots` needs `derivative p ≠ 0`, which is
  `Polynomial.derivative_ne_zero` (the degree is 10 or 11, hence nonzero);
* the general form scales by `leadingCoeff⁻¹` exactly as in
  `Sendov9/Final.lean` (scaling changes neither the zeros of `p` nor of `p'`).

Acceptance gate: every `#print axioms` line below must show exactly
`[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

open Polynomial

namespace SendovN.Final10

/-- **Sendov's conjecture in degree ten (monic form).** -/
theorem sendov_degree_ten {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 10)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1 := by
  obtain ⟨ζ, hζ, hle⟩ := sendov10 p hm hdeg hroots a ha
  have hd : derivative p ≠ 0 := derivative_ne_zero.mpr (by rw [hdeg]; norm_num)
  exact ⟨ζ, (mem_roots hd).mpr hζ, hle⟩

/-- **Sendov's conjecture in degree ten.**

Scaling by `1/leadingCoeff` changes neither the zeros of `p` nor those of `p'`,
so the monic case above is the general statement. -/
theorem sendov_degree_ten_general {p : ℂ[X]} (hdeg : p.natDegree = 10)
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
  have hqdeg : (C p.leadingCoeff⁻¹ * p).natDegree = 10 := by
    rw [Polynomial.natDegree_C_mul hc0]
    exact hdeg
  have hqroots : (C p.leadingCoeff⁻¹ * p).roots = p.roots := Polynomial.roots_C_mul p hc0
  have hdqroots : (derivative (C p.leadingCoeff⁻¹ * p)).roots = (derivative p).roots := by
    rw [derivative_C_mul, Polynomial.roots_C_mul _ hc0]
  have h := sendov_degree_ten hqm hqdeg (by rw [hqroots]; exact hroots)
    (by rw [hqroots]; exact ha)
  rwa [hdqroots] at h

end SendovN.Final10

namespace SendovN.Final11

/-- **Sendov's conjecture in degree eleven (monic form).** -/
theorem sendov_degree_eleven {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 11)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1 := by
  obtain ⟨ζ, hζ, hle⟩ := sendov11 p hm hdeg hroots a ha
  have hd : derivative p ≠ 0 := derivative_ne_zero.mpr (by rw [hdeg]; norm_num)
  exact ⟨ζ, (mem_roots hd).mpr hζ, hle⟩

/-- **Sendov's conjecture in degree eleven.** -/
theorem sendov_degree_eleven_general {p : ℂ[X]} (hdeg : p.natDegree = 11)
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
  have hqdeg : (C p.leadingCoeff⁻¹ * p).natDegree = 11 := by
    rw [Polynomial.natDegree_C_mul hc0]
    exact hdeg
  have hqroots : (C p.leadingCoeff⁻¹ * p).roots = p.roots := Polynomial.roots_C_mul p hc0
  have hdqroots : (derivative (C p.leadingCoeff⁻¹ * p)).roots = (derivative p).roots := by
    rw [derivative_C_mul, Polynomial.roots_C_mul _ hc0]
  have h := sendov_degree_eleven hqm hqdeg (by rw [hqroots]; exact hroots)
    (by rw [hqroots]; exact ha)
  rwa [hdqroots] at h

end SendovN.Final11

#print axioms SendovN.Final10.sendov_degree_ten
#print axioms SendovN.Final10.sendov_degree_ten_general
#print axioms SendovN.Final11.sendov_degree_eleven
#print axioms SendovN.Final11.sendov_degree_eleven_general
