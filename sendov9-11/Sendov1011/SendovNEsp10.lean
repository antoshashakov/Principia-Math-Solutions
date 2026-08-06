import Mathlib
import SendovNSigma
import SendovNEsp
import SendovNEsymm

set_option maxHeartbeats 4000000

/-!
# D10-2: the degree-10 `c`-table (`N = 9`)

The table `(c₂,…,c₉) = (9/2, 9, 2201/100, 2201/100, 877/50, 217/20, 481/100, 1)`,
transcribed from `certificates/degree10_verify.py` (`C_MAJ`) — never retyped from
the paper.  Sources:

* `m = 2` — `EspEasy.e2_bound` (centred Newton at order 2, `c₂ = N/2`);
* `m = 3` — `EspEasy.e3_bound` (`c₃ = N`, valid since `N = 9 ≤ 10`);
* `m = 4…8` — `EspCauchy.esymm_le`, each a single `norm_num` exact-squaring check
  `c_m² · m^m · (9−m)^(9−m) ≥ 9⁹` (the verifier's own assertions);
* `m = 9` — `EspEasy.eN_bound` (AM–GM, `c₉ = 1`).

`cTable10` assembles them in the exact hypothesis shape the P8 row machinery
consumes (`∀ m ∈ Icc 2 N, ‖esD D m‖ ≤ c m · η^m`).
-/

namespace SendovN.CTab10

open Finset

/-- The degree-10 constant table `(c₂,…,c₉)`, from `degree10_verify.py`'s `C_MAJ`. -/
noncomputable def c10 : ℕ → ℝ := fun m =>
  if m = 2 then 9/2 else if m = 3 then 9 else if m = 4 then 2201/100
  else if m = 5 then 2201/100 else if m = 6 then 877/50 else if m = 7 then 217/20
  else if m = 8 then 481/100 else 1

theorem c10_nonneg : ∀ m, 0 ≤ c10 m := by
  intro m
  unfold c10
  split_ifs <;> norm_num

/-- **The degree-10 `c`-table**: `‖e_m(D)‖ ≤ c_m η^m` for all `2 ≤ m ≤ 9`. -/
theorem cTable10 (D : Fin 9 → ℂ) (eta : ℝ) (heta : 0 ≤ eta) (hz : ∑ j, D j = 0)
    (hD : ∑ j, ‖D j‖ ^ 2 ≤ 9 * eta ^ 2) :
    ∀ m ∈ Finset.Icc 2 9, ‖esD D m‖ ≤ c10 m * eta ^ m := by
  have hDc : ∑ j, ‖D j‖ ^ 2 ≤ ((9 : ℕ) : ℝ) * eta ^ 2 := by exact_mod_cast hD
  intro m hm
  simp only [Finset.mem_Icc] at hm
  obtain ⟨hm2, hm9⟩ := hm
  interval_cases m
  · -- m = 2 : centred Newton
    have h := EspEasy.e2_bound D eta hz hDc
    push_cast at h
    simpa [c10] using h
  · -- m = 3 : max-coordinate route
    have h := EspEasy.e3_bound (by norm_num) D eta heta hz hDc
    push_cast at h
    simpa [c10] using h
  · -- m = 4 : Cauchy, (2201/100)²·4⁴·5⁵ ≥ 9⁹
    have h := EspCauchy.esymm_le (m := 4) (by norm_num) (by norm_num)
      (by norm_num : (0:ℝ) ≤ 2201/100) (by norm_num) D eta heta hz hDc
    simpa [c10] using h
  · -- m = 5 : Cauchy, (2201/100)²·5⁵·4⁴ ≥ 9⁹
    have h := EspCauchy.esymm_le (m := 5) (by norm_num) (by norm_num)
      (by norm_num : (0:ℝ) ≤ 2201/100) (by norm_num) D eta heta hz hDc
    simpa [c10] using h
  · -- m = 6 : Cauchy, (877/50)²·6⁶·3³ ≥ 9⁹
    have h := EspCauchy.esymm_le (m := 6) (by norm_num) (by norm_num)
      (by norm_num : (0:ℝ) ≤ 877/50) (by norm_num) D eta heta hz hDc
    simpa [c10] using h
  · -- m = 7 : Cauchy, (217/20)²·7⁷·2² ≥ 9⁹
    have h := EspCauchy.esymm_le (m := 7) (by norm_num) (by norm_num)
      (by norm_num : (0:ℝ) ≤ 217/20) (by norm_num) D eta heta hz hDc
    simpa [c10] using h
  · -- m = 8 : Cauchy, (481/100)²·8⁸·1 ≥ 9⁹
    have h := EspCauchy.esymm_le (m := 8) (by norm_num) (by norm_num)
      (by norm_num : (0:ℝ) ≤ 481/100) (by norm_num) D eta heta hz hDc
    simpa [c10] using h
  · -- m = 9 : AM–GM
    have h := EspEasy.eN_bound (by norm_num) D eta heta hDc
    simpa [c10] using h

end SendovN.CTab10

#print axioms SendovN.CTab10.c10_nonneg
#print axioms SendovN.CTab10.cTable10
