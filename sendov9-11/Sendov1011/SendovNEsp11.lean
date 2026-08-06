import Mathlib
import SendovNSigma
import SendovNEsp
import SendovNEsymm

set_option maxHeartbeats 4000000

/-!
# D11-2: the degree-11 `c`-table (`N = 10`)

The table `(c₂,…,c₁₀) = (5, 10, 1447/50, 32, 3125/108, 2121/100, 3125/256,
509/100, 1)`, transcribed from `emit_boxes11v2.py`'s `C` (line-for-line
`certificates/degree11_verify.py` with the **Cauchy** `c₄ = 1447/50` replacing
Schoenberg's `70/3`, per the c4-experiment decision — the 531 `boxes11v2/` files
were regenerated against exactly this table).  Sources:

* `m = 2` — `EspEasy.e2_bound` (`c₂ = N/2 = 5`);
* `m = 3` — `EspEasy.e3_bound` (`c₃ = N = 10`, the boundary case of `N ≤ 10`);
* `m = 4` — `EspCauchy.c4_deg11` (already banked in `SendovNEsymm`);
* `m = 5…9` — `EspCauchy.esymm_le`, one `norm_num` squaring check each
  `c_m² · m^m · (10−m)^(10−m) ≥ 10¹⁰` (`c₅, c₆, c₈` are exact Cauchy:
  `32²·5⁵·5⁵ = (3125/108)²·6⁶·4⁴ = (3125/256)²·8⁸·2² = 10¹⁰`);
* `m = 10` — `EspEasy.eN_bound` (`c₁₀ = 1`).
-/

namespace SendovN.CTab11

open Finset

/-- The degree-11 constant table `(c₂,…,c₁₀)`, from `emit_boxes11v2.py`'s `C`
(Cauchy `c₄ = 1447/50`). -/
noncomputable def c11 : ℕ → ℝ := fun m =>
  if m = 2 then 5 else if m = 3 then 10 else if m = 4 then 1447/50
  else if m = 5 then 32 else if m = 6 then 3125/108 else if m = 7 then 2121/100
  else if m = 8 then 3125/256 else if m = 9 then 509/100 else 1

theorem c11_nonneg : ∀ m, 0 ≤ c11 m := by
  intro m
  unfold c11
  split_ifs <;> norm_num

/-- **The degree-11 `c`-table**: `‖e_m(D)‖ ≤ c_m η^m` for all `2 ≤ m ≤ 10`. -/
theorem cTable11 (D : Fin 10 → ℂ) (eta : ℝ) (heta : 0 ≤ eta) (hz : ∑ j, D j = 0)
    (hD : ∑ j, ‖D j‖ ^ 2 ≤ 10 * eta ^ 2) :
    ∀ m ∈ Finset.Icc 2 10, ‖esD D m‖ ≤ c11 m * eta ^ m := by
  have hDc : ∑ j, ‖D j‖ ^ 2 ≤ ((10 : ℕ) : ℝ) * eta ^ 2 := by exact_mod_cast hD
  intro m hm
  simp only [Finset.mem_Icc] at hm
  obtain ⟨hm2, hm10⟩ := hm
  interval_cases m
  · -- m = 2 : centred Newton, 10/2 = 5
    have h := EspEasy.e2_bound D eta hz hDc
    push_cast at h
    have h5 : ((10 : ℝ)) / 2 = 5 := by norm_num
    rw [h5] at h
    simpa [c11] using h
  · -- m = 3 : max-coordinate route (boundary case of N ≤ 10)
    have h := EspEasy.e3_bound (by norm_num) D eta heta hz hDc
    push_cast at h
    simpa [c11] using h
  · -- m = 4 : the banked Cauchy c₄ = 1447/50
    have h := EspCauchy.c4_deg11 D eta heta hz hD
    simpa [c11] using h
  · -- m = 5 : exact Cauchy, 32²·5⁵·5⁵ = 10¹⁰
    have h := EspCauchy.esymm_le (m := 5) (by norm_num) (by norm_num)
      (by norm_num : (0:ℝ) ≤ 32) (by norm_num) D eta heta hz hDc
    simpa [c11] using h
  · -- m = 6 : exact Cauchy, (3125/108)²·6⁶·4⁴ = 10¹⁰
    have h := EspCauchy.esymm_le (m := 6) (by norm_num) (by norm_num)
      (by norm_num : (0:ℝ) ≤ 3125/108) (by norm_num) D eta heta hz hDc
    simpa [c11] using h
  · -- m = 7 : Cauchy, (2121/100)²·7⁷·3³ ≥ 10¹⁰
    have h := EspCauchy.esymm_le (m := 7) (by norm_num) (by norm_num)
      (by norm_num : (0:ℝ) ≤ 2121/100) (by norm_num) D eta heta hz hDc
    simpa [c11] using h
  · -- m = 8 : exact Cauchy, (3125/256)²·8⁸·2² = 10¹⁰
    have h := EspCauchy.esymm_le (m := 8) (by norm_num) (by norm_num)
      (by norm_num : (0:ℝ) ≤ 3125/256) (by norm_num) D eta heta hz hDc
    simpa [c11] using h
  · -- m = 9 : Cauchy, (509/100)²·9⁹·1 ≥ 10¹⁰
    have h := EspCauchy.esymm_le (m := 9) (by norm_num) (by norm_num)
      (by norm_num : (0:ℝ) ≤ 509/100) (by norm_num) D eta heta hz hDc
    simpa [c11] using h
  · -- m = 10 : AM–GM
    have h := EspEasy.eN_bound (by norm_num) D eta heta hDc
    simpa [c11] using h

end SendovN.CTab11

#print axioms SendovN.CTab11.c11_nonneg
#print axioms SendovN.CTab11.cTable11
