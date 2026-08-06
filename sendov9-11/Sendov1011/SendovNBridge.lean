import Mathlib
import SendovNData
import SendovNCore

set_option maxHeartbeats 4000000

/-!
# P3: `BridgeN` — the integral identity, `|I| < a/n`, and the segment integrals

Port of `Sendov9/Bridge5.lean` + `Sendov9/INormFull.lean` + `Sendov9/Segment.lean`,
parametric in `n ≥ 2`.

**Parity caveat honored:** at degree 9 there are `N = 8` remaining roots and
`∏ₖ(−zₖ) = ∏ₖ zₖ`; for general `n` the number `N = n − 1` may be odd, so the sign is
**never cancelled**: the identity is stated as `∫ = a·∏ₖ(−zₖ)/n` and the norm bound
uses `‖−zₖ‖ = ‖zₖ‖`.

Degree-9's `linear_combination hint / 9` becomes `eq_div_iff` + `Nat.cast_ne_zero`
(`ring` cannot cancel `n/n` for a symbolic cast).
-/

namespace SendovN.BridgeN

open Polynomial intervalIntegral Finset

/-- `p(0) = −a·∏(−r)` over the erased roots (verbatim from `Bridge5`, via
`Anchor2.factor_out`). -/
theorem eval_zero_eq {p : ℂ[X]} (hm : p.Monic) {a : ℂ} (ha : a ∈ p.roots) :
    p.eval 0 = -a * ((p.roots.erase a).map fun r => -r).prod := by
  conv_lhs => rw [Anchor2.factor_out hm ha]
  rw [eval_mul, eval_sub, eval_X, eval_C, zero_sub, eval_multiset_prod,
    Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun r _ => ?_
  simp

theorem integral_cpow_ofReal (a : ℝ) (k : ℕ) :
    (∫ t in (0:ℝ)..a, ((t : ℂ) ^ k)) = ((a ^ (k + 1) / (k + 1) : ℝ) : ℂ) := by
  have h : ∀ t : ℝ, ((t : ℂ) ^ k) = ((t ^ k : ℝ) : ℂ) := by
    intro t; push_cast; ring
  simp only [h]
  rw [intervalIntegral.integral_ofReal, integral_pow]
  push_cast
  simp

theorem eval_intervalIntegrable (q : ℂ[X]) (a : ℝ) :
    IntervalIntegrable (fun u : ℝ => q.eval (u : ℂ)) MeasureTheory.volume 0 a := by
  apply Continuous.intervalIntegrable
  fun_prop

/-- Polynomial FTC (verbatim from `Bridge5`). -/
theorem integral_deriv_eval (q : ℂ[X]) (a : ℝ) :
    (∫ u in (0:ℝ)..a, (derivative q).eval (u : ℂ)) = q.eval (a : ℂ) - q.eval 0 := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
      rw [derivative_add]
      have hint : ∀ s : ℂ[X], IntervalIntegrable
          (fun u : ℝ => (derivative s).eval (u : ℂ)) MeasureTheory.volume 0 a :=
        fun s => eval_intervalIntegrable (derivative s) a
      rw [show (fun u : ℝ => (derivative p + derivative r).eval (u : ℂ))
            = (fun u : ℝ => (derivative p).eval (u : ℂ) + (derivative r).eval (u : ℂ)) from by
          funext u; simp]
      rw [integral_add (hint p) (hint r), hp, hr]
      simp only [eval_add]
      ring
  | monomial m c =>
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp
      · rw [derivative_monomial]
        have hk : m - 1 + 1 = m := by omega
        have hne : (m : ℂ) ≠ 0 := by
          simp only [ne_eq, Nat.cast_eq_zero]
          omega
        rw [show (fun u : ℝ => (monomial (m - 1) (c * (m : ℂ))).eval (u : ℂ))
              = (fun u : ℝ => (c * (m : ℂ)) * (u : ℂ) ^ (m - 1)) from by
            funext u; simp [eval_monomial]]
        rw [integral_const_mul, integral_cpow_ofReal, hk]
        simp only [eval_monomial]
        rw [show ((0:ℂ)) ^ m = 0 from zero_pow (by omega)]
        have hcast : ((m - 1 : ℕ) : ℂ) = (m : ℂ) - 1 := by
          rw [Nat.cast_sub hm]; simp
        push_cast [hcast]
        rw [show ((m : ℂ) - 1 + 1) = (m : ℂ) from by ring,
          show c * (m : ℂ) * ((a : ℂ) ^ m / (m : ℂ))
              = c * (a : ℂ) ^ m * ((m : ℂ) / (m : ℂ)) from by ring,
          div_self hne, mul_one]
        ring

/-! ### The identity (sign kept) -/

/-- **`n·∫₀ᵃ ∏ⱼ(u − ζⱼ) du = a·∏ₖ(−zₖ)`**, in multiset form. -/
theorem n_mul_integral {p : ℂ[X]} (hm : p.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : p.natDegree = n) {a : ℝ} (ha : (a : ℂ) ∈ p.roots) :
    (n : ℂ) * (∫ u in (0:ℝ)..a, ((derivative p).roots.map fun z => (u : ℂ) - z).prod)
      = (a : ℂ) * ((p.roots.erase (a : ℂ)).map fun r => -r).prod := by
  have hint := integral_deriv_eval p a
  rw [show (fun u : ℝ => (derivative p).eval (u : ℂ))
        = (fun u : ℝ => (n : ℂ) * ((derivative p).roots.map fun z => (u : ℂ) - z).prod) from by
      funext u; exact Anchor2.derivative_eval_prod hm hn hdeg (u : ℂ)] at hint
  rw [integral_const_mul] at hint
  rw [Polynomial.isRoot_of_mem_roots ha, eval_zero_eq hm ha] at hint
  linear_combination hint

/-- **The identity, indexed by `Fin (n−1)`.**  The sign is **not** cancelled: `n − 1`
may be odd. -/
theorem integral_prod_zeta {p : ℂ[X]} (hm : p.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : p.natDegree = n) {a : ℝ} (ha : (a : ℂ) ∈ p.roots)
    (z zeta : Fin (n - 1) → ℂ)
    (hz : ∀ f : ℂ → ℂ, ∏ k, f (z k) = ((p.roots.erase (a : ℂ)).map f).prod)
    (hzeta : ∀ f : ℂ → ℂ, ∏ j, f (zeta j) = ((derivative p).roots.map f).prod) :
    (∫ u in (0:ℝ)..a, ∏ j, ((u : ℂ) - zeta j)) = (a : ℂ) * (∏ k, -(z k)) / n := by
  have hstep : ∀ u : ℝ, ∏ j, ((u : ℂ) - zeta j)
      = ((derivative p).roots.map fun w => (u : ℂ) - w).prod :=
    fun u => hzeta (fun w => (u : ℂ) - w)
  have hzz : ((p.roots.erase (a : ℂ)).map fun r => -r).prod = ∏ k, -(z k) :=
    (hz (fun r => -r)).symm
  have h := n_mul_integral hm hn hdeg ha
  rw [hzz] at h
  rw [show (fun u : ℝ => ∏ j, ((u : ℂ) - zeta j))
        = (fun u : ℝ => ((derivative p).roots.map fun w => (u : ℂ) - w).prod) from
      funext hstep]
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [eq_div_iff hn0]
  linear_combination h

/-! ### `|I| < a/n` -/

/-- `∏ⱼ(1 − tYⱼ)` as a ratio (degree-free; verbatim from `INormFull`). -/
theorem prod_ratio {N : ℕ} (zeta : Fin N → ℂ) (A t : ℂ) (h : ∀ j, A - zeta j ≠ 0) :
    ∏ j, (1 - t * (A - zeta j)⁻¹) = (∏ j, (A - t - zeta j)) / (∏ j, (A - zeta j)) := by
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj : A - zeta j ≠ 0 := h j
  field_simp
  ring

/-- **The reflection.**  `∫₀ᵃ g(a − t) dt = ∫₀ᵃ g(u) du`. -/
theorem integral_reflect (a : ℝ) (g : ℝ → ℂ) :
    (∫ t in (0:ℝ)..a, g (a - t)) = ∫ u in (0:ℝ)..a, g u := by
  rw [intervalIntegral.integral_comp_sub_left g a]
  simp

/-- **`|I| < a/n`**, the generic assembly. -/
theorem norm_I_lt_gen {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : 0 < a)
    (z zeta : Fin (n - 1) → ℂ)
    (hne : ∀ j, (a : ℂ) - zeta j ≠ 0)
    (hInt : (∫ u in (0:ℝ)..a, ∏ j, ((u : ℂ) - zeta j)) = (a : ℂ) * (∏ k, -(z k)) / n)
    (hanchor : (n : ℂ) * ∏ j, ((a : ℂ) - zeta j) = ∏ k, ((a : ℂ) - z k))
    (hzn : ∀ k, ‖z k‖ ≤ 1)
    (hrn : (n : ℝ) < ∏ k, ‖(a : ℂ) - z k‖) :
    ‖∫ t in (0:ℝ)..a, ∏ j, (1 - (t : ℂ) * ((a : ℂ) - zeta j)⁻¹)‖ < a / n := by
  have hn0C : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h0 : 0 < n := by omega
    exact_mod_cast h0
  have hP : (∏ j, ((a : ℂ) - zeta j)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hne j
  -- rewrite the integrand as a ratio and pull the constant denominator out
  have hrw : (fun t : ℝ => ∏ j, (1 - (t : ℂ) * ((a : ℂ) - zeta j)⁻¹))
      = fun t : ℝ => (∏ j, ((a : ℂ) - (t : ℂ) - zeta j)) / (∏ j, ((a : ℂ) - zeta j)) := by
    funext t
    exact prod_ratio zeta (a : ℂ) (t : ℂ) hne
  rw [hrw, intervalIntegral.integral_div]
  -- the numerator is the reflected integral
  have hnum : (∫ t in (0:ℝ)..a, ∏ j, ((a : ℂ) - (t : ℂ) - zeta j))
      = (a : ℂ) * (∏ k, -(z k)) / n := by
    rw [← hInt]
    have hg : (fun t : ℝ => ∏ j, ((a : ℂ) - (t : ℂ) - zeta j))
        = fun t : ℝ => (fun u : ℝ => ∏ j, ((u : ℂ) - zeta j)) (a - t) := by
      funext t
      refine Finset.prod_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [hg]
    exact integral_reflect a (fun u : ℝ => ∏ j, ((u : ℂ) - zeta j))
  rw [hnum]
  -- the `n`s cancel: `I = a·∏(−zₖ) / ∏(a − zₖ)`
  have hI : (a : ℂ) * (∏ k, -(z k)) / n / (∏ j, ((a : ℂ) - zeta j))
      = (a : ℂ) * (∏ k, -(z k)) / (∏ k, ((a : ℂ) - z k)) := by
    rw [← hanchor, div_div]
  rw [hI, norm_div, norm_mul, Complex.norm_prod, Complex.norm_prod,
    Complex.norm_of_nonneg ha0.le]
  have hneg : ∏ k, ‖-(z k)‖ = ∏ k, ‖z k‖ :=
    Finset.prod_congr rfl fun k _ => norm_neg _
  rw [hneg]
  have hnum1 : ∏ k, ‖z k‖ ≤ 1 := by
    calc ∏ k, ‖z k‖ ≤ ∏ _k : Fin (n - 1), (1:ℝ) :=
          Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hzn k)
      _ = 1 := by simp
  have hnum0 : 0 ≤ ∏ k, ‖z k‖ :=
    Finset.prod_nonneg fun k _ => norm_nonneg _
  have hdenom : (0 : ℝ) < ∏ k, ‖(a : ℂ) - z k‖ := lt_trans hnpos hrn
  rw [div_lt_div_iff₀ hdenom hnpos]
  have h1 := mul_le_mul_of_nonneg_left hnum1 (mul_pos ha0 hnpos).le
  have h2 := mul_lt_mul_of_pos_left hrn ha0
  nlinarith

end SendovN.BridgeN

namespace SendovN.SegmentN

open Polynomial Finset

/-! ### FTC along a segment, and the apolar integral (port of `Segment.lean`) -/

/-- `∫₀¹ q'(t) dt = q(1) − q(0)`, along the real axis. -/
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

variable {n : ℕ} (D : DataN n)

/-- The GWS family attached to the `k`-th remaining zero: `uⱼ = (a − zₖ)·Yⱼ`. -/
noncomputable def uFam (k j : Fin (n - 1)) : ℂ :=
  ((D.a : ℂ) - D.z k) * ((D.a : ℂ) - D.zeta j)⁻¹

/-- `‖uⱼ‖ < ‖a − zₖ‖`, since every `‖a − ζⱼ‖ > 1`. -/
theorem norm_u_lt (k j : Fin (n - 1)) : ‖uFam D k j‖ < ‖(D.a : ℂ) - D.z k‖ := by
  have hz : (D.a : ℂ) - D.z k ≠ 0 :=
    Anchor2.erase_ne_zero D.hmonic D.hn1 D.hdeg D.haroot D.crit_ne _ (D.z_mem k)
  have hpos : 0 < ‖(D.a : ℂ) - D.z k‖ := norm_pos_iff.mpr hz
  have hj := D.hzeta j
  have hinv : ‖((D.a : ℂ) - D.zeta j)⁻¹‖ < 1 := by
    rw [norm_inv, inv_lt_one_iff₀]
    right
    exact hj
  calc ‖uFam D k j‖ = ‖(D.a : ℂ) - D.z k‖ * ‖((D.a : ℂ) - D.zeta j)⁻¹‖ := by
        rw [uFam, norm_mul]
    _ < ‖(D.a : ℂ) - D.z k‖ * 1 := mul_lt_mul_of_pos_left hinv hpos
    _ = ‖(D.a : ℂ) - D.z k‖ := mul_one _

/-- **The apolar integral vanishes** — the hypothesis Grace–Walsh–Szegő is applied to. -/
theorem integral_uFam_zero (k : Fin (n - 1)) :
    (∫ t in (0:ℝ)..1, ∏ j, (1 - (t : ℂ) * uFam D k j)) = 0 := by
  have hzroot : D.p.eval (D.z k) = 0 := by
    have hmem : D.z k ∈ D.p.roots := Multiset.mem_of_mem_erase (D.z_mem k)
    exact Polynomial.isRoot_of_mem_roots hmem
  have haroot : D.p.eval ((D.a : ℂ)) = 0 := Polynomial.isRoot_of_mem_roots D.haroot
  have hzne : D.z k - (D.a : ℂ) ≠ 0 := by
    have h := Anchor2.erase_ne_zero D.hmonic D.hn1 D.hdeg D.haroot D.crit_ne _ (D.z_mem k)
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
      (derivative D.p).eval x = (n : ℂ) * ∏ j, (x - D.zeta j) := by
    intro x
    rw [Anchor2.derivative_eval_prod D.hmonic D.hn1 D.hdeg x]
    congr 1
    exact (Extract.prod_map_ofMultiset _ D.zetacard (fun w => x - w)).symm
  have hfac : ∀ t : ℝ,
      (derivative D.p).eval ((D.a : ℂ) + (D.z k - (D.a : ℂ)) * (t : ℂ))
        = ((n : ℂ) * ∏ j, ((D.a : ℂ) - D.zeta j)) * ∏ j, (1 - (t : ℂ) * uFam D k j) := by
    intro t
    rw [hzetaprod, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [uFam]
    field_simp [D.zeta_ne j]
    ring
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
    ((n : ℂ) * ∏ j, ((D.a : ℂ) - D.zeta j)) * ∏ j, (1 - (t : ℂ) * uFam D k j))
    (fun t _ => hfac t), intervalIntegral.integral_const_mul] at hseg
  have hne : (n : ℂ) * ∏ j, ((D.a : ℂ) - D.zeta j) ≠ 0 := by
    refine mul_ne_zero (Nat.cast_ne_zero.mpr (by have := D.hn; omega)) ?_
    exact Finset.prod_ne_zero_iff.mpr fun j _ => D.zeta_ne j
  exact (mul_eq_zero.mp hseg).resolve_left hne

end SendovN.SegmentN

namespace SendovN.DataN

open Finset

variable {n : ℕ} (D : DataN n)

/-- The integral identity, attached to `DataN`. -/
theorem integral_prod_zeta :
    (∫ u in (0:ℝ)..D.a, ∏ j, ((u : ℂ) - D.zeta j))
      = (D.a : ℂ) * (∏ k, -(D.z k)) / n :=
  BridgeN.integral_prod_zeta D.hmonic D.hn1 D.hdeg D.haroot D.z D.zeta
    (fun f => Extract.prod_map_ofMultiset _ D.zcard f)
    (fun f => Extract.prod_map_ofMultiset _ D.zetacard f)

/-- `∏ₖ‖a − zₖ‖ > n`, in norm form (definitional with `prod_r_gt_n`). -/
theorem prod_norm_gt : (n : ℝ) < ∏ k, ‖(D.a : ℂ) - D.z k‖ := D.prod_r_gt_n

/-- **`|I| < a/n`**, attached to `DataN`. -/
theorem norm_I_lt (ha0 : 0 < D.a) :
    ‖∫ t in (0:ℝ)..D.a, ∏ j, (1 - (t : ℂ) * ((D.a : ℂ) - D.zeta j)⁻¹)‖ < D.a / n :=
  BridgeN.norm_I_lt_gen D.hn1 ha0 D.z D.zeta D.zeta_ne D.integral_prod_zeta
    D.hprod D.hz D.prod_norm_gt

end SendovN.DataN

#print axioms SendovN.BridgeN.eval_zero_eq
#print axioms SendovN.BridgeN.integral_deriv_eval
#print axioms SendovN.BridgeN.n_mul_integral
#print axioms SendovN.BridgeN.integral_prod_zeta
#print axioms SendovN.BridgeN.norm_I_lt_gen
#print axioms SendovN.SegmentN.integral_poly_deriv
#print axioms SendovN.SegmentN.integral_segment
#print axioms SendovN.SegmentN.norm_u_lt
#print axioms SendovN.SegmentN.integral_uFam_zero
#print axioms SendovN.DataN.integral_prod_zeta
#print axioms SendovN.DataN.norm_I_lt
