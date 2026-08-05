import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.Bridge5

open Polynomial intervalIntegral Finset

/-!
# The polynomial bridge, part 5: the integral identity `∫₀ᵃ ∏ⱼ(u - ζⱼ) du = a∏ₖzₖ/9`

This is the fact `INorm.lean` isolates as a hypothesis and that **cannot** be derived
from the `Counterexample` structure as it stands.  Worth stating plainly, because it
is a structural finding rather than a missing tactic: the structure carries only the
two anchor identities `hprod` (`p'(a)`) and `hsum` (`p''(a)/p'(a)`).  Those pin down
`p'` and `p''` at the single point `a`; they do **not** say the `ζⱼ` are all the
critical points of one polynomial.  `|I| < a/9` needs the global statement, so it has
to come from `p` itself.  Any attempt to wire `RangeMid` or the `9/10 ≤ a < 1`
interior without this is wiring a hypothesis, not a theorem.

The chain is short once the earlier bridge parts are in hand:

    ∫₀ᵃ p'(u) du = p(a) - p(0)              (`Bridge4.integral_deriv_eval`, polynomial FTC)
              p(a) = 0                       (`a` is a root)
              p(0) = -a ∏ₖ(-zₖ)              (`Bridge.eval_zero_eq`)
             p'(u) = 9 ∏ⱼ(u - ζⱼ)            (`Bridge2.derivative_eval_prod`)

so `9 ∫₀ᵃ ∏ⱼ(u - ζⱼ) du = a ∏ₖ(-zₖ) = a ∏ₖ zₖ`, the last step because there are
eight remaining roots and `(-1)⁸ = 1`.  (That parity is not cosmetic — at odd degree
the sign would flip and the paper's `I = a∏zₖ/∏(a-zₖ)` would be off by a sign.)
-/

/-! ### Restated inputs (each proved in `Bridge.lean` / `Bridge2.lean` / `Bridge4.lean`) -/

theorem card_roots_eq (p : ℂ[X]) : Multiset.card p.roots = p.natDegree := by
  have h : (p.map (RingHom.id ℂ)).Splits := IsAlgClosed.splits_codomain p
  rw [Polynomial.map_id] at h
  exact splits_iff_card_roots.mp h

theorem monic_factorization {p : ℂ[X]} (hm : p.Monic) :
    (p.roots.map fun r => X - C r).prod = p :=
  prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (card_roots_eq p)

theorem factor_out {p : ℂ[X]} (hm : p.Monic) {a : ℂ} (ha : a ∈ p.roots) :
    p = (X - C a) * ((p.roots.erase a).map fun r => X - C r).prod := by
  conv_lhs => rw [← monic_factorization hm, ← Multiset.cons_erase ha]
  rw [Multiset.map_cons, Multiset.prod_cons]

theorem eval_zero_eq {p : ℂ[X]} (hm : p.Monic) {a : ℂ} (ha : a ∈ p.roots) :
    p.eval 0 = -a * ((p.roots.erase a).map fun r => -r).prod := by
  conv_lhs => rw [factor_out hm ha]
  rw [eval_mul, eval_sub, eval_X, eval_C, zero_sub, eval_multiset_prod,
    Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun r _ => ?_
  simp

theorem derivative_coeff_eight {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9) :
    (derivative p).coeff 8 = 9 := by
  rw [Polynomial.coeff_derivative]
  have hc : p.coeff 9 = 1 := by
    have := hm.coeff_natDegree
    rwa [hdeg] at this
  rw [show (8:ℕ) + 1 = 9 from rfl, hc]
  norm_num

theorem derivative_natDegree {p : ℂ[X]} (hdeg : p.natDegree = 9) :
    (derivative p).natDegree = 8 := by
  rw [Polynomial.natDegree_derivative, hdeg]

theorem derivative_leadingCoeff {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9) :
    (derivative p).leadingCoeff = 9 := by
  rw [Polynomial.leadingCoeff, derivative_natDegree hdeg]
  exact derivative_coeff_eight hm hdeg

theorem derivative_factorization {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9) :
    C (9:ℂ) * ((derivative p).roots.map fun z => X - C z).prod = derivative p := by
  have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_eq (derivative p))
  rwa [derivative_leadingCoeff hm hdeg] at h

theorem derivative_eval_prod {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9) (x : ℂ) :
    (derivative p).eval x = 9 * ((derivative p).roots.map fun z => x - z).prod := by
  conv_lhs => rw [← derivative_factorization hm hdeg]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
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

/-- Polynomial FTC (from `Bridge4.lean`). -/
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
  | monomial n c =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · rw [derivative_monomial]
        have hk : n - 1 + 1 = n := by omega
        have hne : (n : ℂ) ≠ 0 := by
          simp only [ne_eq, Nat.cast_eq_zero]
          omega
        rw [show (fun u : ℝ => (monomial (n - 1) (c * (n : ℂ))).eval (u : ℂ))
              = (fun u : ℝ => (c * (n : ℂ)) * (u : ℂ) ^ (n - 1)) from by
            funext u; simp [eval_monomial]]
        rw [integral_const_mul, integral_cpow_ofReal, hk]
        simp only [eval_monomial]
        rw [show ((0:ℂ)) ^ n = 0 from zero_pow (by omega)]
        have hcast : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
          rw [Nat.cast_sub hn]; simp
        push_cast [hcast]
        rw [show ((n : ℂ) - 1 + 1) = (n : ℂ) from by ring,
          show c * (n : ℂ) * ((a : ℂ) ^ n / (n : ℂ))
              = c * (a : ℂ) ^ n * ((n : ℂ) / (n : ℂ)) from by ring,
          div_self hne, mul_one]
        ring

/-! ### The identity -/

/-- **`9 ∫₀ᵃ ∏ⱼ(u - ζⱼ) du = a ∏ₖ(-zₖ)`**, in multiset form. -/
theorem nine_mul_integral {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9)
    {a : ℝ} (ha : (a : ℂ) ∈ p.roots) :
    9 * (∫ u in (0:ℝ)..a, ((derivative p).roots.map fun z => (u : ℂ) - z).prod)
      = (a : ℂ) * ((p.roots.erase (a : ℂ)).map fun r => -r).prod := by
  have hint := integral_deriv_eval p a
  rw [show (fun u : ℝ => (derivative p).eval (u : ℂ))
        = (fun u : ℝ => 9 * ((derivative p).roots.map fun z => (u : ℂ) - z).prod) from by
      funext u; exact derivative_eval_prod hm hdeg (u : ℂ)] at hint
  rw [integral_const_mul] at hint
  rw [Polynomial.isRoot_of_mem_roots ha, eval_zero_eq hm ha] at hint
  linear_combination hint

/-- **The identity, indexed by `Fin 8`.**  The `∏ₖ(-zₖ) = ∏ₖ zₖ` step is where the
even number of remaining roots is used. -/
theorem integral_prod_zeta {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9)
    {a : ℝ} (ha : (a : ℂ) ∈ p.roots) (z zeta : Fin 8 → ℂ)
    (hz : ∀ f : ℂ → ℂ, ∏ k, f (z k) = ((p.roots.erase (a : ℂ)).map f).prod)
    (hzeta : ∀ f : ℂ → ℂ, ∏ j, f (zeta j) = ((derivative p).roots.map f).prod) :
    (∫ u in (0:ℝ)..a, ∏ j, ((u : ℂ) - zeta j)) = (a : ℂ) * (∏ k, z k) / 9 := by
  have hstep : ∀ u : ℝ, ∏ j, ((u : ℂ) - zeta j)
      = ((derivative p).roots.map fun w => (u : ℂ) - w).prod :=
    fun u => hzeta (fun w => (u : ℂ) - w)
  have hneg : ∏ k, -(z k) = ∏ k, z k := by
    rw [Finset.prod_neg]
    norm_num
  have hzz : ((p.roots.erase (a : ℂ)).map fun r => -r).prod = ∏ k, z k := by
    rw [← hz (fun r => -r), hneg]
  have h := nine_mul_integral hm hdeg ha
  rw [hzz] at h
  rw [show (fun u : ℝ => ∏ j, ((u : ℂ) - zeta j))
        = (fun u : ℝ => ((derivative p).roots.map fun w => (u : ℂ) - w).prod) from
      funext hstep]
  linear_combination h / 9

end Sendov9.Bridge5

#print axioms Sendov9.Bridge5.card_roots_eq
#print axioms Sendov9.Bridge5.eval_zero_eq
#print axioms Sendov9.Bridge5.derivative_coeff_eight
#print axioms Sendov9.Bridge5.derivative_natDegree
#print axioms Sendov9.Bridge5.derivative_leadingCoeff
#print axioms Sendov9.Bridge5.derivative_eval_prod
#print axioms Sendov9.Bridge5.integral_deriv_eval
#print axioms Sendov9.Bridge5.nine_mul_integral
#print axioms Sendov9.Bridge5.integral_prod_zeta
