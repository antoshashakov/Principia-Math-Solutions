import Mathlib
import Sendov9.Data

set_option maxHeartbeats 4000000







namespace Sendov9.PolarShift

open Finset

/-!
# Stage six: the polar derivative IS the coefficient shift

`Apolarity.lean` took as read (CAS-verified, `n = 1..6`) the identity that makes Grace
tractable: in the normalized basis `f = ∑ₖ C(n,k) aₖ zᵏ`,

    n·f + (ζ - z)·f' = n · ∑ₖ C(n-1,k) (aₖ + ζ·aₖ₊₁) zᵏ.

This file proves it.  With `n = m+1` there is no `ℕ`-subtraction in the binomials, and
everything reduces to two standard facts, both already in Mathlib:

    Nat.succ_mul_choose_eq   : (m+1)·C(m,k)     = C(m+1,k+1)·(k+1)
    Nat.choose_succ_right_eq : C(n,k+1)·(k+1)   = C(n,k)·(n-k)

The second, at `n = m+1`, turns the first into `C(m+1,k)·(m+1-k) = (m+1)·C(m,k)`, so
*both* coefficients appearing on the left — the `(n-k)C(n,k)` from `n·f - z·f'` and the
`(k+1)C(n,k+1)` from `ζ·f'` — collapse to the same `(m+1)·C(m,k)`.  That is the whole
reason the shift `aₖ ↦ aₖ + ζaₖ₊₁` appears with no leftover binomial factors.

`f'` is written directly as `∑ₖ (k+1)·C(n,k+1)·aₖ₊₁·zᵏ` rather than via
`Polynomial.derivative`, which keeps the file to evaluated sums and avoids the
`natDegree` machinery entirely — the same trick that let `Apolarity.lean` dodge degree
bookkeeping.

Sendov's conjecture in degree nine remains unproven.
-/

/-! ### The two binomial facts -/

/-- `(m+1)·C(m,k) = C(m+1,k+1)·(k+1)` — Mathlib's, restated. -/
theorem binom_shift (m k : ℕ) : (m + 1) * m.choose k = (m + 1).choose (k + 1) * (k + 1) :=
  Nat.succ_mul_choose_eq m k

/-- `C(m+1,k)·(m+1-k) = (m+1)·C(m,k)` — the two Mathlib facts composed. -/
theorem binom_desc (m k : ℕ) :
    (m + 1).choose k * (m + 1 - k) = (m + 1) * m.choose k := by
  rw [← Nat.choose_succ_right_eq, ← binom_shift]

/-- The cast of `binom_desc` into `ℂ`, with the subtraction resolved. -/
theorem binom_desc_cast {m k : ℕ} (hk : k ≤ m) :
    (((m + 1).choose k : ℂ)) * (((m : ℂ) + 1) - (k : ℂ))
      = ((m : ℂ) + 1) * (m.choose k : ℂ) := by
  have h := binom_desc m k
  have hcast : (((m + 1 - k : ℕ)) : ℂ) = ((m : ℂ) + 1) - (k : ℂ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have := congrArg (fun t : ℕ => (t : ℂ)) h
  push_cast at this
  rw [← hcast]
  push_cast
  linear_combination this

/-! ### The identity -/

/-- **The polar derivative acts as the coefficient shift.**

`n·f + (ζ - z)·f' = n·∑ₖ C(n-1,k)(aₖ + ζaₖ₊₁)zᵏ` with `n = m+1`, `f` written in the
normalized basis and `f'` written out directly. -/
theorem polar_shift (m : ℕ) (a : ℕ → ℂ) (zeta z : ℂ) :
    ((m : ℂ) + 1) * (∑ k ∈ range (m + 2), ((m + 1).choose k : ℂ) * a k * z ^ k)
      + (zeta - z) * (∑ k ∈ range (m + 1),
          ((k : ℂ) + 1) * ((m + 1).choose (k + 1) : ℂ) * a (k + 1) * z ^ k)
      = ((m : ℂ) + 1) * ∑ k ∈ range (m + 1),
          (m.choose k : ℂ) * (a k + zeta * a (k + 1)) * z ^ k := by
  -- `z · f' = ∑ₖ k·C(n,k)·aₖ·zᵏ` (the `k = 0` term vanishes)
  have hz : z * (∑ k ∈ range (m + 1),
        ((k : ℂ) + 1) * ((m + 1).choose (k + 1) : ℂ) * a (k + 1) * z ^ k)
      = ∑ k ∈ range (m + 2), (k : ℂ) * ((m + 1).choose k : ℂ) * a k * z ^ k := by
    rw [Finset.mul_sum,
      Finset.sum_range_succ' (fun k => (k : ℂ) * ((m + 1).choose k : ℂ) * a k * z ^ k) (m + 1)]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  -- `n·f - z·f'` has coefficients `(n - k)·C(n,k)`, and its top term vanishes
  have hnf : ((m : ℂ) + 1) * (∑ k ∈ range (m + 2), ((m + 1).choose k : ℂ) * a k * z ^ k)
      - (∑ k ∈ range (m + 2), (k : ℂ) * ((m + 1).choose k : ℂ) * a k * z ^ k)
      = ∑ k ∈ range (m + 1),
          (((m : ℂ) + 1) - (k : ℂ)) * ((m + 1).choose k : ℂ) * a k * z ^ k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_range_succ (fun k => ((m : ℂ) + 1) * (((m + 1).choose k : ℂ) * a k * z ^ k)
        - (k : ℂ) * ((m + 1).choose k : ℂ) * a k * z ^ k) (m + 1)]
    have htop : ((m : ℂ) + 1) * (((m + 1).choose (m + 1) : ℂ) * a (m + 1) * z ^ (m + 1))
        - ((m + 1 : ℕ) : ℂ) * ((m + 1).choose (m + 1) : ℂ) * a (m + 1) * z ^ (m + 1) = 0 := by
      push_cast
      ring
    rw [htop, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  -- assemble: LHS = (n·f - z·f') + ζ·f'
  have hLHS : ((m : ℂ) + 1) * (∑ k ∈ range (m + 2), ((m + 1).choose k : ℂ) * a k * z ^ k)
      + (zeta - z) * (∑ k ∈ range (m + 1),
          ((k : ℂ) + 1) * ((m + 1).choose (k + 1) : ℂ) * a (k + 1) * z ^ k)
      = (∑ k ∈ range (m + 1),
          (((m : ℂ) + 1) - (k : ℂ)) * ((m + 1).choose k : ℂ) * a k * z ^ k)
        + zeta * (∑ k ∈ range (m + 1),
          ((k : ℂ) + 1) * ((m + 1).choose (k + 1) : ℂ) * a (k + 1) * z ^ k) := by
    rw [← hnf, sub_mul, hz]
    ring
  rw [hLHS, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : (((m + 1).choose k : ℂ)) * (((m : ℂ) + 1) - (k : ℂ))
      = ((m : ℂ) + 1) * (m.choose k : ℂ) := binom_desc_cast hkm
  have h2 : ((m + 1).choose (k + 1) : ℂ) * ((k : ℂ) + 1)
      = ((m : ℂ) + 1) * (m.choose k : ℂ) := by
    have hc := congrArg (fun t : ℕ => (t : ℂ)) (binom_shift m k)
    push_cast at hc
    linear_combination -hc
  linear_combination (a k * z ^ k) * h1 + (zeta * a (k + 1) * z ^ k) * h2

end Sendov9.PolarShift

namespace Sendov9.PolyOf

open Polynomial Finset

/-!
# Stage nine: the normalized-basis polynomial, and `PolarShift` lifted to it

The Grace induction has to carry three things at once — the polynomial's degree, the
location of its roots, and its coefficient sequence — and the coefficient sequence is
what `PolarShift` and `Apolarity` speak about.  This file is the object that ties them
together: `polyOf m a = ∑ₖ C(m,k)·aₖ·Xᵏ`, built from `monomial` so every coefficient
is available by `Finset.sum_ite_eq'` rather than by unfolding a product.

With that, `polar_shift_poly` lifts `PolarShift.polar_shift` from evaluated sums to an
identity of polynomials:

    (m+1)·polyOf (m+1) a + (ζ - X)·(polyOf (m+1) a)' = (m+1)·polyOf m (shift ζ a)

via `Polynomial.funext` — two polynomials over `ℂ` agreeing at every point are equal,
so nothing has to be proved coefficient-by-coefficient a second time.

The left-hand side is exactly the polar derivative `D_ζ` when `polyOf (m+1) a` has
degree `m+1`, which `natDegree_eq` supplies from `a (m+1) ≠ 0`.  So one step of the
Grace iteration is one application of this identity, and `Centroid.shift_top_ne_zero`
says the hypothesis `a (m+1) ≠ 0` is re-established at the next step.

Sendov's conjecture in degree nine remains unproven.
-/

/-- `f = ∑ₖ C(m,k)·aₖ·Xᵏ`, the normalized basis. -/
noncomputable def polyOf (m : ℕ) (a : ℕ → ℂ) : ℂ[X] :=
  ∑ k ∈ range (m + 1), monomial k ((m.choose k : ℂ) * a k)

@[simp] theorem coeff_polyOf (m : ℕ) (a : ℕ → ℂ) (j : ℕ) :
    (polyOf m a).coeff j = if j ∈ range (m + 1) then (m.choose j : ℂ) * a j else 0 := by
  unfold polyOf
  rw [Polynomial.finset_sum_coeff]
  simp [Polynomial.coeff_monomial, Finset.sum_ite_eq']

theorem natDegree_le (m : ℕ) (a : ℕ → ℂ) : (polyOf m a).natDegree ≤ m := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
  rw [coeff_polyOf]
  have hnot : j ∉ range (m + 1) := by
    simp only [Finset.mem_range]
    omega
  rw [if_neg hnot]

/-- The degree is exactly `m` when the top normalized coefficient is nonzero. -/
theorem natDegree_eq {m : ℕ} {a : ℕ → ℂ} (ha : a m ≠ 0) :
    (polyOf m a).natDegree = m := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le m a) ?_
  rw [coeff_polyOf]
  simp only [Finset.mem_range, Nat.lt_succ_self, if_pos, Nat.choose_self, Nat.cast_one,
    one_mul]
  exact ha

theorem polyOf_ne_zero {m : ℕ} {a : ℕ → ℂ} (ha : a m ≠ 0) : polyOf m a ≠ 0 := by
  intro h
  have hc : (polyOf m a).coeff m = 0 := by rw [h]; simp
  rw [coeff_polyOf] at hc
  simp only [Finset.mem_range, Nat.lt_succ_self, if_pos, Nat.choose_self, Nat.cast_one,
    one_mul] at hc
  exact ha hc

/-! ### Evaluation -/

theorem eval_polyOf (m : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    (polyOf m a).eval z = ∑ k ∈ range (m + 1), (m.choose k : ℂ) * a k * z ^ k := by
  unfold polyOf
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_monomial]

theorem eval_deriv_polyOf (m : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    (derivative (polyOf m a)).eval z
      = ∑ k ∈ range m, ((k : ℂ) + 1) * (m.choose (k + 1) : ℂ) * a (k + 1) * z ^ k := by
  unfold polyOf
  rw [derivative_sum, Polynomial.eval_finset_sum]
  rw [Finset.sum_range_succ' (fun k => (derivative (monomial k ((m.choose k : ℂ) * a k))).eval z) m]
  simp only [derivative_monomial, Polynomial.eval_monomial, Nat.cast_zero, mul_zero,
    zero_mul, map_zero, Polynomial.eval_zero, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-! ### `PolarShift`, lifted -/

/-- The coefficient shift `aₖ ↦ aₖ + ζ·aₖ₊₁`. -/
def shift (zeta : ℂ) (a : ℕ → ℂ) : ℕ → ℂ := fun k => a k + zeta * a (k + 1)

/-- **The polar derivative, as an identity of polynomials.**

`(m+1)·f + (ζ - X)·f' = (m+1)·polyOf m (shift ζ a)` for `f = polyOf (m+1) a`.  Proved
by `Polynomial.funext` off `PolarShift.polar_shift`, so the coefficient computation is
not redone. -/
theorem polar_shift_poly (m : ℕ) (a : ℕ → ℂ) (zeta : ℂ) :
    C ((m : ℂ) + 1) * polyOf (m + 1) a
        + (C zeta - X) * derivative (polyOf (m + 1) a)
      = C ((m : ℂ) + 1) * polyOf m (shift zeta a) := by
  refine Polynomial.funext fun z => ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X, eval_polyOf, eval_deriv_polyOf]
  have h := Sendov9.PolarShift.polar_shift m a zeta z
  unfold shift
  linear_combination h

end Sendov9.PolyOf







namespace Sendov9.Laguerre2

open Finset Complex

/-!
# Stage two: the Möbius step, without Möbius theory

Laguerre's theorem needs: for `zⱼ` in a closed disk `D(p,ρ)` and `ζ, z₀` outside it,

    ∑ⱼ (ζ - zⱼ)/(z₀ - zⱼ) ≠ 0

which is `D_ζf(z₀)/f(z₀) ≠ 0`, i.e. the polar derivative has no zero outside `D`.

The textbook argument says: `x ↦ (ζ - x)/(z₀ - x)` is a Möbius map, its image of `D`
is a disk, that disk misses `0` because `ζ ∉ D`, and a disk missing `0` lies in a
half-plane.  Formalizing "the Möbius image of a disk is a disk" is real work.

It turns out not to be needed.  Writing `A = ζ - p`, `B = z₀ - p`, `dⱼ = zⱼ - p` and
`N = ‖B‖² - ρ²`, the image disk's centre and radius are explicit,

    γ = (A B̄ - ρ²)/N,      r = ρ‖A - B‖/N,

and the two facts that matter are *algebraic identities that factor exactly*:

    ρ²‖B - d‖² - ‖d B̄ - ρ²‖² = (ρ² - ‖d‖²)(‖B‖² - ρ²)     — puts each image point in the disk
    ‖A B̄ - ρ²‖² - ρ²‖A - B‖² = (‖A‖² - ρ²)(‖B‖² - ρ²)     — puts `0` outside it

Both right-hand sides are products of two nonnegative factors under the hypotheses, so
each inequality is immediate.  The cross terms cancel identically — verified in CAS
before formalizing.  With those, the containment `‖w - γ‖ ≤ r < ‖γ‖` is a two-line
computation off the identity

    (A - d)/(B - d) - γ = (A - B)(d B̄ - ρ²)/((B - d)·N)

and `Laguerre.disk_halfplane` finishes.

This completes Laguerre's localization.  Grace's apolarity theorem and Walsh's
coincidence theorem still stand between here and `GraceWalshSzego`; Sendov's
conjecture in degree nine remains unproven.
-/

/-! ### Restated from `Laguerre.lean` -/

theorem sum_ne_zero_of_halfplane {n : ℕ} (hn : 0 < n) (c : ℂ) (w : Fin n → ℂ)
    (h : ∀ j, 0 < (c * w j).re) : ∑ j, w j ≠ 0 := by
  intro hsum
  have hre : (0:ℝ) < ∑ j, (c * w j).re := by
    refine Finset.sum_pos (fun j _ => h j) ?_
    exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  have hzero : ∑ j, (c * w j).re = 0 := by
    rw [← Complex.re_sum, ← Finset.mul_sum, hsum, mul_zero]
    simp
  rw [hzero] at hre
  exact lt_irrefl 0 hre

theorem disk_halfplane {p v : ℂ} {r : ℝ} (hr : r ≤ ‖p‖) (h : ‖v - p‖ < r) :
    0 < ((starRingEnd ℂ) p * v).re := by
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) h
  have hp0 : 0 < ‖p‖ := lt_of_lt_of_le hr0 hr
  have hsplit : ((starRingEnd ℂ) p * v).re
      = ‖p‖ ^ 2 + ((starRingEnd ℂ) p * (v - p)).re := by
    have hpp : ((starRingEnd ℂ) p * p).re = ‖p‖ ^ 2 := by
      have hns : ((starRingEnd ℂ) p * p).re = Complex.normSq p := by
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
          Complex.normSq_apply]
        ring
      rw [hns, Complex.normSq_eq_norm_sq]
    rw [mul_sub, Complex.sub_re, hpp]
    ring
  have hbound : -(‖p‖ * ‖v - p‖) ≤ ((starRingEnd ℂ) p * (v - p)).re := by
    have h1 : |((starRingEnd ℂ) p * (v - p)).re| ≤ ‖(starRingEnd ℂ) p * (v - p)‖ :=
      Complex.abs_re_le_norm _
    have h2 : ‖(starRingEnd ℂ) p * (v - p)‖ = ‖p‖ * ‖v - p‖ := by
      rw [norm_mul, RCLike.norm_conj]
    rw [h2] at h1
    linarith [neg_abs_le (((starRingEnd ℂ) p * (v - p)).re)]
  have h1 : ‖p‖ * ‖v - p‖ < ‖p‖ * r := mul_lt_mul_of_pos_left h hp0
  have h2 : ‖p‖ * r ≤ ‖p‖ * ‖p‖ := mul_le_mul_of_nonneg_left hr hp0.le
  have hlt : ‖p‖ * ‖v - p‖ < ‖p‖ ^ 2 := by nlinarith
  rw [hsplit]
  linarith

/-! ### The two factoring identities -/

/-- **Each image point lands in the disk.**  `‖d B̄ - ρ²‖ ≤ ρ‖B - d‖`, because
`ρ²‖B-d‖² - ‖d B̄ - ρ²‖² = (ρ² - ‖d‖²)(‖B‖² - ρ²)` and both factors are `≥ 0`. -/
theorem norm_inner_le {d B : ℂ} {rho : ℝ} (hd : ‖d‖ ≤ rho) (hB : rho ≤ ‖B‖) :
    ‖d * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ)‖ ≤ rho * ‖B - d‖ := by
  have hr0 : 0 ≤ rho := le_trans (norm_nonneg d) hd
  have hfac : rho ^ 2 * Complex.normSq (B - d)
      - Complex.normSq (d * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ))
      = (rho ^ 2 - Complex.normSq d) * (Complex.normSq B - rho ^ 2) := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hd2 : Complex.normSq d ≤ rho ^ 2 := by
    rw [← Complex.sq_norm]; nlinarith [norm_nonneg d]
  have hB2 : rho ^ 2 ≤ Complex.normSq B := by
    rw [← Complex.sq_norm]; nlinarith [norm_nonneg B]
  have hnn : 0 ≤ (rho ^ 2 - Complex.normSq d) * (Complex.normSq B - rho ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hsq : Complex.normSq (d * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ))
      ≤ (rho * ‖B - d‖) ^ 2 := by
    rw [mul_pow, Complex.sq_norm]
    linarith
  rw [← Complex.sq_norm] at hsq
  nlinarith [norm_nonneg (d * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ)),
    mul_nonneg hr0 (norm_nonneg (B - d))]

/-- **The origin lands outside the disk.**  `ρ‖A - B‖ < ‖A B̄ - ρ²‖`, because
`‖A B̄ - ρ²‖² - ρ²‖A-B‖² = (‖A‖² - ρ²)(‖B‖² - ρ²)` and both factors are `> 0`. -/
theorem norm_centre_gt {A B : ℂ} {rho : ℝ} (hr0 : 0 ≤ rho)
    (hA : rho < ‖A‖) (hB : rho < ‖B‖) :
    rho * ‖A - B‖ < ‖A * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ)‖ := by
  have hfac : Complex.normSq (A * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ))
      - rho ^ 2 * Complex.normSq (A - B)
      = (Complex.normSq A - rho ^ 2) * (Complex.normSq B - rho ^ 2) := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hA2 : rho ^ 2 < Complex.normSq A := by
    rw [← Complex.sq_norm]; nlinarith
  have hB2 : rho ^ 2 < Complex.normSq B := by
    rw [← Complex.sq_norm]; nlinarith
  have hpos : 0 < (Complex.normSq A - rho ^ 2) * (Complex.normSq B - rho ^ 2) :=
    mul_pos (by linarith) (by linarith)
  have hsq : (rho * ‖A - B‖) ^ 2
      < Complex.normSq (A * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ)) := by
    rw [mul_pow, Complex.sq_norm]
    linarith
  rw [← Complex.sq_norm] at hsq
  nlinarith [norm_nonneg (A * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ)),
    mul_nonneg hr0 (norm_nonneg (A - B))]

/-- **The image-disk identity.**  Stated standalone so `subst` hands `field_simp` the
denominator's non-vanishing in unfolded form; inline, `field_simp` cannot see it. -/
theorem mobius_diff {A B d NC : ℂ} {rho : ℝ}
    (hNCdef : NC = B * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ))
    (hBd : B - d ≠ 0) (hNC0 : NC ≠ 0) :
    (A - d) / (B - d) - (A * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ)) / NC
      = (A - B) * (d * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ)) / ((B - d) * NC) := by
  subst hNCdef
  field_simp
  ring

/-! ### Laguerre's localization -/

/-- **The polar derivative has no zero outside the disk.**

If every `zⱼ` lies in the closed disk `D(p, ρ)` and both `ζ` and `z₀` lie strictly
outside it, then `∑ⱼ (ζ - zⱼ)/(z₀ - zⱼ) ≠ 0`.  Since
`D_ζf(z₀)/f(z₀) = ∑ⱼ (ζ - zⱼ)/(z₀ - zⱼ)`, this is Laguerre's theorem. -/
theorem sum_ratio_ne_zero {n : ℕ} (hn : 0 < n) {p zeta z0 : ℂ} {rho : ℝ}
    (zs : Fin n → ℂ) (hzs : ∀ j, ‖zs j - p‖ ≤ rho)
    (hzeta : rho < ‖zeta - p‖) (hz0 : rho < ‖z0 - p‖) :
    ∑ j, (zeta - zs j) / (z0 - zs j) ≠ 0 := by
  set A : ℂ := zeta - p with hA
  set B : ℂ := z0 - p with hB
  have hr0 : 0 ≤ rho := le_trans (norm_nonneg _) (hzs ⟨0, hn⟩)
  -- `N = B B̄ - ρ²`, positive real
  set NC : ℂ := B * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ) with hNC
  have hNreal : NC = ((Complex.normSq B - rho ^ 2 : ℝ) : ℂ) := by
    rw [hNC, Complex.mul_conj]
    push_cast
    ring
  have hNpos : 0 < Complex.normSq B - rho ^ 2 := by
    have : rho ^ 2 < Complex.normSq B := by
      rw [← Complex.sq_norm]; nlinarith
    linarith
  have hNC0 : NC ≠ 0 := by
    rw [hNreal]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hNpos)
  have hNCnorm : ‖NC‖ = Complex.normSq B - rho ^ 2 := by
    rw [hNreal, Complex.norm_real, Real.norm_of_nonneg hNpos.le]
  -- the centre of the image disk
  set gamma : ℂ := (A * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ)) / NC with hgamma
  -- every denominator is nonzero
  have hden : ∀ j, z0 - zs j ≠ 0 := by
    intro j h0
    have h1 : ‖B - (zs j - p)‖ = 0 := by
      rw [show B - (zs j - p) = z0 - zs j from by rw [hB]; ring, h0, norm_zero]
    have h2 : ‖B‖ ≤ ‖zs j - p‖ := by
      have := norm_sub_norm_le B (zs j - p)
      have h3 : ‖B‖ - ‖zs j - p‖ ≤ 0 := le_trans this (le_of_eq h1)
      linarith
    have := hzs j
    rw [hB] at h2
    linarith
  -- each image point sits within `r` of `gamma`
  have hclose : ∀ j, ‖(zeta - zs j) / (z0 - zs j) - gamma‖
      ≤ rho * ‖A - B‖ / (Complex.normSq B - rho ^ 2) := by
    intro j
    set d : ℂ := zs j - p with hd
    have hBd : B - d ≠ 0 := by
      rw [hB, hd]
      simpa using hden j
    have hrewrite : (zeta - zs j) / (z0 - zs j) - gamma
        = (A - B) * (d * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ)) / ((B - d) * NC) := by
      rw [show zeta - zs j = A - d from by rw [hA, hd]; ring,
        show z0 - zs j = B - d from by rw [hB, hd]; ring, hgamma]
      exact mobius_diff hNC hBd hNC0
    rw [hrewrite, norm_div, norm_mul, norm_mul, hNCnorm]
    have h1 : ‖d * (starRingEnd ℂ) B - ((rho ^ 2 : ℝ) : ℂ)‖ ≤ rho * ‖B - d‖ :=
      norm_inner_le (by rw [hd]; exact hzs j) (by rw [hB]; exact hz0.le)
    have hBd0 : 0 < ‖B - d‖ := norm_pos_iff.mpr hBd
    rw [div_le_div_iff₀ (by positivity) hNpos]
    nlinarith [h1, norm_nonneg (A - B), hNpos.le,
      mul_nonneg (norm_nonneg (A - B)) hNpos.le]
  -- and `gamma` is farther from the origin than `r`
  have hfar : rho * ‖A - B‖ / (Complex.normSq B - rho ^ 2) < ‖gamma‖ := by
    rw [hgamma, norm_div, hNCnorm, div_lt_div_iff₀ hNpos hNpos]
    nlinarith [norm_centre_gt hr0 hzeta hz0, hNpos]
  -- so every image point is within `‖gamma‖` of `gamma`: the half-plane applies
  refine sum_ne_zero_of_halfplane hn ((starRingEnd ℂ) gamma) _ (fun j => ?_)
  exact disk_halfplane (le_refl ‖gamma‖) (lt_of_le_of_lt (hclose j) hfar)

end Sendov9.Laguerre2

namespace Sendov9.Laguerre3

open Finset Complex

/-!
# Stage three: Laguerre in polynomial form

`Laguerre2.sum_ratio_ne_zero` gives the analytic statement — `∑ⱼ(ζ-zⱼ)/(z₀-zⱼ) ≠ 0`.
Grace's apolarity theorem consumes the *polynomial* statement: the polar derivative

    D_ζ f = n·f + (ζ - X)·f'

of a polynomial whose zeros all lie in a closed disk has no zero outside that disk.

The bridge is one line of algebra,

    D_ζf(z₀) = f(z₀) · ∑ⱼ (ζ - zⱼ)/(z₀ - zⱼ),

because `f'(z₀)/f(z₀) = ∑ⱼ (z₀ - zⱼ)⁻¹` and

    n + (ζ - z₀)·∑ⱼ (z₀-zⱼ)⁻¹ = ∑ⱼ [(z₀-zⱼ) + (ζ-z₀)]/(z₀-zⱼ) = ∑ⱼ (ζ-zⱼ)/(z₀-zⱼ).

`f(z₀) ≠ 0` because `z₀` is outside the disk and every zero is inside, so the product
is nonzero and Laguerre follows.

This is the last stage of the route that is purely elementary.  What remains between
here and `GraceWalshSzego` is Grace's apolarity theorem — whose proof from Laguerre is
an induction applying `D_{w₁}, …, D_{wₙ}` and identifying the resulting constant with
the apolarity form — and then Walsh's coincidence theorem.  Sendov's conjecture in
degree nine remains unproven.
-/

/-! ### The algebraic bridge -/

/-- **`n + (ζ - z₀)·∑ⱼ(z₀-zⱼ)⁻¹ = ∑ⱼ(ζ-zⱼ)/(z₀-zⱼ)`.**  Each summand splits as
`(z₀-zⱼ) + (ζ-z₀)` over `(z₀-zⱼ)`. -/
theorem polar_sum_identity {n : ℕ} (zs : Fin n → ℂ) (zeta z0 : ℂ)
    (hne : ∀ j, z0 - zs j ≠ 0) :
    (n : ℂ) + (zeta - z0) * ∑ j, (z0 - zs j)⁻¹ = ∑ j, (zeta - zs j) / (z0 - zs j) := by
  rw [Finset.mul_sum]
  have hterm : ∀ j ∈ (univ : Finset (Fin n)),
      (zeta - zs j) / (z0 - zs j) = 1 + (zeta - z0) * (z0 - zs j)⁻¹ := by
    intro j _
    have hj : z0 - zs j ≠ 0 := hne j
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  simp

/-- **`f'(z₀) = f(z₀)·∑ⱼ(z₀-zⱼ)⁻¹`** for `f = ∏ⱼ(X - zⱼ)`, in evaluated form. -/
theorem deriv_prod_eq {n : ℕ} (zs : Fin n → ℂ) (z0 : ℂ) (hne : ∀ j, z0 - zs j ≠ 0) :
    ∑ i, ∏ j ∈ univ.erase i, (z0 - zs j)
      = (∏ j, (z0 - zs j)) * ∑ i, (z0 - zs i)⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : z0 - zs i ≠ 0 := hne i
  have hsplit : (∏ j ∈ univ.erase i, (z0 - zs j)) * (z0 - zs i) = ∏ j, (z0 - zs j) :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  rw [← hsplit, mul_inv_cancel_right₀ hi]

/-! ### Laguerre, in polynomial form -/

/-- **The polar derivative has no zero outside the disk.**

For `f = ∏ⱼ(X - zⱼ)` with every `zⱼ` in the closed disk `D(p,ρ)`, and `ζ` outside it,
`D_ζf(z₀) = n·f(z₀) + (ζ-z₀)·f'(z₀)` is nonzero at every `z₀` outside the disk.

This is Laguerre's theorem, and it is what Grace's apolarity theorem is proved from. -/
theorem polar_deriv_ne_zero {n : ℕ} (hn : 0 < n) {p : ℂ} {rho : ℝ}
    (zs : Fin n → ℂ) (hzs : ∀ j, ‖zs j - p‖ ≤ rho)
    {zeta z0 : ℂ} (hzeta : rho < ‖zeta - p‖) (hz0 : rho < ‖z0 - p‖) :
    (n : ℂ) * (∏ j, (z0 - zs j))
      + (zeta - z0) * (∑ i, ∏ j ∈ univ.erase i, (z0 - zs j)) ≠ 0 := by
  -- every factor of `f(z₀)` is nonzero
  have hne : ∀ j, z0 - zs j ≠ 0 := by
    intro j h0
    have h1 : ‖z0 - p‖ ≤ ‖zs j - p‖ := by
      have : z0 - p = zs j - p := by
        have : z0 = zs j := by linear_combination h0
        rw [this]
      rw [this]
    linarith [hzs j]
  have hF : (∏ j, (z0 - zs j)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hne j
  -- `D_ζf(z₀) = f(z₀) · ∑ⱼ(ζ-zⱼ)/(z₀-zⱼ)`
  have hfac : (n : ℂ) * (∏ j, (z0 - zs j))
      + (zeta - z0) * (∑ i, ∏ j ∈ univ.erase i, (z0 - zs j))
      = (∏ j, (z0 - zs j)) * ∑ j, (zeta - zs j) / (z0 - zs j) := by
    rw [deriv_prod_eq zs z0 hne, ← polar_sum_identity zs zeta z0 hne]
    ring
  rw [hfac]
  refine mul_ne_zero hF ?_
  -- the analytic statement, from stage two
  exact Laguerre2.sum_ratio_ne_zero hn zs hzs hzeta hz0

end Sendov9.Laguerre3

/-!
## `Extract` and `Anchor2` come from `Sendov9.Data`

The standalone `Grace2.lean` carries verbatim copies of `Sendov9.Extract` (the
`Multiset`/`Fin n` adapter) and the two `Sendov9.Anchor2` lemmas it uses
(`prod_split`, `logderiv_eval`), because it gated against bare Mathlib.  `Data.lean`
declares the same names — byte-identical statements and proofs, verified by md5 on the
`Extract` blocks and by textual comparison on the two `Anchor2` declarations — so the
two modules cannot be imported together.

This module is `Grace2.lean` with those three blocks deleted and `import Sendov9.Data`
added in their place, exactly the surgery `Core.lean` performs on `Instantiate2.lean`.
Everything else is byte-identical to the gated original, so the GWS route and the
counterexample data compose in one environment.
-/


namespace Sendov9.LagGen

open Polynomial Finset

/-!
# Stage eight: Laguerre from "no root outside", so the iteration has an invariant

`Laguerre3.polar_deriv_ne_zero` is stated for an explicit product `f = ∏ⱼ(X - zⱼ)`.
That is the wrong shape to iterate: after one polar derivative the roots are no longer
anything one has a formula for, so the next step cannot be applied.

`laguerre_general` restates it with the hypothesis and conclusion in the *same* shape —
"every root lies in the closed disk" — which is an invariant an induction can carry.
The root extraction happens once, inside: `ℂ` is algebraically closed, so `g` factors
over its root multiset, `Extract.ofMultiset` indexes it by `Fin n`, and `Laguerre3`
applies.  Iterating is then legitimate, since the conclusion re-establishes the
hypothesis at degree `n-1` (which is the right degree by `Centroid.shift_top_ne_zero`).
-/

theorem card_roots_eq (q : ℂ[X]) : Multiset.card q.roots = q.natDegree := by
  have h : (q.map (RingHom.id ℂ)).Splits := IsAlgClosed.splits_codomain q
  rw [Polynomial.map_id] at h
  exact splits_iff_card_roots.mp h

/-- **Laguerre, in invariant form.**  If every root of `g` lies in the closed disk and
`ζ`, `z₀` lie strictly outside it, the polar derivative `n·g + (ζ - z₀)·g'` does not
vanish at `z₀` — i.e. `D_ζg` has no root outside the disk either. -/
theorem laguerre_general {g : ℂ[X]} {p zeta z0 : ℂ} {rho : ℝ}
    (hg : g ≠ 0) (hn : 0 < g.natDegree)
    (hroots : ∀ r ∈ g.roots, ‖r - p‖ ≤ rho)
    (hzeta : rho < ‖zeta - p‖) (hz0 : rho < ‖z0 - p‖) :
    (g.natDegree : ℂ) * g.eval z0 + (zeta - z0) * (derivative g).eval z0 ≠ 0 := by
  have hcard : Multiset.card g.roots = g.natDegree := card_roots_eq g
  set u : Fin g.natDegree → ℂ := Extract.ofMultiset g.roots hcard with hu
  have hud : ∀ j, ‖u j - p‖ ≤ rho := fun j => hroots _ (Extract.mem_ofMultiset _ _ j)
  have hne : ∀ r ∈ g.roots, z0 - r ≠ 0 := by
    intro r hr h0
    have hrz : z0 = r := by linear_combination h0
    have := hroots r hr
    rw [← hrz] at this
    linarith
  have hnef : ∀ j, z0 - u j ≠ 0 := fun j => hne _ (Extract.mem_ofMultiset _ _ j)
  have hc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg
  have hfac : C g.leadingCoeff * (g.roots.map fun a => X - C a).prod = g :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  -- evaluate `g` and `g'` through the factorization
  have hP : ((g.roots.map fun r => z0 - r).prod) = ∏ j, (z0 - u j) :=
    (Extract.prod_map_ofMultiset g.roots hcard (fun r => z0 - r)).symm
  have hS : ((g.roots.map fun r => (z0 - r)⁻¹).sum) = ∑ j, (z0 - u j)⁻¹ :=
    (Extract.sum_map_ofMultiset g.roots hcard (fun r => (z0 - r)⁻¹)).symm
  have heval : g.eval z0 = g.leadingCoeff * ∏ j, (z0 - u j) := by
    conv_lhs => rw [← hfac]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    rw [← hP]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun r _ => ?_)
    simp
  have hderiv : (derivative g).eval z0
      = g.leadingCoeff * ((∏ j, (z0 - u j)) * ∑ j, (z0 - u j)⁻¹) := by
    conv_lhs => rw [← hfac]
    rw [derivative_C_mul, eval_mul, eval_C, Sendov9.Anchor2.logderiv_eval hne, hP, hS]
  -- factor out `c · ∏(z₀ - uⱼ)` and apply Laguerre
  rw [heval, hderiv]
  have hprod : (∏ j, (z0 - u j)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hnef j
  have hkey : (g.natDegree : ℂ) * (g.leadingCoeff * ∏ j, (z0 - u j))
      + (zeta - z0) * (g.leadingCoeff * ((∏ j, (z0 - u j)) * ∑ j, (z0 - u j)⁻¹))
      = g.leadingCoeff * (∏ j, (z0 - u j))
        * ((g.natDegree : ℂ) + (zeta - z0) * ∑ j, (z0 - u j)⁻¹) := by ring
  rw [hkey, Sendov9.Laguerre3.polar_sum_identity u zeta z0 hnef]
  refine mul_ne_zero (mul_ne_zero hc hprod) ?_
  exact Sendov9.Laguerre2.sum_ratio_ne_zero hn u hud hzeta hz0

end Sendov9.LagGen



namespace Sendov9.Vieta

open Polynomial Finset

/-!
# Stage ten: the top coefficient survives the shift

The Grace induction needs, at each step, that the shifted sequence's top entry is still
nonzero — otherwise the degree falls by more than one and the iteration loses a step.
`Centroid.shift_top_ne_zero` proved this for a *monic product* `∏(z - uⱼ)`, where the
centroid is visibly `(∑uⱼ)/n`.  The induction, though, carries `polyOf m a`, whose
roots are not given by a formula.  So the centroid has to be read off the
*coefficients* instead — which is Vieta.

For `g = polyOf (m+1) a` with `a₍ₘ₊₁₎ ≠ 0`:

    leadingCoeff = g.coeff (m+1) = a₍ₘ₊₁₎,     g.coeff m = (m+1)·aₘ

and `Polynomial.coeff_eq_esymm_roots_of_card` at `k = m` gives
`g.coeff m = leadingCoeff · (-1) · e₁(roots)`, i.e. `∑roots = -(m+1)aₘ/a₍ₘ₊₁₎`.  Hence

    centroid = (∑roots)/(m+1) = -aₘ/a₍ₘ₊₁₎        and        aₘ + ζ·a₍ₘ₊₁₎ = a₍ₘ₊₁₎·(ζ - centroid),

which is nonzero because the centroid of points of a closed disk lies in that disk
while `ζ` is strictly outside.

Sendov's conjecture in degree nine remains unproven.
-/

/-- `e₁` of a multiset is its sum. -/
theorem esymm_one (s : Multiset ℂ) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

/-- **The centroid of a multiset of points in a closed disk lies in that disk.** -/
theorem centroid_multiset {s : Multiset ℂ} {p : ℂ} {rho : ℝ} {n : ℕ}
    (hcard : Multiset.card s = n) (hn : 0 < n)
    (hs : ∀ r ∈ s, ‖r - p‖ ≤ rho) : ‖s.sum / (n : ℂ) - p‖ ≤ rho := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmapsum : (s.map fun r => r - p).sum = s.sum - (n : ℂ) * p := by
    rw [Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, hcard,
      nsmul_eq_mul]
    simp
  have hrw : s.sum / (n : ℂ) - p = (s.map fun r => r - p).sum / (n : ℂ) := by
    rw [hmapsum]
    field_simp
  rw [hrw, norm_div]
  have hnorm : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  rw [hnorm, div_le_iff₀ hnr]
  have hbound : ‖(s.map fun r => r - p).sum‖ ≤ ((s.map fun r => r - p).map norm).sum :=
    norm_multiset_sum_le _
  have hle : ((s.map fun r => r - p).map norm).sum ≤ rho * (n : ℝ) := by
    rw [Multiset.map_map]
    have hcong : ∀ r ∈ s, (norm ∘ fun r => r - p) r ≤ rho := fun r hr => hs r hr
    calc ((s.map (norm ∘ fun r => r - p)).sum)
        ≤ (s.map (fun _ => rho)).sum := by
          refine Multiset.sum_map_le_sum_map _ _ ?_
          intro r hr
          exact hcong r hr
      _ = rho * (n : ℝ) := by
          rw [Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul]
          ring
  linarith

/-- **Vieta at the second coefficient.**  `∑roots = -g.coeff(n-1)/leadingCoeff`. -/
theorem roots_sum {g : ℂ[X]} {n : ℕ} (hdeg : g.natDegree = n + 1) (hg : g ≠ 0) :
    g.leadingCoeff * g.roots.sum = -g.coeff n := by
  have hcard : Multiset.card g.roots = g.natDegree := by
    have h : (g.map (RingHom.id ℂ)).Splits := IsAlgClosed.splits_codomain g
    rw [Polynomial.map_id] at h
    exact splits_iff_card_roots.mp h
  have hn : n ≤ g.natDegree := by omega
  have hv := Polynomial.coeff_eq_esymm_roots_of_card hcard hn
  have hsub : g.natDegree - n = 1 := by omega
  rw [hsub, esymm_one] at hv
  rw [hv]
  ring

/-- **The top coefficient survives.**  `aₘ + ζ·a₍ₘ₊₁₎ ≠ 0` when every root of
`polyOf (m+1) a` lies in the closed disk and `ζ` is strictly outside it. -/
theorem shift_top_ne_zero {m : ℕ} {a : ℕ → ℂ} {p zeta : ℂ} {rho : ℝ}
    {g : ℂ[X]} (hdeg : g.natDegree = m + 1) (hg : g ≠ 0)
    (hlead : g.leadingCoeff = a (m + 1)) (hcm : g.coeff m = ((m : ℂ) + 1) * a m)
    (ha : a (m + 1) ≠ 0)
    (hroots : ∀ r ∈ g.roots, ‖r - p‖ ≤ rho)
    (hzeta : rho < ‖zeta - p‖) :
    a m + zeta * a (m + 1) ≠ 0 := by
  have hcard : Multiset.card g.roots = g.natDegree := by
    have h : (g.map (RingHom.id ℂ)).Splits := IsAlgClosed.splits_codomain g
    rw [Polynomial.map_id] at h
    exact splits_iff_card_roots.mp h
  rw [hdeg] at hcard
  -- Vieta: `a₍ₘ₊₁₎ · ∑roots = -(m+1)·aₘ`
  have hv : a (m + 1) * g.roots.sum = -(((m : ℂ) + 1) * a m) := by
    have := roots_sum hdeg hg
    rw [hlead, hcm] at this
    exact this
  -- the centroid is in the disk
  have hm1 : ((m : ℂ) + 1) ≠ 0 := by
    have : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast at this
    exact this
  have hcent : ‖g.roots.sum / ((m + 1 : ℕ) : ℂ) - p‖ ≤ rho :=
    centroid_multiset hcard (by omega) hroots
  -- so `ζ ≠ centroid`
  have hne : zeta - g.roots.sum / ((m + 1 : ℕ) : ℂ) ≠ 0 := by
    intro h0
    have heq : zeta = g.roots.sum / ((m + 1 : ℕ) : ℂ) := by linear_combination h0
    rw [← heq] at hcent
    linarith
  -- and `aₘ + ζ·a₍ₘ₊₁₎ = (a₍ₘ₊₁₎/(m+1))·(m+1)·(ζ - centroid)`
  intro hzero
  apply hne
  -- `aₘ = -ζ·a₍ₘ₊₁₎`, so Vieta gives `∑roots = (m+1)·ζ` after cancelling `a₍ₘ₊₁₎`
  have hS : g.roots.sum = ((m : ℂ) + 1) * zeta := by
    refine mul_left_cancel₀ ha ?_
    rw [hv]
    linear_combination -((m : ℂ) + 1) * hzero
  have hcast : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  rw [hS, hcast]
  field_simp
  ring

end Sendov9.Vieta

namespace Sendov9.Grace

open Polynomial Finset Sendov9.PolyOf

/-!
# Stage eleven: Grace's iteration

Every ingredient is in place, so this is the induction that runs them together.

`shiftIter w m a` applies the coefficient shift `m` times, by `w 0, …, w (m-1)`.  The
claim is that if `polyOf m a` has all its roots in the closed disk `D(p,ρ)`, its top
normalized coefficient is nonzero, and every `w i` is strictly outside, then the
surviving entry `shiftIter w m a 0` is nonzero.

The step is exactly one application of each banked lemma:

* `Vieta.shift_top_ne_zero` — the top coefficient survives, so the degree drops by
  exactly one and the induction hypothesis applies at `m`;
* `PolyOf.polar_shift_poly` — the shifted sequence's polynomial is (a scalar times)
  the polar derivative;
* `LagGen.laguerre_general` — so its roots are still in the disk.

At `m = 0` the surviving entry is `a 0`, which is the hypothesis.  That is where the
non-vanishing actually comes from: the chain of "top coefficient nonzero" is not
bookkeeping, it *is* the conclusion.
-/

/-- The coefficient shift, iterated. -/
noncomputable def shiftIter (w : ℕ → ℂ) : ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | 0,     a => a
  | m + 1, a => shiftIter w m (PolyOf.shift (w m) a)

@[simp] theorem shiftIter_zero (w : ℕ → ℂ) (a : ℕ → ℂ) : shiftIter w 0 a = a := rfl

@[simp] theorem shiftIter_succ (w : ℕ → ℂ) (m : ℕ) (a : ℕ → ℂ) :
    shiftIter w (m + 1) a = shiftIter w m (PolyOf.shift (w m) a) := rfl

theorem leadingCoeff_polyOf {m : ℕ} {a : ℕ → ℂ} (ha : a m ≠ 0) :
    (polyOf m a).leadingCoeff = a m := by
  rw [Polynomial.leadingCoeff, PolyOf.natDegree_eq ha, PolyOf.coeff_polyOf]
  simp

theorem coeff_polyOf_sub (m : ℕ) (a : ℕ → ℂ) :
    (polyOf (m + 1) a).coeff m = ((m : ℂ) + 1) * a m := by
  rw [PolyOf.coeff_polyOf, if_pos (by simp : m ∈ range (m + 2))]
  have hch : ((m + 1).choose m : ℂ) = (m : ℂ) + 1 := by
    rw [Nat.choose_succ_self_right]
    push_cast
    ring
  rw [hch]

/-- **Grace's iteration.** -/
theorem grace_ind {p : ℂ} {rho : ℝ} (w : ℕ → ℂ) (hw : ∀ i, rho < ‖w i - p‖) :
    ∀ (m : ℕ) (a : ℕ → ℂ), a m ≠ 0 →
      (∀ r ∈ (polyOf m a).roots, ‖r - p‖ ≤ rho) →
      shiftIter w m a 0 ≠ 0 := by
  intro m
  induction m with
  | zero => intro a ha _; exact ha
  | succ m ih =>
      intro a ha hroots
      have hdeg : (polyOf (m + 1) a).natDegree = m + 1 := PolyOf.natDegree_eq ha
      have hg0 : polyOf (m + 1) a ≠ 0 := PolyOf.polyOf_ne_zero ha
      have hlead : (polyOf (m + 1) a).leadingCoeff = a (m + 1) := leadingCoeff_polyOf ha
      have hcm : (polyOf (m + 1) a).coeff m = ((m : ℂ) + 1) * a m := coeff_polyOf_sub m a
      -- (i) the top coefficient survives, so the degree drops by exactly one
      have htop : PolyOf.shift (w m) a m ≠ 0 := by
        show a m + w m * a (m + 1) ≠ 0
        exact Sendov9.Vieta.shift_top_ne_zero hdeg hg0 hlead hcm ha hroots (hw m)
      -- (ii) the roots stay in the disk
      have hroots' : ∀ r ∈ (polyOf m (PolyOf.shift (w m) a)).roots, ‖r - p‖ ≤ rho := by
        intro r hr
        by_contra hcon
        push_neg at hcon
        have hzero : (polyOf m (PolyOf.shift (w m) a)).eval r = 0 :=
          Polynomial.isRoot_of_mem_roots hr
        have hev := congrArg (Polynomial.eval r) (PolyOf.polar_shift_poly m a (w m))
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_C, Polynomial.eval_X] at hev
        rw [hzero, mul_zero] at hev
        have hL := Sendov9.LagGen.laguerre_general hg0 (by rw [hdeg]; omega)
          hroots (hw m) hcon
        rw [hdeg] at hL
        push_cast at hL
        exact hL hev
      rw [shiftIter_succ]
      exact ih (PolyOf.shift (w m) a) htop hroots'

end Sendov9.Grace



namespace Sendov9.Apolarity

open Finset

/-!
# Stage four: the apolarity form, and why Grace needs no degree bookkeeping

With Laguerre done (`Laguerre3`), Grace's apolarity theorem is the next stage.  Its
proof applies the polar derivatives `D_{w₁}, …, D_{wₙ}` in succession to a polynomial
whose zeros lie in a disk, and identifies the resulting constant with the apolarity
form.  Formalizing that naively means tracking polynomial degrees through `n`
applications, which is the part everyone dreads.

It is avoidable.  Writing `f = ∑ₖ C(n,k) aₖ zᵏ` in the *normalized* basis, a CAS check
(n = 1..6) confirms

    n·f + (ζ - z)·f' = n · ∑ₖ C(n-1,k) (aₖ + ζ·aₖ₊₁) zᵏ

— the polar derivative is nothing but the **coefficient shift** `aₖ ↦ aₖ + ζ·aₖ₊₁`,
times `n`.  So the `n`-fold composite contributes `n!` and its surviving entry is what
this file computes.

Define the pairing of a coefficient sequence against a family `x`,

    ⟪a, x⟫_s = ∑ₖ aₖ · eₖ(x on s).

Then `pair_insert` says adjoining one point to `s` is exactly one coefficient shift:

    ⟪a, x⟫_{insert i s} = ⟪(aₖ + xᵢ·aₖ₊₁), x⟫_s

and iterating strips `s` to `∅`, where the pairing is just `a₀`.  That is the
apolarity form, reached with no polynomial and hence no degree bookkeeping — the
recursion is the same `esymm_insert` that drove the Maclaurin discharge.

**Scope.**  This is the algebraic half of Grace.  The analytic half — that each polar
derivative keeps its zeros in the disk, iterated `n` times, with the degree staying
exactly `n-1` at each step (it does: the leading coefficient `n(aₙ₋₁ + ζ)` vanishes
only at the centroid, which is inside the disk while `ζ` is outside) — still has to be
assembled on top of `Laguerre3`.  Sendov's conjecture in degree nine remains unproven.
-/

variable {ι : Type*} [DecidableEq ι]

/-- `eₘ` of a family over a finite index set. -/
noncomputable def E (x : ι → ℂ) (s : Finset ι) (m : ℕ) : ℂ :=
  ∑ A ∈ s.powersetCard m, ∏ k ∈ A, x k

@[simp] theorem E_zero (x : ι → ℂ) (s : Finset ι) : E x s 0 = 1 := by
  simp [E, Finset.powersetCard_zero]

/-- Above the cardinality there are no subsets, so `eₘ` vanishes. -/
theorem E_eq_zero_of_lt {x : ι → ℂ} {s : Finset ι} {m : ℕ} (h : s.card < m) :
    E x s m = 0 := by
  rw [E, Finset.powersetCard_eq_empty.mpr h, Finset.sum_empty]

@[simp] theorem E_empty (x : ι → ℂ) (m : ℕ) : E x (∅ : Finset ι) (m + 1) = 0 :=
  E_eq_zero_of_lt (by simp)

/-- Adjoining one coordinate (the same recursion as the Maclaurin engine). -/
theorem esymm_insert {t : Finset ι} {i : ι} (hi : i ∉ t) (x : ι → ℂ) (m : ℕ) :
    E x (insert i t) (m + 1) = E x t (m + 1) + x i * E x t m := by
  unfold E
  rw [Finset.powersetCard_succ_insert hi]
  have hdisj : Disjoint (t.powersetCard (m + 1)) ((t.powersetCard m).image (insert i)) := by
    rw [Finset.disjoint_right]
    rintro A hA hA'
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    have hsub : insert i B ⊆ t := (Finset.mem_powersetCard.mp hA').1
    exact hi (hsub (Finset.mem_insert_self i B))
  rw [Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun B hB => ?_
    have hiB : i ∉ B := fun h => hi ((Finset.mem_powersetCard.mp hB).1 h)
    rw [Finset.prod_insert hiB]
  · intro B hB C hC hBC
    have hiB : i ∉ B := fun h => hi ((Finset.mem_powersetCard.mp hB).1 h)
    have hiC : i ∉ C := fun h => hi ((Finset.mem_powersetCard.mp hC).1 h)
    have := congrArg (fun s => Finset.erase s i) hBC
    simpa [Finset.erase_insert hiB, Finset.erase_insert hiC] using this

/-! ### The pairing -/

/-- `⟪a, x⟫_s = ∑ₖ aₖ eₖ(x on s)`, truncated at `N`.  This is the apolarity form when
`s` indexes the zeros. -/
noncomputable def pair (N : ℕ) (a : ℕ → ℂ) (x : ι → ℂ) (s : Finset ι) : ℂ :=
  ∑ k ∈ range (N + 1), a k * E x s k

/-- On the empty index set only `a₀` survives. -/
theorem pair_empty (N : ℕ) (a : ℕ → ℂ) (x : ι → ℂ) : pair N a x ∅ = a 0 := by
  unfold pair
  rw [Finset.sum_range_succ']
  simp

/-- **One point ↔ one coefficient shift.**  This is the whole content: adjoining a
point to the index set is exactly the polar derivative's action `aₖ ↦ aₖ + xᵢ aₖ₊₁`
on the normalized coefficients. -/
theorem pair_insert {N : ℕ} {s : Finset ι} {i : ι} (hi : i ∉ s) (hcard : s.card ≤ N)
    (a : ℕ → ℂ) (x : ι → ℂ) :
    pair (N + 1) a x (insert i s) = pair N (fun k => a k + x i * a (k + 1)) x s := by
  have hzero : E x s (N + 1) = 0 := E_eq_zero_of_lt (by omega)
  have hL : pair (N + 1) a x (insert i s)
      = (∑ k ∈ range N, a (k + 1) * E x s (k + 1)) + a 0
        + x i * ∑ k ∈ range (N + 1), a (k + 1) * E x s k := by
    unfold pair
    rw [Finset.sum_range_succ' (fun k => a k * E x (insert i s) k) (N + 1)]
    have hstep : ∀ k ∈ range (N + 1),
        a (k + 1) * E x (insert i s) (k + 1)
          = a (k + 1) * E x s (k + 1) + x i * (a (k + 1) * E x s k) := by
      intro k _
      rw [esymm_insert hi x k]; ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_range_succ (fun k => a (k + 1) * E x s (k + 1)) N, hzero]
    simp only [E_zero, mul_one, mul_zero, add_zero]
    ring
  have hR : pair N (fun k => a k + x i * a (k + 1)) x s
      = (∑ k ∈ range N, a (k + 1) * E x s (k + 1)) + a 0
        + x i * ∑ k ∈ range (N + 1), a (k + 1) * E x s k := by
    unfold pair
    have hexp : ∀ k ∈ range (N + 1),
        (a k + x i * a (k + 1)) * E x s k
          = a k * E x s k + x i * (a (k + 1) * E x s k) := fun k _ => by ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_range_succ' (fun k => a k * E x s k) N]
    simp only [E_zero, mul_one]
  rw [hL, hR]

end Sendov9.Apolarity

namespace Sendov9.Grace2

open Polynomial Finset Sendov9.PolyOf

/-!
# Stage twelve: Grace's apolarity theorem

`Grace.grace_ind` says the iterated shift's surviving entry is nonzero.
`Apolarity.pair` says what that entry *is*.  Joining them gives Grace.

The join is one induction and no new mathematics: `Apolarity.pair_insert` peels one
point off the index set and `Grace.shiftIter_succ` peels one shift, and they are the
same operation — that was the whole point of `PolarShift`.  With `range (m+1) =
insert m (range m)` the two recursions line up exactly, and at `m = 0` both sides are
`a 0`.

The result, `grace_apolarity`, is Grace's theorem in the shape the coincidence theorem
consumes: if a polynomial's roots all lie in a closed disk and its normalized
coefficients are paired against points all lying strictly outside, the apolarity form
cannot vanish.  Contrapositively — which is how it is used — if the form *does*
vanish, some `w i` must lie in the disk.
-/

/-- **The iterated shift is the apolarity form.** -/
theorem shiftIter_eq_pair (w : ℕ → ℂ) :
    ∀ (m : ℕ) (a : ℕ → ℂ),
      Sendov9.Apolarity.pair m a w (range m) = Sendov9.Grace.shiftIter w m a 0 := by
  intro m
  induction m with
  | zero =>
      intro a
      rw [Finset.range_zero, Sendov9.Apolarity.pair_empty]
      rfl
  | succ m ih =>
      intro a
      rw [Finset.range_add_one,
        Sendov9.Apolarity.pair_insert (by simp) (by simp) a w,
        Sendov9.Grace.shiftIter_succ]
      exact ih (PolyOf.shift (w m) a)

/-- **Grace's apolarity theorem.**

If every root of `polyOf m a` lies in the closed disk `D(p,ρ)`, the top normalized
coefficient is nonzero, and every `w i` lies strictly outside, then the apolarity form
`∑ₖ aₖ eₖ(w)` does not vanish.

Used contrapositively: a vanishing apolarity form forces some `w i` into the disk —
which is exactly how the coincidence theorem produces its point. -/
theorem grace_apolarity {p : ℂ} {rho : ℝ} (w : ℕ → ℂ) (hw : ∀ i, rho < ‖w i - p‖)
    (m : ℕ) (a : ℕ → ℂ) (ha : a m ≠ 0)
    (hroots : ∀ r ∈ (polyOf m a).roots, ‖r - p‖ ≤ rho) :
    Sendov9.Apolarity.pair m a w (range m) ≠ 0 := by
  rw [shiftIter_eq_pair w m a]
  exact Sendov9.Grace.grace_ind w hw m a ha hroots

end Sendov9.Grace2

#print axioms Sendov9.Grace2.shiftIter_eq_pair
#print axioms Sendov9.Grace2.grace_apolarity
