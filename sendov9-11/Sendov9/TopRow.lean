import Mathlib
import Sendov9.TopEmajEq
import Sendov9.TopJ
import Sendov9.RowPrep
import Sendov9.RangeTop
import Sendov9.Sigma22Gen

set_option maxHeartbeats 4000000

namespace Sendov9.TopRow

open Finset

/-!
# The boundary range `9/10 ≤ a ≤ 1` is excluded

`a = 1` is immediate (`one_excluded`: localization degenerates to `u ≥ 1` against
`‖μ‖ < 1`).  For `9/10 ≤ a < 1` this runs §5 of the paper:

    σ ≤ 39/5                  `SigmaGen.sigma_boundary` at `M = 2`, `ν = 5`
    1 - u ≤ (19/20)δ          `Top.one_sub_u_le`
    η² ≤ (19/10)δ - (361/400)δ²   `Top.eta_sq_le`
    x = √δ, y = η/x           `Top.box_bounds` puts `(x,y)` in the certificate's box
    |I - J| ≤ ∑ₘ cₘ ηᵐ ∫₀^{1-x²}   `TopPt.norm_I_sub_J_le_E`
    |J| ≥ 1/9 + η²/18 - δ/1000     `norm_J_ge` + `TopJ.R9_le`
    ⟹ |I| - a/9 ≥ δ·𝒫(x,y) > δ/100 > 0,  against `|I| < a/9`

The one place arithmetic has to be done by hand is the last implication.  With
`a = 1 - δ` and `η² = δy²`,

    |I| - a/9 ≥ (1/9 + δy²/18 - δ/1000 - x²·ℰ) - (1-δ)/9 = δ(1/9 + y²/18 - 1/1000 - ℰ),

which is `δ·𝒫` exactly — the `x²` in front of `ℰ` (`TopEq.Emaj_eqW`) is what makes the
factored `δ` come out right.

Sendov's conjecture in degree nine remains unproven.
-/

/-- The seven-term bracket of `ℰ`, kept as a DEFINITION.  Inlining it makes
`δ·(bracket)` ring-expand into hundreds of monomials, which stalls both `ring` and
`linarith` in `top_excluded`'s closing step; as a def it stays one atom. -/
noncomputable def Eterms (x y : ℝ) : ℝ :=
(4 : ℝ) * x ^ 0 * y ^ 2 * ((1/3 : ℝ) * TopEq.W x ^ 3
        + (3/5 : ℝ) * TopEq.Q2 x y * TopEq.W x ^ 5
        + (3/7 : ℝ) * TopEq.Q2 x y ^ 2 * TopEq.W x ^ 7
        + (1/9 : ℝ) * TopEq.Q2 x y ^ 3 * TopEq.W x ^ 9
        + (3/4 : ℝ) * TopEq.Q1 x * TopEq.W x ^ 4
        + (1 : ℝ) * TopEq.Q1 x * TopEq.Q2 x y * TopEq.W x ^ 6
        + (3/8 : ℝ) * TopEq.Q1 x * TopEq.Q2 x y ^ 2 * TopEq.W x ^ 8
        + (3/5 : ℝ) * TopEq.Q1 x ^ 2 * TopEq.W x ^ 5
        + (3/7 : ℝ) * TopEq.Q1 x ^ 2 * TopEq.Q2 x y * TopEq.W x ^ 7
        + (1/6 : ℝ) * TopEq.Q1 x ^ 3 * TopEq.W x ^ 6)
      + (264/35 : ℝ) * x ^ 1 * y ^ 3 * ((1/4 : ℝ) * TopEq.W x ^ 4
        + (1/3 : ℝ) * TopEq.Q2 x y * TopEq.W x ^ 6
        + (1/8 : ℝ) * TopEq.Q2 x y ^ 2 * TopEq.W x ^ 8
        + (2/5 : ℝ) * TopEq.Q1 x * TopEq.W x ^ 5
        + (2/7 : ℝ) * TopEq.Q1 x * TopEq.Q2 x y * TopEq.W x ^ 7
        + (1/6 : ℝ) * TopEq.Q1 x ^ 2 * TopEq.W x ^ 6)
      + (24 : ℝ) * x ^ 2 * y ^ 4 * ((1/5 : ℝ) * TopEq.W x ^ 5
        + (2/7 : ℝ) * TopEq.Q2 x y * TopEq.W x ^ 7
        + (1/9 : ℝ) * TopEq.Q2 x y ^ 2 * TopEq.W x ^ 9
        + (1/3 : ℝ) * TopEq.Q1 x * TopEq.W x ^ 6
        + (1/4 : ℝ) * TopEq.Q1 x * TopEq.Q2 x y * TopEq.W x ^ 8
        + (1/7 : ℝ) * TopEq.Q1 x ^ 2 * TopEq.W x ^ 7)
      + (56 : ℝ) * x ^ 3 * y ^ 5 * ((1/6 : ℝ) * TopEq.W x ^ 6
        + (1/8 : ℝ) * TopEq.Q2 x y * TopEq.W x ^ 8
        + (1/7 : ℝ) * TopEq.Q1 x * TopEq.W x ^ 7)
      + (28 : ℝ) * x ^ 4 * y ^ 6 * ((1/7 : ℝ) * TopEq.W x ^ 7
        + (1/9 : ℝ) * TopEq.Q2 x y * TopEq.W x ^ 9
        + (1/8 : ℝ) * TopEq.Q1 x * TopEq.W x ^ 8)
      + (8 : ℝ) * x ^ 5 * y ^ 7 * ((1/8 : ℝ) * TopEq.W x ^ 8)
      + (1 : ℝ) * x ^ 6 * y ^ 8 * ((1/9 : ℝ) * TopEq.W x ^ 9)

/-- The certificate's `𝒫(x,y)`. -/
noncomputable def Pb (x y : ℝ) : ℝ :=
  (1 : ℝ) / 9 + y ^ 2 / 18 - 1 / 1000 - Eterms x y

/-- `TopEq.Emaj_eqW` with the bracket folded. -/
theorem Emaj_folded (x y : ℝ) :
    (∑ m ∈ Finset.Icc 2 8, MidPt.cc m * (x * y) ^ m
        * ∫ t in (0:ℝ)..(1 - x ^ 2), t ^ m * TopAn.qb x y t ^ MidPt.ell m)
      = x ^ 2 * Eterms x y := TopEq.Emaj_eqW x y

/-- **The certificate, at `(x,y)` rather than `(U,V)`.**  `U = 25x/8`, `V = 5y/7`. -/
theorem cert_at {x y : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 8/25) (hy0 : 0 ≤ y) (hy : y ≤ 7/5) :
    (1 : ℝ) / 100 < Pb x y := by
  have hU0 : (0:ℝ) ≤ 25 * x / 8 := by linarith
  have hU1 : 25 * x / 8 ≤ 1 := by linarith
  have hV0 : (0:ℝ) ≤ 5 * y / 7 := by linarith
  have hV1 : 5 * y / 7 ≤ 1 := by linarith
  have h := Cert.bdry_pos hU0 hU1 hV0 hV1
  have hxU : (8/25 : ℝ) * (25 * x / 8) = x := by ring
  have hyV : (7/5 : ℝ) * (5 * y / 7) = y := by ring
  -- this `simp only` also zeta-reduces `bdry_pos`'s `let`s, leaving `h` in raw form
  simp only [hxU, hyV] at h
  have hnum : (1:ℝ)/100
      < 139392070260030830922829855080988292511/11102230246251565404236316680908203125000 := by
    norm_num
  refine lt_of_lt_of_le hnum (le_trans h (le_of_eq ?_))
  unfold Pb Eterms TopEq.W TopEq.Q1 TopEq.Q2
  ring

/-- **The boundary range is excluded.** -/
theorem top_excluded (C : Counterexample)
    (hsep : ∀ k, (681/1000 : ℝ) ≤ C.r k)
    (hprod : (9:ℝ) ≤ ∏ k, C.r k)
    (hI : ‖∫ t in (0:ℝ)..C.a, ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹)‖
      < C.a / 9)
    (h0 : (9/10 : ℝ) ≤ C.a) (h1 : C.a ≤ 1) : False := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · exact one_excluded C heq
  -- ### `9/10 ≤ a < 1`
  set delta : ℝ := 1 - C.a with hdel
  have hd0 : 0 < delta := by rw [hdel]; linarith
  have hd : delta ≤ 1/10 := by rw [hdel]; linarith
  have ha0 : 0 < C.a := by linarith
  -- σ ≤ 39/5 at `M = 2`, `ν = 5`
  have hrle : ∀ k, C.r k ≤ (2 : ℝ) := fun k => le_trans (RowPrep.r_le C k) (by linarith)
  have hsig : C.sigma ≤ (39/5 : ℝ) := by
    rw [RowPrep.sigma_eq C]
    exact SigmaGen.sigma_boundary C.r hsep hrle hprod
  -- `1 - u ≤ (19/20)δ`
  have hloc := localization C
  -- `C.u` and `C.mu.re` are defeq but DISTINCT ATOMS to linarith; bridge once.
  have hue : C.u = C.mu.re := rfl
  have hone : 1 - C.mu.re ≤ (19/20 : ℝ) * delta := by
    have h := Top.one_sub_u_le h0 h1 hsig hloc
    rw [hue] at h
    rw [hdel]
    linarith [h]
  -- `η² ≤ (19/10)δ - (361/400)δ²`
  have hu1 : C.mu.re ≤ 1 := le_of_lt (lt_of_le_of_lt (Complex.re_le_norm C.mu)
    (mu_norm_lt_one C))
  have hetau := eta_sq_le_one_sub_u_sq C
  have hetad : C.eta ^ 2 ≤ 19/10 * delta - 361/400 * delta ^ 2 :=
    Top.eta_sq_le hd0.le hd hone hu1 hetau
  have heta0 : 0 ≤ C.eta := eta_nonneg C
  -- `x = √δ`, `y = η/x`
  set x : ℝ := Real.sqrt delta with hxdef
  have hx0 : 0 < x := Real.sqrt_pos.mpr hd0
  have hx2 : x ^ 2 = delta := Real.sq_sqrt hd0.le
  set y : ℝ := C.eta / x with hydef
  have hy0 : 0 ≤ y := div_nonneg heta0 hx0.le
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hxy : x * y = C.eta := by rw [hydef]; field_simp
  obtain ⟨hxb, hyb⟩ := Top.box_bounds hx0 hy0 hx2.symm hxy.symm hd0 hd hetad
  -- `y² ≤ 19/10`, which `qb_le_one` needs and the box alone does not give
  have hy2 : y ^ 2 ≤ 19/10 := by
    have hxy2 : delta * y ^ 2 = C.eta ^ 2 := by rw [← hx2, ← hxy]; ring
    have hle : delta * y ^ 2 ≤ delta * (19/10) := by
      rw [hxy2]
      nlinarith [hetad, sq_nonneg delta]
    exact le_of_mul_le_mul_left hle hd0
  -- the two integrals, over `[0, 1-x²] = [0, a]`
  have haW : (1 : ℝ) - x ^ 2 = C.a := by rw [hx2, hdel]; ring
  have hnsq : Complex.normSq C.mu = 1 - x ^ 2 * y ^ 2 := by
    have := eta_sq C
    have hxy2 : x ^ 2 * y ^ 2 = C.eta ^ 2 := by rw [← hxy]; ring
    rw [hxy2]; linarith
  have hIJ0 := TopPt.norm_I_sub_J_le_E (x := x) (y := y) (eta := C.eta) (u := C.mu.re)
    C.mu C.D hx0.le hxb hy0 hy2 hxy.symm heta0 rfl hnsq (by rw [hx2]; exact hone)
    (sum_D_zero C) (sum_normSq_D_le C) (by rw [haW]; linarith)
  rw [haW] at hIJ0
  have hprodrw : ∀ t : ℝ, (∏ j, ((1 : ℂ) - (t : ℂ) * (C.mu + C.D j)))
      = ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹) := by
    intro t
    exact Finset.prod_congr rfl fun j _ => by rw [MidRow.mu_add_D C j]
  simp only [hprodrw] at hIJ0
  -- `|J| ≥ 1/9 + η²/18 - δ/1000`
  have hmu0 : C.mu ≠ 0 := by
    intro hcon
    have := TopJ.norm_mu_ge (u := C.mu.re) C.mu rfl hd0.le hd hone
    rw [hcon] at this
    simp at this
    linarith
  have hnormsq : ‖C.mu‖ ^ 2 = 1 - C.eta ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    have := eta_sq C; linarith
  have heta1 : C.eta < 1 := by nlinarith [hetad, hd, hd0, heta0]
  have hJ0 := norm_J_ge hmu0 C.a C.eta hnormsq heta0 heta1
  have hnsqE : Complex.normSq C.mu = 1 - C.eta ^ 2 := by
    have := eta_sq C; linarith
  have hRsq : ‖1 - (C.a : ℂ) * C.mu‖ ^ 2 ≤ (19/10 : ℝ) * delta :=
    TopJ.R_sq_le (u := C.mu.re) C.mu hdel hd0.le hd rfl hnsqE hone
  have hmuge : (181/200 : ℝ) ≤ ‖C.mu‖ :=
    TopJ.norm_mu_ge (u := C.mu.re) C.mu rfl hd0.le hd hone
  have hR9 := TopJ.R9_le hd0.le hd (norm_nonneg (1 - (C.a : ℂ) * C.mu)) hRsq hmuge
  have hJcf := J_closed_form hmu0 C.a
  have hJ : 1/9 + C.eta ^ 2 / 18 - delta / 1000
      ≤ ‖∫ t in (0:ℝ)..C.a, ((1 : ℂ) - (t : ℂ) * C.mu) ^ 8‖ := by
    rw [hJcf]; linarith [hJ0, hR9]
  -- triangle, then the certificate
  have htri : ‖∫ t in (0:ℝ)..C.a, ((1 : ℂ) - (t : ℂ) * C.mu) ^ 8‖
      - ‖(∫ t in (0:ℝ)..C.a, ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹))
          - (∫ t in (0:ℝ)..C.a, ((1 : ℂ) - (t : ℂ) * C.mu) ^ 8)‖
      ≤ ‖∫ t in (0:ℝ)..C.a, ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹)‖ := by
    have := norm_sub_norm_le
      (∫ t in (0:ℝ)..C.a, ((1 : ℂ) - (t : ℂ) * C.mu) ^ 8)
      (∫ t in (0:ℝ)..C.a, ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹))
    rw [norm_sub_rev] at this
    linarith
  -- `δ·𝒫 ≤ |I| - a/9`
  have hEm := Emaj_folded x y
  rw [haW] at hEm
  have hlow : delta * Pb x y
      ≤ ‖∫ t in (0:ℝ)..C.a, ∏ j, ((1 : ℂ) - (t : ℂ) * ((C.a : ℂ) - C.zeta j)⁻¹)‖
        - C.a / 9 := by
    have hetasq : C.eta ^ 2 = delta * y ^ 2 := by
      rw [← hxy, ← hx2]; ring
    have ha : C.a = 1 - delta := by rw [hdel]; ring
    -- normalise onto `delta`; `TopEq.W x` etc. are def applications, so this rewrites
    -- only the explicit `x ^ 2` factor and leaves the brackets matching `Pb`
    rw [hx2] at hEm
    -- `hIJ0`'s sum carries `C.eta ^ m` while `hEm`/`hPbB` carry `(x*y) ^ m`.  They are
    -- equal but DISTINCT ATOMS to linarith, so the two sums never cancel.  Align them.
    rw [← hxy] at hIJ0
    -- keep the seven-term bracket FOLDED: handing `delta * (7 terms)` to linarith makes it
    -- ring-normalise into hundreds of monomials and it stalls.  One `ring` absorbs it into
    -- the (opaque) integral sum, after which the remaining step is genuinely linear.
    have hPbB : delta * Pb x y
        = delta * (1/9 + y ^ 2 / 18 - 1/1000)
          - (∑ m ∈ Finset.Icc 2 8, MidPt.cc m * (x * y) ^ m
              * ∫ t in (0:ℝ)..C.a, t ^ m * TopAn.qb x y t ^ MidPt.ell m) := by
      rw [hEm]
      unfold Pb
      ring
    rw [hPbB]
    linarith [hIJ0, hJ, htri, hetasq, ha]
  exact Top.contradiction hd0 (cert_at hx0.le hxb hy0 hyb) hlow hI

end Sendov9.TopRow

#print axioms Sendov9.TopRow.cert_at
#print axioms Sendov9.TopRow.top_excluded
