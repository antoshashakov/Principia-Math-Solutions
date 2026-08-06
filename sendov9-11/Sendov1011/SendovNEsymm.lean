import Mathlib
import SendovNSigma

set_option maxHeartbeats 4000000

/-!
# P6 (hard half): the Cauchy coefficient estimate, by roots-of-unity extraction

The plan's `EspCauchy` module, contour-free.  For a centred family `d : Fin N → ℂ`
(`∑ dⱼ = 0`, `∑‖dⱼ‖² ≤ Nη²`) and `1 ≤ m < N`:

* `esymm_extract` — the finite coefficient-extraction identity
  `(N+1)·e_m(d)·z^m = ∑_{k<N+1} ζ^{-km} ∏ⱼ(1 + z ζ^k dⱼ)` for any primitive
  `(N+1)`-st root of unity `ζ` (orthogonality via `geom_sum_mul`; no aliasing
  because all degrees are `≤ N < N+1`);
* `H_bound` — `‖∏ⱼ(1 + w dⱼ)‖² ≤ (1 + ‖w‖²η²)^N`, by AM–GM over the `N` factors
  (the same weighted-AM–GM step as `SendovNEsp.eN_bound`), using
  `∑ⱼ‖1 + w dⱼ‖² = N + ‖w‖²∑‖dⱼ‖²` (the cross terms vanish since `∑ dⱼ = 0`);
* `esymm_le` — `‖e_m(d)‖ ≤ c·η^m` for any rational `c ≥ 0` with
  `N^N ≤ c²·m^m·(N-m)^{N-m}`, by optimizing at `r² = m/((N-m)η²)`; everything is
  kept in squares so only integer exponents appear.

The degree-11 `c₄` entry is the **Cauchy** constant `c₄ = 1447/50` (the Schoenberg
route is deleted per the c4-experiment decision); its validity is the single
`norm_num` goal `(1447/50)²·4⁴·6⁶ ≥ 10¹⁰`, checked in `c4_deg11` below.
-/

namespace SendovN.EspCauchy

open Finset

variable {N : ℕ}

/-- The generating identity `∏ⱼ(1 + w dⱼ) = ∑_{m ≤ N} e_m(d) w^m`, an instance of
`prod_sub_eq_sum_esD`. -/
theorem prod_one_add_eq (d : Fin N → ℂ) (w : ℂ) :
    ∏ j, (1 + w * d j) = ∑ m ∈ range (N + 1), esD d m * w ^ m := by
  have h := prod_sub_eq_sum_esD (1 : ℂ) (-w) d
  calc ∏ j, (1 + w * d j) = ∏ j, ((1:ℂ) - (-w) * d j) := by
        refine Finset.prod_congr rfl fun j _ => by ring
    _ = ∑ m ∈ range (N + 1), (-(-w)) ^ m * (1:ℂ) ^ (N - m) * esD d m := h
    _ = ∑ m ∈ range (N + 1), esD d m * w ^ m := by
        refine Finset.sum_congr rfl fun m _ => by rw [neg_neg, one_pow]; ring

/-- **Coefficient extraction by `(N+1)`-st roots of unity** (no contour integrals):
`(N+1)·e_m(d)·z^m = ∑_{k<N+1} ζ^{-km} ∏ⱼ(1 + z ζ^k dⱼ)`. -/
theorem esymm_extract {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (N + 1)) {m : ℕ} (hm : m ≤ N)
    (d : Fin N → ℂ) (z : ℂ) :
    ((N : ℂ) + 1) * esD d m * z ^ m
      = ∑ k ∈ range (N + 1), (ζ ^ (k * m))⁻¹ * ∏ j, (1 + z * ζ ^ k * d j) := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    have h1 := hζ.pow_eq_one
    rw [h, zero_pow (Nat.succ_ne_zero N)] at h1
    exact zero_ne_one h1
  have hζm : ζ ^ m ≠ 0 := pow_ne_zero _ hζ0
  -- expand each product and rearrange the summand
  have hterm : ∀ k ∈ range (N + 1),
      (ζ ^ (k * m))⁻¹ * ∏ j, (1 + z * ζ ^ k * d j)
        = ∑ m' ∈ range (N + 1), esD d m' * z ^ m' * (ζ ^ m' * (ζ ^ m)⁻¹) ^ k := by
    intro k _
    have hgen := prod_one_add_eq d (z * ζ ^ k)
    rw [hgen, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m' _ => by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  -- orthogonality: only `m' = m` survives
  have hinner : ∀ m' ∈ range (N + 1), m' ≠ m →
      ∑ k ∈ range (N + 1), esD d m' * z ^ m' * (ζ ^ m' * (ζ ^ m)⁻¹) ^ k = 0 := by
    intro m' hm' hne
    have hx1 : ζ ^ m' * (ζ ^ m)⁻¹ ≠ 1 := by
      intro hx
      rw [mul_inv_eq_one₀ hζm] at hx
      exact hne (hζ.pow_inj (mem_range.mp hm') (by omega) hx)
    have hxpow : (ζ ^ m' * (ζ ^ m)⁻¹) ^ (N + 1) = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul,
        Nat.mul_comm m' (N + 1), Nat.mul_comm m (N + 1), pow_mul, pow_mul,
        hζ.pow_eq_one, one_pow, one_pow, inv_one, mul_one]
    have hgeo : ∑ k ∈ range (N + 1), (ζ ^ m' * (ζ ^ m)⁻¹) ^ k = 0 := by
      have hmul := geom_sum_mul (ζ ^ m' * (ζ ^ m)⁻¹) (N + 1)
      rw [hxpow, sub_self] at hmul
      exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero_of_ne hx1)
    rw [← Finset.mul_sum, hgeo, mul_zero]
  rw [Finset.sum_eq_single_of_mem m (mem_range.mpr (by omega)) hinner,
    mul_inv_cancel₀ hζm]
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **The Cauchy modulus bound** `‖∏ⱼ(1 + w dⱼ)‖² ≤ (1 + ‖w‖²η²)^N`, by AM–GM
over the `N` factors (the cross terms vanish because `∑ dⱼ = 0`). -/
theorem H_bound (hN : 1 ≤ N) (d : Fin N → ℂ) (eta : ℝ) (w : ℂ)
    (hz : ∑ j, d j = 0) (hD : ∑ j, ‖d j‖ ^ 2 ≤ (N : ℝ) * eta ^ 2) :
    ‖∏ j, (1 + w * d j)‖ ^ 2 ≤ (1 + ‖w‖ ^ 2 * eta ^ 2) ^ N := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : ((N : ℕ) : ℝ) ≠ 0 := ne_of_gt hNR
  -- pointwise expansion of the squared factor norms
  have hx : ∀ j : Fin N, ‖1 + w * d j‖ ^ 2
      = 1 + 2 * (w * d j).re + ‖w‖ ^ 2 * ‖d j‖ ^ 2 := by
    intro j
    have hns1 : Complex.normSq 1 = 1 := by simp
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_mul, hns1,
      one_mul, Complex.conj_re, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    ring
  -- the arithmetic mean: `∑ⱼ‖1 + w dⱼ‖² ≤ N(1 + ‖w‖²η²)`
  have hre : ∑ j, (w * d j).re = 0 := by
    have h1 : ∑ j, w * d j = 0 := by rw [← Finset.mul_sum, hz, mul_zero]
    calc ∑ j, (w * d j).re = (∑ j, w * d j).re := (Complex.re_sum _ _).symm
      _ = 0 := by rw [h1]; simp
  have hsum : ∑ j, ‖1 + w * d j‖ ^ 2 ≤ (N : ℝ) * (1 + ‖w‖ ^ 2 * eta ^ 2) := by
    have hexp : ∑ j, ‖1 + w * d j‖ ^ 2
        = (N : ℝ) + 2 * ∑ j, (w * d j).re + ‖w‖ ^ 2 * ∑ j, ‖d j‖ ^ 2 := by
      rw [Finset.sum_congr rfl fun j _ => hx j, Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp [Finset.card_univ]
    rw [hexp, hre]
    have h2 := mul_le_mul_of_nonneg_left hD (sq_nonneg ‖w‖)
    nlinarith [h2]
  -- AM–GM with uniform weights `1/N` (as in `eN_bound`)
  have hxnn : ∀ j ∈ (univ : Finset (Fin N)), (0:ℝ) ≤ ‖1 + w * d j‖ ^ 2 :=
    fun j _ => sq_nonneg _
  have hw' : ∀ j ∈ (univ : Finset (Fin N)), (0:ℝ) ≤ 1 / (N:ℝ) := fun j _ => by positivity
  have hw1 : ∑ _j : Fin N, (1 / (N:ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hamgm := Real.geom_mean_le_arith_mean_weighted univ (fun _ => 1 / (N:ℝ))
    (fun j => ‖1 + w * d j‖ ^ 2) hw' hw1 hxnn
  set X : ℝ := ∏ j, ‖1 + w * d j‖ ^ 2 with hX
  have hX0 : 0 ≤ X := Finset.prod_nonneg fun j _ => sq_nonneg _
  have hlhs : ∏ j, (‖1 + w * d j‖ ^ 2) ^ (1 / (N:ℝ) : ℝ) = X ^ (1 / (N:ℝ) : ℝ) := by
    rw [hX, ← Real.finsetProd_rpow univ _ (fun j _ => sq_nonneg _) _]
  have hrhs : ∑ j, (1 / (N:ℝ)) * ‖1 + w * d j‖ ^ 2 ≤ 1 + ‖w‖ ^ 2 * eta ^ 2 := by
    rw [← Finset.mul_sum]
    calc (1 / (N:ℝ)) * ∑ j, ‖1 + w * d j‖ ^ 2
        ≤ (1 / (N:ℝ)) * ((N:ℝ) * (1 + ‖w‖ ^ 2 * eta ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 + ‖w‖ ^ 2 * eta ^ 2 := by field_simp
  have h1 : X ^ (1 / (N:ℝ) : ℝ) ≤ 1 + ‖w‖ ^ 2 * eta ^ 2 := by
    rw [← hlhs]
    exact le_trans hamgm hrhs
  have h2 : X ≤ (1 + ‖w‖ ^ 2 * eta ^ 2) ^ N := by
    have h3 : (X ^ (1 / (N:ℝ) : ℝ)) ^ N ≤ (1 + ‖w‖ ^ 2 * eta ^ 2) ^ N :=
      pow_le_pow_left₀ (Real.rpow_nonneg hX0 _) h1 N
    rwa [← Real.rpow_natCast (X ^ (1 / (N:ℝ) : ℝ)) N, ← Real.rpow_mul hX0,
      one_div, inv_mul_cancel₀ hNne, Real.rpow_one] at h3
  calc ‖∏ j, (1 + w * d j)‖ ^ 2 = ∏ j, ‖1 + w * d j‖ ^ 2 := by
        rw [Complex.norm_prod, ← Finset.prod_pow]
    _ ≤ (1 + ‖w‖ ^ 2 * eta ^ 2) ^ N := h2

/-- **The Cauchy coefficient estimate** `‖e_m(d)‖ ≤ c·η^m`, for any `c ≥ 0` whose
square dominates `N^N/(m^m (N-m)^{N-m})` — the exact-squaring form
`N^N ≤ c²·m^m·(N-m)^{N-m}` of eq. (cauchy-esp), optimized at `r² = m/((N-m)η²)`. -/
theorem esymm_le {m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ((N : ℝ)) ^ N ≤ c ^ 2 * (m : ℝ) ^ m * ((N - m : ℕ) : ℝ) ^ (N - m))
    (d : Fin N → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hz : ∑ j, d j = 0) (hD : ∑ j, ‖d j‖ ^ 2 ≤ (N : ℝ) * eta ^ 2) :
    ‖esD d m‖ ≤ c * eta ^ m := by
  rcases eq_or_lt_of_le heta with h0 | hpos
  · -- `η = 0`: all coordinates vanish, so does `e_m` (`m ≥ 1`)
    have hz0 : ∀ j, d j = 0 := by
      intro j
      have hle : ∑ k, ‖d k‖ ^ 2 ≤ 0 := by
        rw [← h0] at hD
        simpa using hD
      have hnn : ∀ k ∈ (univ : Finset (Fin N)), (0:ℝ) ≤ ‖d k‖ ^ 2 :=
        fun k _ => sq_nonneg _
      have heach := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp
        (le_antisymm hle (Finset.sum_nonneg hnn))
      have hj := heach j (mem_univ j)
      have hnj : ‖d j‖ = 0 := by nlinarith [norm_nonneg (d j)]
      exact norm_eq_zero.mp hnj
    have hesd : esD d m = 0 := by
      refine Finset.sum_eq_zero fun s hs => ?_
      have hcard : s.card = m := (Finset.mem_powersetCard.mp hs).2
      have hne : s.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨j, hj⟩ := hne
      exact Finset.prod_eq_zero hj (hz0 j)
    rw [hesd, norm_zero, ← h0, zero_pow (by omega : m ≠ 0), mul_zero]
  · -- `η > 0`: the optimized extraction bound
    have hNm : 0 < N - m := by omega
    have hKpos : (0:ℝ) < ((N - m : ℕ) : ℝ) := by exact_mod_cast hNm
    have hmpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    set rho : ℝ := (m : ℝ) / (((N - m : ℕ) : ℝ) * eta ^ 2) with hrho
    have hrho0 : 0 < rho := by
      rw [hrho]
      exact div_pos hmpos (mul_pos hKpos (by positivity))
    set r : ℝ := Real.sqrt rho with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr hrho0
    have hr2 : r ^ 2 = rho := Real.sq_sqrt hrho0.le
    -- the primitive root and the extraction at `z = r`
    obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ (N + 1) :=
      ⟨_, Complex.isPrimitiveRoot_exp (N + 1) (Nat.succ_ne_zero N)⟩
    have hζ0 : ζ ≠ 0 := by
      intro h
      have h1 := hζ.pow_eq_one
      rw [h, zero_pow (Nat.succ_ne_zero N)] at h1
      exact zero_ne_one h1
    have hζnorm : ‖ζ‖ = 1 := by
      have h1 : ‖ζ‖ ^ (N + 1) = 1 := by rw [← norm_pow, hζ.pow_eq_one, norm_one]
      rcases lt_trichotomy ‖ζ‖ 1 with hlt | heq | hgt
      · exact absurd h1 (by
          have := pow_lt_one₀ (norm_nonneg ζ) hlt (by omega : N + 1 ≠ 0)
          linarith)
      · exact heq
      · exact absurd h1 (by
          have := one_lt_pow₀ hgt (by omega : N + 1 ≠ 0)
          linarith)
    have hext := esymm_extract hζ hmN.le d ((r : ℝ) : ℂ)
    -- the norm of the left side
    have hnormeq : ((N:ℝ) + 1) * (‖esD d m‖ * r ^ m)
        = ‖∑ k ∈ range (N + 1), (ζ ^ (k * m))⁻¹ * ∏ j, (1 + (r:ℂ) * ζ ^ k * d j)‖ := by
      rw [← hext, norm_mul, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hr0.le]
      have hN1 : ‖((N:ℂ) + 1)‖ = (N:ℝ) + 1 := by
        rw [show ((N:ℂ) + 1) = ((N + 1 : ℕ) : ℂ) by push_cast; ring,
          Complex.norm_natCast]
        push_cast
        ring
      rw [hN1]
      ring
    -- each summand is bounded by `√((1+ρη²)^N)`
    have hbound : ∀ k ∈ range (N + 1),
        ‖(ζ ^ (k * m))⁻¹ * ∏ j, (1 + (r:ℂ) * ζ ^ k * d j)‖
          ≤ Real.sqrt ((1 + rho * eta ^ 2) ^ N) := by
      intro k _
      rw [norm_mul, norm_inv, norm_pow, hζnorm, one_pow, inv_one, one_mul]
      have hw2 : ‖(r:ℂ) * ζ ^ k‖ ^ 2 = rho := by
        rw [norm_mul, norm_pow, hζnorm, one_pow, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hr0.le, hr2]
      have hH := H_bound (by omega : 1 ≤ N) d eta ((r:ℂ) * ζ ^ k) hz hD
      rw [hw2] at hH
      have h4 := Real.sqrt_le_sqrt hH
      rwa [Real.sqrt_sq (norm_nonneg _)] at h4
    -- sum the bounds and cancel `N+1`
    have hsumle : ‖∑ k ∈ range (N + 1), (ζ ^ (k * m))⁻¹ * ∏ j, (1 + (r:ℂ) * ζ ^ k * d j)‖
        ≤ ((N:ℝ) + 1) * Real.sqrt ((1 + rho * eta ^ 2) ^ N) := by
      calc ‖∑ k ∈ range (N + 1), (ζ ^ (k * m))⁻¹ * ∏ j, (1 + (r:ℂ) * ζ ^ k * d j)‖
          ≤ ∑ k ∈ range (N + 1),
              ‖(ζ ^ (k * m))⁻¹ * ∏ j, (1 + (r:ℂ) * ζ ^ k * d j)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ range (N + 1), Real.sqrt ((1 + rho * eta ^ 2) ^ N) :=
            Finset.sum_le_sum hbound
        _ = ((N:ℝ) + 1) * Real.sqrt ((1 + rho * eta ^ 2) ^ N) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hVrM : ‖esD d m‖ * r ^ m ≤ Real.sqrt ((1 + rho * eta ^ 2) ^ N) := by
      have h1 : ((N:ℝ) + 1) * (‖esD d m‖ * r ^ m)
          ≤ ((N:ℝ) + 1) * Real.sqrt ((1 + rho * eta ^ 2) ^ N) := hnormeq ▸ hsumle
      exact le_of_mul_le_mul_left h1 (by positivity)
    -- square everything: `‖e_m‖²·ρ^m ≤ (1+ρη²)^N`
    have hmain : ‖esD d m‖ ^ 2 * rho ^ m ≤ (1 + rho * eta ^ 2) ^ N := by
      have h2 : (‖esD d m‖ * r ^ m) ^ 2 ≤ Real.sqrt ((1 + rho * eta ^ 2) ^ N) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hVrM 2
      rw [Real.sq_sqrt (by positivity)] at h2
      calc ‖esD d m‖ ^ 2 * rho ^ m = (‖esD d m‖ * r ^ m) ^ 2 := by
            rw [mul_pow, ← pow_mul, Nat.mul_comm m 2, pow_mul, hr2]
        _ ≤ (1 + rho * eta ^ 2) ^ N := h2
    -- the optimum: `1 + ρη² = N/(N-m)` and `ρ^m·(N-m)^m·(η²)^m = m^m`
    have hone : 1 + rho * eta ^ 2 = (N : ℝ) / ((N - m : ℕ) : ℝ) := by
      rw [hrho]
      field_simp
      push_cast [Nat.cast_sub hmN.le]
      ring
    have hrhoKm : rho ^ m * (((N - m : ℕ) : ℝ) ^ m * (eta ^ 2) ^ m) = (m : ℝ) ^ m := by
      rw [hrho, div_pow, mul_pow]
      field_simp
    -- the exact-squaring domination
    have hAK : ((N : ℝ) / ((N - m : ℕ) : ℝ)) ^ N * ((N - m : ℕ) : ℝ) ^ N
        = (N : ℝ) ^ N := by
      rw [div_pow]
      field_simp
    have hstep1 : ((N : ℝ) / ((N - m : ℕ) : ℝ)) ^ N * ((N - m : ℕ) : ℝ) ^ m
        * ((N - m : ℕ) : ℝ) ^ (N - m)
        ≤ c ^ 2 * (m : ℝ) ^ m * ((N - m : ℕ) : ℝ) ^ (N - m) := by
      calc ((N : ℝ) / ((N - m : ℕ) : ℝ)) ^ N * ((N - m : ℕ) : ℝ) ^ m
            * ((N - m : ℕ) : ℝ) ^ (N - m)
          = ((N : ℝ) / ((N - m : ℕ) : ℝ)) ^ N * ((N - m : ℕ) : ℝ) ^ N := by
            rw [mul_assoc, ← pow_add, show m + (N - m) = N by omega]
        _ = (N : ℝ) ^ N := hAK
        _ ≤ c ^ 2 * (m : ℝ) ^ m * ((N - m : ℕ) : ℝ) ^ (N - m) := hc
    have hstep2 : ((N : ℝ) / ((N - m : ℕ) : ℝ)) ^ N * ((N - m : ℕ) : ℝ) ^ m
        ≤ c ^ 2 * (m : ℝ) ^ m :=
      le_of_mul_le_mul_right hstep1 (by positivity)
    -- assemble: `‖e_m‖²·m^m ≤ c²·m^m·(η²)^m`
    have hVm : ‖esD d m‖ ^ 2 * (m : ℝ) ^ m
        ≤ c ^ 2 * (m : ℝ) ^ m * (eta ^ 2) ^ m := by
      calc ‖esD d m‖ ^ 2 * (m : ℝ) ^ m
          = ‖esD d m‖ ^ 2 * rho ^ m * (((N - m : ℕ) : ℝ) ^ m * (eta ^ 2) ^ m) := by
            rw [mul_assoc, hrhoKm]
        _ ≤ (1 + rho * eta ^ 2) ^ N * (((N - m : ℕ) : ℝ) ^ m * (eta ^ 2) ^ m) :=
            mul_le_mul_of_nonneg_right hmain (by positivity)
        _ = ((1 + rho * eta ^ 2) ^ N * ((N - m : ℕ) : ℝ) ^ m) * (eta ^ 2) ^ m := by
            ring
        _ = (((N : ℝ) / ((N - m : ℕ) : ℝ)) ^ N * ((N - m : ℕ) : ℝ) ^ m)
            * (eta ^ 2) ^ m := by rw [hone]
        _ ≤ (c ^ 2 * (m : ℝ) ^ m) * (eta ^ 2) ^ m :=
            mul_le_mul_of_nonneg_right hstep2 (by positivity)
        _ = c ^ 2 * (m : ℝ) ^ m * (eta ^ 2) ^ m := by ring
    have hV2 : ‖esD d m‖ ^ 2 ≤ c ^ 2 * (eta ^ 2) ^ m := by
      have h' : ‖esD d m‖ ^ 2 * (m : ℝ) ^ m ≤ (c ^ 2 * (eta ^ 2) ^ m) * (m : ℝ) ^ m := by
        calc ‖esD d m‖ ^ 2 * (m : ℝ) ^ m ≤ c ^ 2 * (m : ℝ) ^ m * (eta ^ 2) ^ m := hVm
          _ = (c ^ 2 * (eta ^ 2) ^ m) * (m : ℝ) ^ m := by ring
      exact le_of_mul_le_mul_right h' (by positivity)
    have hfin : ‖esD d m‖ ^ 2 ≤ (c * eta ^ m) ^ 2 := by
      calc ‖esD d m‖ ^ 2 ≤ c ^ 2 * (eta ^ 2) ^ m := hV2
        _ = (c * eta ^ m) ^ 2 := by
            rw [← pow_mul, Nat.mul_comm 2 m, pow_mul]
            ring
    have h5 := Real.sqrt_le_sqrt hfin
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h5

/-- **The degree-11 `c₄` entry, with the CAUCHY constant `1447/50`** (the Schoenberg
route `70/3` is deleted per the c4-experiment decision box): the whole content is
the exact squaring check `(1447/50)²·4⁴·6⁶ ≥ 10¹⁰`. -/
theorem c4_deg11 (D : Fin 10 → ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (hz : ∑ j, D j = 0) (hD : ∑ j, ‖D j‖ ^ 2 ≤ 10 * eta ^ 2) :
    ‖esD D 4‖ ≤ (1447/50 : ℝ) * eta ^ 4 := by
  refine esymm_le (by norm_num) (by norm_num) (by norm_num : (0:ℝ) ≤ 1447/50)
    (by norm_num) D eta heta hz ?_
  exact_mod_cast hD

end SendovN.EspCauchy

#print axioms SendovN.EspCauchy.prod_one_add_eq
#print axioms SendovN.EspCauchy.esymm_extract
#print axioms SendovN.EspCauchy.H_bound
#print axioms SendovN.EspCauchy.esymm_le
#print axioms SendovN.EspCauchy.c4_deg11
