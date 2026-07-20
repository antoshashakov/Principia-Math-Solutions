/-
ERDŐS #123 — THE INTERMEDIATE AND MINOR RANGES OF THE THREE-RANGE SPLIT
======================================================================
Companion of `Erdos123/GPrincipal.lean`.  Where the principal range produces a lower
bound `≥ 1/(5V)` for `∫₀^{t₁}`, this file shows that everything from `t₁` out to `1/2`
contributes at most `1/(10V)` in absolute value, UNIFORMLY IN `n`.

Split point `t₂ = 2δ/x`, where `δ` is the rigidity radius of `gvery_low_sharp`:

* INTERMEDIATE `[t₁, t₂]`: every band element satisfies `s < d·x` with
  `d = min a (min b c)`, and `δ·d ≤ 1/8`, so `s·t < 1/2` and `round (s t) = 0`.
  Hence `GQenergy x t = S₂ t²` exactly and `|χ| ≤ exp(−2 S₂ t²)`; the Gaussian tail
  `gauss_tail_Ioi` gives `exp(−2T²)/(2VT) = o(1/V)`.

* MINOR `[t₂, 1/2]`: every `t` there is at distance `> δ/x` from every integer, so the
  contrapositive of `gvery_low_sharp` gives the energy floor `GQenergy ≥ κ₀ log x`;
  the layer-split `gexp_integral_le_on` plus `glow_energy_measure` then give
  `≲ x^{−2κ₀} L^{C₄}/x + x^{−2} = o(1/(xL)) = o(1/V)`.

Main result: `gtail_upper`.
-/
import Erdos123.GPrincipal
import Erdos123.GBandAux
import Erdos123.GRigidity
import Erdos123.GGrid
import Erdos123.GaussFT
import Erdos123.GLowEnergy

set_option maxHeartbeats 1000000

open MeasureTheory

namespace Erdos123Band

noncomputable section

/-! ## Step 1 — a narrow sub-band

`gvery_low` only guarantees `δ ≤ 1/32`, which is not enough to force `s·t < 1/2` for the
band elements `s < d·x` when `d = min a (min b c)` is large.  We sharpen it below; the
tool is a sub-band of ratio `≤ 3/2`, whose elements are all `< 2x`. -/

/-- A ratio `p'/q' ≤ 3/2` that is at most `p/q`, so that `GBand a b c p' q' x` is a
sub-band of `GBand a b c p q x` all of whose elements are `< 2x`. -/
lemma gnarrow_ratio {a b c p q : ℕ} (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) (hd2 : 2 ≤ min a (min b c)) :
    ∃ p' q' : ℕ, 0 < q' ∧ q' < p' ∧ p' < q' * min a (min b c) ∧ 2 * p' ≤ 3 * q' ∧
      ∀ x : ℕ, GBand a b c p' q' x ⊆ GBand a b c p q x := by
  by_cases h : 2 * p ≤ 3 * q
  · exact ⟨p, q, hq, hqp, hpd, h, fun x => Finset.Subset.refl _⟩
  · push_neg at h
    refine ⟨3, 2, by norm_num, by norm_num, ?_, by norm_num, fun x s hs => ?_⟩
    · omega
    · obtain ⟨hS, hx, hw⟩ := of_mem_GBand hs
      refine (mem_GBand hq).mpr ⟨hS, hx, ?_⟩
      have hx0 : 0 < x := by omega
      have h1 : 2 * (q * s) < 3 * (q * x) := by
        calc 2 * (q * s) = q * (2 * s) := by ring
          _ < q * (3 * x) := mul_lt_mul_of_pos_left hw hq
          _ = 3 * (q * x) := by ring
      have h2 : 3 * (q * x) < 2 * (p * x) := by
        calc 3 * (q * x) = 3 * q * x := by ring
          _ < 2 * p * x := mul_lt_mul_of_pos_right h hx0
          _ = 2 * (p * x) := by ring
      omega

/-- Elements of a ratio-`≤ 3/2` band are `< 2x`. -/
lemma gband_lt_two_mul {a b c p' q' x s : ℕ} (hq' : 0 < q') (hnarrow : 2 * p' ≤ 3 * q')
    (hs : s ∈ GBand a b c p' q' x) : 2 * s < 3 * x := by
  obtain ⟨-, -, hw⟩ := of_mem_GBand hs
  have h1 : q' * (2 * s) < q' * (3 * x) := by
    calc q' * (2 * s) = 2 * (q' * s) := by ring
      _ < 2 * (p' * x) := by omega
      _ = 2 * p' * x := by ring
      _ ≤ 3 * q' * x := Nat.mul_le_mul_right x hnarrow
      _ = q' * (3 * x) := by ring
  exact lt_of_mul_lt_mul_left h1 (Nat.zero_le _)

/-- Every band element satisfies `s < d·x` with `d = min a (min b c)`. -/
lemma gband_lt_d_mul {a b c p q x s : ℕ} (hq : 0 < q) (hpd : p < q * min a (min b c))
    (hs : s ∈ GBand a b c p q x) : s < min a (min b c) * x := by
  obtain ⟨-, -, hw⟩ := of_mem_GBand hs
  have h1 : q * s < q * (min a (min b c) * x) := by
    calc q * s < p * x := hw
      _ ≤ q * min a (min b c) * x := Nat.mul_le_mul_right x (le_of_lt hpd)
      _ = q * (min a (min b c) * x) := by ring
  exact lt_of_mul_lt_mul_left h1 (Nat.zero_le _)

/-! ## Step 2 — the sharpened rigidity radius -/

/-- **Sharpened [very-low].**  Same as `gvery_low`, but the rigidity radius `δ` is made
small enough that `δ · min a (min b c) ≤ 1/8`.  This is what makes `round (s t) = 0`
available on the whole intermediate range.  Proved from `gvery_low` by bootstrapping
inside the narrow sub-band, whose cardinality is `≫ (log x)²` (`gband_card_ge_sq`). -/
theorem gvery_low_sharp (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ κ₀ δ : ℝ, ∃ X₅ : ℕ, 0 < κ₀ ∧ 0 < δ ∧
      δ * ((min a (min b c) : ℕ) : ℝ) ≤ 1 / 8 ∧ ∀ x : ℕ, X₅ ≤ x → ∀ t : ℝ,
        GQenergy a b c p q x t < κ₀ * Real.log x → ∃ r : ℤ, |t - (r : ℝ)| ≤ δ / (x : ℝ) := by
  classical
  have hd2 : 2 ≤ min a (min b c) := by simp only [le_min_iff]; omega
  obtain ⟨p', q', hq', hq'p', hp'd, hnarrow, hsub⟩ := gnarrow_ratio hq hqp hpd hd2
  obtain ⟨κ₀, δ₀, X₅, hκ₀, hδ₀, hδ₀32, hvl⟩ := gvery_low a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨c₁, hc₁, X₁, hcard⟩ := gband_card_ge_sq a b c p' q' ha hb hc hco hq' hq'p' hp'd
  set d : ℕ := min a (min b c) with hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  set δ : ℝ := min (1 / 32) (1 / (8 * (d : ℝ))) with hδdef
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδd : δ * (d : ℝ) ≤ 1 / 8 := by
    have h1 : δ ≤ 1 / (8 * (d : ℝ)) := min_le_right _ _
    have h2 : δ * (d : ℝ) ≤ (1 / (8 * (d : ℝ))) * (d : ℝ) :=
      mul_le_mul_of_nonneg_right h1 hdR.le
    calc δ * (d : ℝ) ≤ (1 / (8 * (d : ℝ))) * (d : ℝ) := h2
      _ = 1 / 8 := by field_simp
  -- eventually `log x` is large enough that the bootstrap closes
  have hlogtop : Filter.Tendsto (fun x : ℕ => Real.log x) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨X₃, hX₃⟩ := Filter.eventually_atTop.mp
    (hlogtop.eventually_ge_atTop (max (κ₀ / (c₁ * δ ^ 2)) 1))
  refine ⟨κ₀, δ, max (max X₅ X₁) (max X₃ 2), hκ₀, hδpos, hδd, fun x hx t hQ => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxX₅, hxX₁⟩, hxX₃, hx2⟩ := hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hLbig := hX₃ x hxX₃
  rw [max_le_iff] at hLbig
  obtain ⟨hLratio, hL1⟩ := hLbig
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  obtain ⟨r, hr⟩ := hvl x hxX₅ t hQ
  refine ⟨r, ?_⟩
  set u : ℝ := t - (r : ℝ) with hu
  -- the energy only sees `u`
  have hshift : ∀ s : ℕ, (s : ℝ) * t - (round ((s : ℝ) * t) : ℝ)
      = (s : ℝ) * u - (round ((s : ℝ) * u) : ℝ) := by
    intro s
    have he : (s : ℝ) * t = (s : ℝ) * u + ((s * r : ℤ) : ℝ) := by
      rw [hu]; push_cast; ring
    rw [he, round_add_intCast]
    push_cast; ring
  have hQu : GQenergy a b c p q x t
      = ∑ s ∈ GBand a b c p q x, ((s : ℝ) * u - (round ((s : ℝ) * u) : ℝ)) ^ 2 := by
    unfold GQenergy
    exact Finset.sum_congr rfl (fun s _ => by rw [hshift s])
  have hu32 : |u| ≤ (1 / 32) / (x : ℝ) := hr.trans (by gcongr)
  -- on the narrow sub-band the rounding vanishes
  have hkey : ∀ s ∈ GBand a b c p' q' x,
      ((s : ℝ) * u - (round ((s : ℝ) * u) : ℝ)) ^ 2 = ((s : ℝ) * u) ^ 2 := by
    intro s hs
    have h2s : 2 * s < 3 * x := gband_lt_two_mul hq' hnarrow hs
    have hsR : (s : ℝ) ≤ 2 * (x : ℝ) := by
      have : s ≤ 2 * x := by omega
      exact_mod_cast this
    have hsu : |(s : ℝ) * u| < 1 / 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s : ℝ))]
      have h1 : (s : ℝ) * |u| ≤ (2 * (x : ℝ)) * ((1 / 32) / (x : ℝ)) :=
        mul_le_mul hsR hu32 (abs_nonneg _) (by positivity)
      have h2 : (2 * (x : ℝ)) * ((1 / 32) / (x : ℝ)) = 1 / 16 := by field_simp; ring
      linarith [h1, h2.le, h2.ge]
    have hround : round ((s : ℝ) * u) = 0 := by
      rw [round_eq_zero_iff, Set.mem_Ico]
      constructor
      · linarith [neg_abs_le ((s : ℝ) * u)]
      · linarith [le_abs_self ((s : ℝ) * u)]
    rw [hround]
    push_cast; ring
  -- the bootstrap inequality
  have hbig : c₁ * Real.log x ^ 2 * ((x : ℝ) ^ 2 * u ^ 2) ≤ GQenergy a b c p q x t := by
    have hstep1 : ∑ s ∈ GBand a b c p' q' x,
          ((s : ℝ) * u - (round ((s : ℝ) * u) : ℝ)) ^ 2
        ≤ GQenergy a b c p q x t := by
      rw [hQu]
      exact Finset.sum_le_sum_of_subset_of_nonneg (hsub x) (fun s _ _ => sq_nonneg _)
    have hstep2 : ((GBand a b c p' q' x).card : ℝ) * ((x : ℝ) ^ 2 * u ^ 2)
        ≤ ∑ s ∈ GBand a b c p' q' x, ((s : ℝ) * u - (round ((s : ℝ) * u) : ℝ)) ^ 2 := by
      rw [Finset.sum_congr rfl hkey]
      calc ((GBand a b c p' q' x).card : ℝ) * ((x : ℝ) ^ 2 * u ^ 2)
          = ∑ _s ∈ GBand a b c p' q' x, ((x : ℝ) ^ 2 * u ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ s ∈ GBand a b c p' q' x, ((s : ℝ) * u) ^ 2 := by
            refine Finset.sum_le_sum (fun s hs => ?_)
            have hxs : (x : ℝ) ≤ (s : ℝ) := by exact_mod_cast (of_mem_GBand hs).2.1
            have hsq : (x : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 := by nlinarith [hxpos.le]
            nlinarith [sq_nonneg u]
    have hstep3 : c₁ * Real.log x ^ 2 * ((x : ℝ) ^ 2 * u ^ 2)
        ≤ ((GBand a b c p' q' x).card : ℝ) * ((x : ℝ) ^ 2 * u ^ 2) := by
      refine mul_le_mul_of_nonneg_right (hcard x hxX₁) (by positivity)
    linarith
  -- conclude
  have hu2 : u ^ 2 ≤ (δ / (x : ℝ)) ^ 2 := by
    have h1 : c₁ * Real.log x ^ 2 * ((x : ℝ) ^ 2 * u ^ 2) < κ₀ * Real.log x := by linarith
    have h2 : κ₀ ≤ c₁ * δ ^ 2 * Real.log x := by
      rw [div_le_iff₀ (by positivity)] at hLratio
      linarith
    have h3 : c₁ * Real.log x ^ 2 * ((x : ℝ) ^ 2 * u ^ 2)
        < c₁ * δ ^ 2 * Real.log x * Real.log x := by nlinarith
    have h4 : (x : ℝ) ^ 2 * u ^ 2 ≤ δ ^ 2 := by
      nlinarith [hLpos, hc₁, mul_pos hc₁ (pow_pos hLpos 2)]
    rw [div_pow]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rcases abs_cases u with ⟨he, hnn⟩ | ⟨he, hnn⟩
  · rw [he]; nlinarith [hu2, div_pos hδpos hxpos]
  · rw [he]; nlinarith [hu2, div_pos hδpos hxpos]

/-! ## Step 3 — the layer split of `∫ exp(−2Q)` over an arbitrary subset of `(0,1]`

Verbatim port of `gminor_exp_integral_le` (`Erdos123.GBand`) from `GMinorArc p q x` to an
arbitrary measurable `S ⊆ Ioc 0 1`; we need it on `S = Ioc t₂ (1/2)`, whose width has
nothing to do with the `q/(8px)` of `GMinorArc`. -/

lemma gexp_integral_le_on (a b c p q x : ℕ) {κ₀ Mbound : ℝ} {S : Set ℝ}
    (hSm : MeasurableSet S) (hSsub : S ⊆ Set.Ioc (0 : ℝ) 1)
    (hfloor : ∀ t ∈ S, κ₀ * Real.log x ≤ GQenergy a b c p q x t)
    (hmeas : (volume {t : ℝ | t ∈ S ∧ GQenergy a b c p q x t ≤ Real.log x}).toReal ≤ Mbound) :
    (∫ t in S, Real.exp (-(2 * GQenergy a b c p q x t)))
      ≤ Real.exp (-(2 * κ₀ * Real.log x)) * Mbound + Real.exp (-(2 * Real.log x)) := by
  have hmeasQ : MeasurableSet {t : ℝ | GQenergy a b c p q x t ≤ Real.log x} :=
    measurableSet_le (GQenergy_measurable a b c p q x) measurable_const
  have hInt : IntegrableOn (fun t => Real.exp (-(2 * GQenergy a b c p q x t))) S volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (gexp_neg_two_Q_intervalIntegrable a b c p q x 0 1))).mono_set hSsub
  have hvolIoc : volume (Set.Ioc (0 : ℝ) 1) < ⊤ := by rw [Real.volume_Ioc]; simp
  have hfin : ∀ U : Set ℝ, U ⊆ S → volume U < ⊤ := fun U hU =>
    lt_of_le_of_lt (measure_mono (hU.trans hSsub)) hvolIoc
  rw [← MeasureTheory.integral_inter_add_sdiff hmeasQ hInt]
  refine add_le_add ?_ ?_
  · have hsetle : (∫ t in S ∩ {t | GQenergy a b c p q x t ≤ Real.log x},
          Real.exp (-(2 * GQenergy a b c p q x t)))
        ≤ ∫ _t in S ∩ {t | GQenergy a b c p q x t ≤ Real.log x},
            Real.exp (-(2 * κ₀ * Real.log x)) := by
      refine MeasureTheory.setIntegral_mono_on (hInt.mono_set Set.inter_subset_left)
        (MeasureTheory.integrableOn_const (hfin _ Set.inter_subset_left).ne)
        (hSm.inter hmeasQ) (fun t ht => ?_)
      exact Real.exp_le_exp.mpr (by linarith [hfloor t ht.1])
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hsetle
    refine hsetle.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    rw [show S ∩ {t | GQenergy a b c p q x t ≤ Real.log x}
        = {t : ℝ | t ∈ S ∧ GQenergy a b c p q x t ≤ Real.log x} from by
      ext t; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]]
    exact hmeas
  · have hsetle : (∫ t in S \ {t | GQenergy a b c p q x t ≤ Real.log x},
          Real.exp (-(2 * GQenergy a b c p q x t)))
        ≤ ∫ _t in S \ {t | GQenergy a b c p q x t ≤ Real.log x},
            Real.exp (-(2 * Real.log x)) := by
      refine MeasureTheory.setIntegral_mono_on (hInt.mono_set Set.diff_subset)
        (MeasureTheory.integrableOn_const (hfin _ Set.diff_subset).ne)
        (hSm.diff hmeasQ) (fun t ht => ?_)
      have hQ : Real.log x < GQenergy a b c p q x t := by
        have h2 := ht.2; simp only [Set.mem_setOf_eq, not_le] at h2; exact h2
      exact Real.exp_le_exp.mpr (by linarith)
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hsetle
    refine hsetle.trans ?_
    rw [mul_comm]
    refine (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)).trans (le_of_eq (mul_one _))
    calc (volume (S \ {t | GQenergy a b c p q x t ≤ Real.log x})).toReal
        ≤ (volume (Set.Ioc (0 : ℝ) 1)).toReal :=
          ENNReal.toReal_mono hvolIoc.ne (measure_mono (Set.diff_subset.trans hSsub))
      _ = 1 := by rw [Real.volume_Ioc]; simp

/-! ## Step 4 — the energy is exactly `S₂ t²` on the intermediate range -/

/-- If `d·x·t ≤ 1/4` (`d = min a (min b c)`) and `t ≥ 0`, then every `s ∈ GBand` has
`round (s t) = 0`, so `GQenergy x t = S₂ t²`. -/
lemma gQenergy_eq_of_small {a b c p q x : ℕ} (hq : 0 < q) (hpd : p < q * min a (min b c))
    {t : ℝ} (ht0 : 0 ≤ t) (hsmall : ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) * t ≤ 1 / 4) :
    GQenergy a b c p q x t = (GS2 a b c p q x : ℝ) * t ^ 2 := by
  rw [GQenergy, ← gsum_sq_band a b c p q x t]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have hslt : (s : ℝ) ≤ ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) := by
    have := gband_lt_d_mul hq hpd hs
    have h2 : (s : ℝ) ≤ ((min a (min b c) * x : ℕ) : ℝ) := by exact_mod_cast this.le
    rwa [Nat.cast_mul] at h2
  have hst : 0 ≤ (s : ℝ) * t := mul_nonneg (by positivity) ht0
  have hst2 : (s : ℝ) * t ≤ 1 / 4 := by
    refine le_trans (mul_le_mul_of_nonneg_right hslt ht0) ?_
    linarith [hsmall]
  have hround : round ((s : ℝ) * t) = 0 := by
    rw [round_eq_zero_iff, Set.mem_Ico]
    constructor <;> linarith
  rw [hround]
  push_cast; ring

/-! ## Step 5 — the two ranges, as named lemmas

Both are stated for a FIXED `x` and for an ARBITRARY continuous integrand `F` dominated by the
Gaussian majorant `exp(−2Q)`.  Uniformity in `n` is therefore structural: the Fourier integrand
`(∏ cos π s t)·cos(π(S₁−2n)t)` satisfies the domination hypothesis with a bound independent of
`n` (`gintegrand_abs_le`).  Every asymptotic side condition is passed in as a hypothesis; all
the "for large `x`" bookkeeping lives in `gtail_upper` below. -/

/-- The Fourier integrand is dominated by the Gaussian majorant `exp(−2Q)`, uniformly in `n`
(the oscillating factor has modulus `≤ 1`). -/
lemma gintegrand_abs_le (a b c p q x n : ℕ) (t : ℝ) :
    |(∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
        * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))|
      ≤ Real.exp (-(2 * GQenergy a b c p q x t)) := by
  refine le_trans ?_ (gchi_le_exp_neg_two_Q a b c p q x t)
  rw [GchiBand, ← Finset.abs_prod, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- The Fourier integrand is continuous. -/
lemma gintegrand_continuous (a b c p q x n : ℕ) :
    Continuous (fun t : ℝ => (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
      * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))) := by
  fun_prop

/-- **INTERMEDIATE RANGE `[t₁, 2δ/x]`.**  There every band element has `s·t ≤ 1/4`, so
`round (s t) = 0`, the energy is exactly `S₂t²`, and the Gaussian tail beyond `t₁ = T/V`
is `exp(−2T²)/(2VT) ≤ 1/(20V)` once `T ≥ 2`. -/
lemma gintermediate_upper (a b c p q : ℕ) (hq : 0 < q) (hpd : p < q * min a (min b c))
    {δ : ℝ} (hδ : 0 < δ) (hδd : δ * ((min a (min b c) : ℕ) : ℝ) ≤ 1 / 8)
    (x : ℕ) (hx : 0 < x) {F : ℝ → ℝ} (hFcont : Continuous F)
    (hFabs : ∀ t : ℝ, |F t| ≤ Real.exp (-(2 * GQenergy a b c p q x t)))
    (hVpos : 0 < Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ))
    (hT2 : (2 : ℝ) ≤ gT x)
    (h12 : gt₁ a b c p q x ≤ 2 * δ / (x : ℝ)) :
    |∫ t in (gt₁ a b c p q x)..(2 * δ / (x : ℝ)), F t|
      ≤ 1 / (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ)) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  set V : ℝ := Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) with hVdef
  have hVne : V ≠ 0 := ne_of_gt hVpos
  have hV2 : V ^ 2 = ((GS2 a b c p q x : ℕ) : ℝ) := by
    rw [hVdef]; exact Real.sq_sqrt (by positivity)
  set T : ℝ := gT x with hTdef
  have hTpos : (0 : ℝ) < T := by linarith
  set t₁ : ℝ := gt₁ a b c p q x with ht₁def
  have ht₁eq : t₁ = T / V := by rw [ht₁def, hTdef, hVdef, gt₁]
  have ht₁pos : 0 < t₁ := by rw [ht₁eq]; positivity
  set t₂ : ℝ := 2 * δ / (x : ℝ) with ht₂def
  have hFabsInt : ∀ u v : ℝ, IntervalIntegrable (fun t => |F t|) volume u v :=
    fun u v => (hFcont.abs).intervalIntegrable u v
  set A : ℝ := 2 * ((GS2 a b c p q x : ℕ) : ℝ) with hAdef
  have hApos : 0 < A := by rw [hAdef]; nlinarith [hV2, hVpos]
  have hgi : MeasureTheory.Integrable (fun u : ℝ => Real.exp (-(A * u ^ 2))) := by
    have := gaussian_integrable_scaled hApos 0
    simpa using this
  have hstep1 : |∫ t in t₁..t₂, F t| ≤ ∫ t in t₁..t₂, |F t| := by
    have := intervalIntegral.norm_integral_le_integral_norm (f := F) (μ := volume) h12
    simpa only [Real.norm_eq_abs] using this
  have hstep2 : (∫ t in t₁..t₂, |F t|) ≤ ∫ t in t₁..t₂, Real.exp (-(A * t ^ 2)) := by
    refine intervalIntegral.integral_mono_on h12 (hFabsInt t₁ t₂)
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(A * t ^ 2))).intervalIntegrable _ _)
      (fun t ht => ?_)
    have htpos : 0 ≤ t := le_trans ht₁pos.le ht.1
    have hQ : GQenergy a b c p q x t = ((GS2 a b c p q x : ℕ) : ℝ) * t ^ 2 := by
      refine gQenergy_eq_of_small hq hpd htpos ?_
      have hdx0 : (0 : ℝ) ≤ ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) := by positivity
      have h1 : ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) * t
          ≤ ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) * t₂ := by nlinarith [ht.2]
      have h2 : ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) * t₂
          = ((min a (min b c) : ℕ) : ℝ) * (2 * δ) := by
        rw [ht₂def]; field_simp
      nlinarith [h1, h2, hδd]
    calc |F t| ≤ Real.exp (-(2 * GQenergy a b c p q x t)) := hFabs t
      _ = Real.exp (-(A * t ^ 2)) := by rw [hQ, hAdef]; congr 1; ring
  have hstep3 : (∫ t in t₁..t₂, Real.exp (-(A * t ^ 2)))
      ≤ ∫ t in Set.Ioi t₁, Real.exp (-(A * t ^ 2)) := by
    rw [intervalIntegral.integral_of_le h12]
    refine MeasureTheory.setIntegral_mono_set hgi.integrableOn ?_
      (HasSubset.Subset.eventuallyLE Set.Ioc_subset_Ioi_self)
    filter_upwards with t using Real.exp_nonneg _
  have hstep4 := gauss_tail_Ioi hApos ht₁pos
  have hAt1 : A * t₁ ^ 2 = 2 * T ^ 2 := by rw [hAdef, ht₁eq, ← hV2]; field_simp
  have hAt1' : A * t₁ = 2 * V * T := by rw [hAdef, ht₁eq, ← hV2]; field_simp
  have hfin : Real.exp (-(A * t₁ ^ 2)) / (A * t₁) ≤ 1 / (20 * V) := by
    rw [hAt1, hAt1']
    have h1 : 2 * T ^ 2 ≤ Real.exp (2 * T ^ 2) := by
      linarith [Real.add_one_le_exp (2 * T ^ 2)]
    have h2 : (2 * T ^ 2) * Real.exp (-(2 * T ^ 2)) ≤ 1 := by
      have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg (-(2 * T ^ 2)))
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h3
    have hT3 : (8 : ℝ) ≤ T ^ 3 := by
      nlinarith [hT2, hTpos, sq_nonneg (T - 2), sq_nonneg T]
    have h5 : 10 * Real.exp (-(2 * T ^ 2)) ≤ T := by
      have hT2pos : (0 : ℝ) < 2 * T ^ 2 := by positivity
      rw [← sub_nonneg]
      have h6 : T - 10 * Real.exp (-(2 * T ^ 2))
          = (T * (2 * T ^ 2) - 10 * ((2 * T ^ 2) * Real.exp (-(2 * T ^ 2)))) / (2 * T ^ 2) := by
        field_simp
      rw [h6]
      refine div_nonneg ?_ hT2pos.le
      nlinarith [h2, hT3]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ 2 * V by linarith)]
  linarith [hstep1, hstep2, hstep3, hstep4, hfin]

/-- **MINOR RANGE `[2δ/x, 1/2]`.**  Every such `t` is at distance `> δ/x` from every integer,
so the contrapositive of the rigidity input `hvl` gives the energy floor `Q ≥ κ₀ log x`; the
layer split `gexp_integral_le_on` against the low-energy measure `hmeasx` then finishes. -/
lemma gminor_upper (a b c p q : ℕ) {κ₀ δ : ℝ} {C₄ : ℕ} (x : ℕ) (hx1 : 1 ≤ x)
    (hδ : 0 < δ) (hδ16 : δ ≤ 1 / 16) (hL1 : (1 : ℝ) ≤ Real.log x)
    {F : ℝ → ℝ} (hFcont : Continuous F)
    (hFabs : ∀ t : ℝ, |F t| ≤ Real.exp (-(2 * GQenergy a b c p q x t)))
    (hvl : ∀ t : ℝ, GQenergy a b c p q x t < κ₀ * Real.log x →
      ∃ r : ℤ, |t - (r : ℝ)| ≤ δ / (x : ℝ))
    (hmeasx : volume {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ Real.log x}
      ≤ ENNReal.ofReal (1 / (x : ℝ) * Real.log x ^ C₄))
    (hnum : Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
        + Real.exp (-(2 * Real.log x)) ≤ 1 / (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ))) :
    |∫ t in (2 * δ / (x : ℝ))..(1 / 2), F t|
      ≤ 1 / (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ)) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  set t₂ : ℝ := 2 * δ / (x : ℝ) with ht₂def
  have ht₂pos : 0 < t₂ := by rw [ht₂def]; positivity
  have ht₂half : t₂ ≤ 1 / 2 := by
    rw [ht₂def, div_le_iff₀ hxpos]; nlinarith [hδ16, hx1R]
  have hstep1 : |∫ t in t₂..(1 / 2), F t| ≤ ∫ t in t₂..(1 / 2), |F t| := by
    have := intervalIntegral.norm_integral_le_integral_norm (f := F) (μ := volume) ht₂half
    simpa only [Real.norm_eq_abs] using this
  have hstep2 : (∫ t in t₂..(1 / 2), |F t|)
      ≤ ∫ t in t₂..(1 / 2), Real.exp (-(2 * GQenergy a b c p q x t)) :=
    intervalIntegral.integral_mono_on ht₂half ((hFcont.abs).intervalIntegrable _ _)
      (gexp_neg_two_Q_intervalIntegrable a b c p q x t₂ (1 / 2)) (fun t _ => hFabs t)
  have hdx : δ / (x : ℝ) ≤ 1 / 16 := by
    rw [div_le_iff₀ hxpos]; nlinarith [hδ16, hx1R]
  have hfloor : ∀ t ∈ Set.Ioc t₂ (1 / 2 : ℝ), κ₀ * Real.log x ≤ GQenergy a b c p q x t := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, hr⟩ := hvl t hcon
    have htpos : 0 < t := lt_trans ht₂pos ht.1
    have hhalf : δ / (x : ℝ) < t₂ := by
      have heq : t₂ - δ / (x : ℝ) = δ / (x : ℝ) := by rw [ht₂def]; field_simp; norm_num
      have hpos : 0 < δ / (x : ℝ) := div_pos hδ hxpos
      linarith
    have hcontr : δ / (x : ℝ) < |t - (r : ℝ)| := by
      rcases le_or_gt 1 r with h | h
      · have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.2, hdx]
      · rcases le_or_gt r (-1) with h' | h'
        · have hrR : ((r : ℤ) : ℝ) ≤ -1 := by exact_mod_cast h'
          rw [abs_of_nonneg (by linarith)]
          linarith [hdx]
        · have hr0 : r = 0 := by omega
          subst hr0
          rw [Int.cast_zero, sub_zero, abs_of_pos htpos]
          linarith [ht.1, hhalf]
    linarith [hr, hcontr]
  have hSsub : Set.Ioc t₂ (1 / 2 : ℝ) ⊆ Set.Ioc (0 : ℝ) 1 :=
    fun t ht => ⟨lt_trans ht₂pos ht.1, by linarith [ht.2]⟩
  have hmeasS : (volume {t : ℝ | t ∈ Set.Ioc t₂ (1 / 2 : ℝ) ∧
      GQenergy a b c p q x t ≤ Real.log x}).toReal ≤ 1 / (x : ℝ) * Real.log x ^ C₄ := by
    have hsub : {t : ℝ | t ∈ Set.Ioc t₂ (1 / 2 : ℝ) ∧ GQenergy a b c p q x t ≤ Real.log x}
        ⊆ {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ Real.log x} := by
      rintro t ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith [ht₂pos], by linarith⟩, h3⟩
    have hle := (measure_mono hsub).trans hmeasx
    have hnn : (0 : ℝ) ≤ 1 / (x : ℝ) * Real.log x ^ C₄ :=
      mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq (ENNReal.toReal_ofReal hnn)
  have hmain := gexp_integral_le_on a b c p q x measurableSet_Ioc hSsub hfloor hmeasS
  rw [← intervalIntegral.integral_of_le ht₂half] at hmain
  linarith [hstep1, hstep2, hmain, hnum]

/-! ## Step 6 — assembly: `gtail_upper` -/


/-- **The intermediate + minor ranges contribute at most `1/(10V)`, uniformly in `n`.** -/
theorem gtail_upper (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      |∫ t in (gt₁ a b c p q x)..(1 / 2),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))|
        ≤ 1 / (10 * Real.sqrt (GS2 a b c p q x)) := by
  classical
  obtain ⟨κ₀, δ, X₅, hκ₀, hδ, hδd, hvl⟩ := gvery_low_sharp a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨C₄, hC₄, X₂, hmeasx⟩ := glow_energy_measure a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨CV, hCV, X₆, hVup⟩ := gV_upper a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨cV, hcV, X₇, hVlow⟩ := gV_lower a b c p q ha hb hc hco hq hqp hpd
  have hd2 : 2 ≤ min a (min b c) := by simp only [le_min_iff]; omega
  have hdR2 : (2 : ℝ) ≤ ((min a (min b c) : ℕ) : ℝ) := by exact_mod_cast hd2
  have hδ16 : δ ≤ 1 / 16 := by nlinarith [hδd, hdR2, hδ]
  -- the two growth conditions
  have hlogtop : Filter.Tendsto (fun x : ℕ => Real.log x) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Xa, hXa⟩ := Filter.eventually_atTop.mp
    (hlogtop.eventually_ge_atTop (max 16 ((1 / (2 * δ * cV)) ^ 2)))
  have hgrow : Filter.Tendsto
      (fun y : ℝ => 20 * CV * Real.log y ^ ((1 : ℝ) + (C₄ : ℝ)) * y ^ (-(2 * κ₀))
        + 20 * CV * Real.log y * y ^ (-(1 : ℝ))) Filter.atTop (nhds 0) := by
    have h1 := poly_log_rpow_tendsto (p := (1 : ℝ) + (C₄ : ℝ)) (q := 2 * κ₀) (by linarith)
    have h2 := poly_log_rpow_tendsto (p := (1 : ℝ)) (q := (1 : ℝ)) (by norm_num)
    have hsum := (h1.const_mul (20 * CV)).add (h2.const_mul (20 * CV))
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr (fun y => ?_)
    rw [Real.rpow_one]
    ring
  obtain ⟨Xb, hXb⟩ := Filter.eventually_atTop.mp
    ((hgrow.comp tendsto_natCast_atTop_atTop).eventually_lt_const (show (0 : ℝ) < 1 by norm_num))
  refine ⟨max (max (max X₅ X₂) (max X₆ X₇)) (max (max Xa Xb) 2), fun x hx n => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hxX₅, hxX₂⟩, hxX₆, hxX₇⟩, ⟨hxXa, hxXb⟩, hx2⟩ := hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hLbig := hXa x hxXa
  rw [max_le_iff] at hLbig
  obtain ⟨hL16, hLB⟩ := hLbig
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  -- `V = √S₂` and its two-sided bounds
  have hVge : cV * (x : ℝ) * Real.log x ≤ Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) :=
    hVlow x hxX₇
  have hVpos : 0 < Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) :=
    lt_of_lt_of_le (mul_pos (mul_pos hcV hxpos) hLpos) hVge
  have hVle : Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) ≤ CV * (x : ℝ) * Real.log x :=
    hVup x hxX₆
  have h20V : (0 : ℝ) < 20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) := by linarith
  -- `T = (log x)^{1/4} ≥ 2` and `T ≤ √(log x)`
  have hsq16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsq4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsL4 : (4 : ℝ) ≤ Real.sqrt (Real.log x) := by
    have h := Real.sqrt_le_sqrt hL16; rwa [hsq16] at h
  have hT2 : (2 : ℝ) ≤ gT x := by
    unfold gT
    have h := Real.sqrt_le_sqrt hsL4; rwa [hsq4] at h
  have hTle : gT x ≤ Real.sqrt (Real.log x) := by
    unfold gT
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg (Real.log x)),
      Real.sqrt_nonneg (Real.sqrt (Real.log x)), hsL4,
      sq_nonneg (Real.sqrt (Real.sqrt (Real.log x)) - 2)]
  -- `t₁ ≤ t₂ = 2δ/x`
  have h12 : gt₁ a b c p q x ≤ 2 * δ / (x : ℝ) := by
    have hp : (0 : ℝ) < 2 * δ * cV := by positivity
    have hkey : 1 / (2 * δ * cV) ≤ Real.sqrt (Real.log x) := by
      have h := Real.sqrt_le_sqrt hLB
      rwa [Real.sqrt_sq (by positivity)] at h
    have h3 : 1 ≤ 2 * δ * cV * Real.sqrt (Real.log x) := by
      rw [div_le_iff₀ hp] at hkey; linarith
    have hself : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
      Real.mul_self_sqrt hLpos.le
    have h4 : Real.sqrt (Real.log x) ≤ 2 * δ * cV * Real.log x := by
      nlinarith [h3, Real.sqrt_nonneg (Real.log x), hself]
    unfold gt₁
    rw [div_le_div_iff₀ hVpos hxpos]
    nlinarith [mul_le_mul_of_nonneg_right (hTle.trans h4) hxpos.le,
      mul_le_mul_of_nonneg_left hVge (show (0 : ℝ) ≤ 2 * δ by linarith)]
  -- the numeric input of the minor range
  have hnum : Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
      + Real.exp (-(2 * Real.log x))
      ≤ 1 / (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ)) := by
    have hEnn : (0 : ℝ) ≤ Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
        + Real.exp (-(2 * Real.log x)) :=
      add_nonneg (mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))) (Real.exp_nonneg _)
    have hc1 : Real.exp (-(2 * κ₀ * Real.log x)) = (x : ℝ) ^ (-(2 * κ₀)) := by
      rw [Real.rpow_def_of_pos hxpos]; ring_nf
    have hc3 : Real.exp (-(2 * Real.log x)) = (x : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_def_of_pos hxpos]; ring_nf
    have hLpow : Real.log (x : ℝ) ^ ((1 : ℝ) + (C₄ : ℝ))
        = Real.log (x : ℝ) ^ C₄ * Real.log x := by
      rw [show ((1 : ℝ) + (C₄ : ℝ)) = ((C₄ + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, pow_succ]
    have hkey := hXb x hxXb
    simp only [Function.comp_apply] at hkey
    rw [le_div_iff₀ h20V]
    have heq : (Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
          + Real.exp (-(2 * Real.log x))) * (20 * CV * (x : ℝ) * Real.log x)
        = 20 * CV * Real.log (x : ℝ) ^ ((1 : ℝ) + (C₄ : ℝ)) * (x : ℝ) ^ (-(2 * κ₀))
          + 20 * CV * Real.log (x : ℝ) * (x : ℝ) ^ (-(1 : ℝ)) := by
      rw [hc1, hc3, hLpow,
        show (-(1 : ℝ)) = -(2 : ℝ) + 1 by ring, Real.rpow_add hxpos, Real.rpow_one]
      field_simp
    have hmono : (Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
          + Real.exp (-(2 * Real.log x))) * (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ))
        ≤ (Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
          + Real.exp (-(2 * Real.log x))) * (20 * CV * (x : ℝ) * Real.log x) := by
      refine mul_le_mul_of_nonneg_left ?_ hEnn
      linarith
    rw [heq] at hmono
    linarith [hmono, hkey]
  -- the two ranges
  have hA := gintermediate_upper a b c p q hq hpd hδ hδd x (by omega)
    (gintegrand_continuous a b c p q x n) (gintegrand_abs_le a b c p q x n) hVpos hT2 h12
  have hB := gminor_upper a b c p q x (by omega) hδ hδ16 hL1
    (gintegrand_continuous a b c p q x n) (gintegrand_abs_le a b c p q x n)
    (hvl x hxX₅) (hmeasx x hxX₂) hnum
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((gintegrand_continuous a b c p q x n).intervalIntegrable (μ := volume)
      (gt₁ a b c p q x) (2 * δ / (x : ℝ)))
    ((gintegrand_continuous a b c p q x n).intervalIntegrable (μ := volume) (2 * δ / (x : ℝ)) (1 / 2))
  rw [← hsplit]
  refine le_trans (abs_add_le _ _) ?_
  have hSne : Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) ≠ 0 := ne_of_gt hVpos
  have hsum : 1 / (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ))
      + 1 / (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ))
      = 1 / (10 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ)) := by
    field_simp
    ring
  linarith [hA, hB, hsum]

/-! ## Interface certification

Restatement of the FROZEN `gtail_upper` type, verbatim from the spec, discharged by
`@gtail_upper`.  If this `example` elaborates, no hypothesis was added, no quantifier was
narrowed, and no parameter was specialized. -/
example : ∀ (a b c p q : ℕ), 1 < a → 1 < b → 1 < c →
    PairwiseCoprime3 a b c → 0 < q → q < p →
    p < q * min a (min b c) →
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      |∫ t in (gt₁ a b c p q x)..(1 / 2),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))|
        ≤ 1 / (10 * Real.sqrt (GS2 a b c p q x)) := @gtail_upper

end

#print axioms Erdos123Band.gtail_upper
#print axioms Erdos123Band.gvery_low_sharp

end Erdos123Band
