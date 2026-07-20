/-
Major-arc lower bound — replacement of the `major_arc_lower` axiom (sharpened window).
-/
import Erdos123.Slab

set_option maxHeartbeats 1000000

namespace Erdos123Band

open Real MeasureTheory

/-- `e` of an integer is `1`. -/
lemma e_int (k : ℤ) : e (k : ℝ) = 1 := by
  rw [e, show (2 * (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ))
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- Conjugation reflects the character: `conj (e x) = e (-x)`. -/
lemma e_conj (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  rw [e, e, ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_mul]
  simp only [Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring

/-- Gaussian lower bound for cosine near `0`: `exp (−y²) ≤ cos y` for `y² ≤ 1`. -/
lemma cos_ge_exp_neg_sq (y : ℝ) (hy : y ^ 2 ≤ 1) : Real.exp (-(y ^ 2)) ≤ Real.cos y := by
  have h1 : y ^ 2 + 1 ≤ Real.exp (y ^ 2) := Real.add_one_le_exp _
  have h3 : (0 : ℝ) < Real.exp (y ^ 2) := Real.exp_pos _
  have h4 : Real.exp (-(y ^ 2)) ≤ 1 / (1 + y ^ 2) := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ h3 (by positivity)]
    linarith
  have h5 : 1 / (1 + y ^ 2) ≤ 1 - y ^ 2 / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + y ^ 2)]
    nlinarith [sq_nonneg y, sq_nonneg (y ^ 2), sq_nonneg (1 - y ^ 2)]
  have h6 : 1 - y ^ 2 / 2 ≤ Real.cos y := Real.one_sub_sq_div_two_le_cos
  linarith

/-- `round y = 0` on `[0, 1/2)`. -/
lemma round_eq_zero_of' {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1 / 2) : round y = 0 := by
  rw [round_eq, Int.floor_eq_zero_iff]
  simp only [Set.mem_Ico]
  constructor <;> linarith

/-- Reflection symmetry of the subset-sum integrand: `f (1−u) = conj (f u)`. -/
lemma integrand_reflect (a b c x n : ℕ) (u : ℝ) :
    (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * (1 - u)))) * e (-((n : ℝ) * (1 - u)))
      = (starRingEnd ℂ)
          ((∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * u))) * e (-((n : ℝ) * u))) := by
  rw [map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl (fun s _ => ?_)
    rw [map_add, map_one, e_conj]
    congr 1
    rw [show (s : ℝ) * (1 - u) = ((s : ℤ) : ℝ) + -((s : ℝ) * u) by push_cast; ring,
      e_add, e_int, one_mul]
  · rw [e_conj]
    rw [show -((n : ℝ) * (1 - u)) = ((-(n : ℤ) : ℤ) : ℝ) + (n : ℝ) * u by push_cast; ring,
      e_add, e_int, one_mul, neg_neg]

/-- Real-part symmetry: the major-arc integrand's real part is symmetric about `t = 1/2`. -/
lemma integrand_re_reflect (a b c x n : ℕ) (u : ℝ) :
    ((∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * (1 - u)))) * e (-((n : ℝ) * (1 - u)))).re
      = ((∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * u))) * e (-((n : ℝ) * u))).re := by
  rw [integrand_reflect, Complex.conj_re]

/-- The major arc is the disjoint union of a head interval and its mirror. -/
lemma majorArc_eq_union (x : ℕ) (hx : 1 ≤ x) :
    MajorArc x
      = Set.Ioc (0 : ℝ) (1 / (8 * (x : ℝ))) ∪ Set.Icc (1 - 1 / (8 * (x : ℝ))) 1 := by
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hw0 : (0 : ℝ) < 1 / (8 * (x : ℝ)) := by positivity
  have hw8 : 1 / (8 * (x : ℝ)) ≤ 1 / 8 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  ext t
  simp only [MajorArc, Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_union, Set.mem_Icc]
  constructor
  · rintro ⟨⟨ht0, ht1⟩, h | h⟩
    · exact Or.inl ⟨ht0, h⟩
    · exact Or.inr ⟨h, ht1⟩
  · rintro (⟨ht0, htw⟩ | ⟨htw, ht1⟩)
    · exact ⟨⟨ht0, by linarith⟩, Or.inl htw⟩
    · exact ⟨⟨by linarith, ht1⟩, Or.inr htw⟩

/-- Folding a symmetric integrand over the major arc: twice the head integral. -/
lemma setIntegral_majorArc_twice (x : ℕ) (hx : 1 ≤ x) (h : ℝ → ℝ) (hcont : Continuous h)
    (hsymm : ∀ u, h (1 - u) = h u) :
    ∫ t in MajorArc x, h t = 2 * ∫ t in Set.Ioc (0 : ℝ) (1 / (8 * (x : ℝ))), h t := by
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  set w : ℝ := 1 / (8 * (x : ℝ)) with hw
  have hw0 : 0 < w := by rw [hw]; positivity
  have hw8 : w ≤ 1 / 8 := by
    rw [hw]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) w) (Set.Icc (1 - w) 1) := by
    rw [Set.disjoint_left]
    rintro t ⟨_, htw⟩ ⟨ht1, _⟩
    linarith
  have hint1 : IntegrableOn h (Set.Ioc (0 : ℝ) w) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hw0.le).mp (hcont.intervalIntegrable 0 w)
  have hint2 : IntegrableOn h (Set.Icc (1 - w) 1) volume := hcont.integrableOn_Icc
  rw [majorArc_eq_union x hx, ← hw,
    MeasureTheory.setIntegral_union hdisj measurableSet_Icc hint1 hint2]
  have hIcc : ∫ t in Set.Icc (1 - w) 1, h t = ∫ t in Set.Ioc (0 : ℝ) w, h t := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : 1 - w ≤ 1),
      ← intervalIntegral.integral_of_le hw0.le]
    have hsub := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := w) h 1
    rw [sub_zero] at hsub
    rw [← hsub]
    exact intervalIntegral.integral_congr (fun u _ => hsymm u)
  rw [hIcc]; ring

/-- `∑_{s∈B} (s t)² = S₂ t²`. -/
lemma sum_sq_band (a b c x : ℕ) (t : ℝ) :
    ∑ s ∈ Band a b c x, ((s : ℝ) * t) ^ 2 = (S2 a b c x : ℝ) * t ^ 2 := by
  rw [S2, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun s _ => by push_cast; ring)

/-- `S₂ ≥ card · x²` (each band element is `≥ x`). -/
lemma S2_ge_card_sq (a b c x : ℕ) : (Band a b c x).card * x ^ 2 ≤ S2 a b c x := by
  have hstep : (Band a b c x).card • (x ^ 2) ≤ (Band a b c x).sum (fun s => s ^ 2) := by
    apply Finset.card_nsmul_le_sum
    intro s hs
    exact Nat.pow_le_pow_left (mem_Band.mp hs).2.1 2
  simpa [smul_eq_mul, S2] using hstep

/-- `√S₂ ≥ 10x` once the band has `≥ 100` elements. -/
lemma sqrtS2_ge_10x {a b c x : ℕ} (hM : 100 ≤ (Band a b c x).card) :
    10 * (x : ℝ) ≤ Real.sqrt (S2 a b c x) := by
  have h1 : 100 * x ^ 2 ≤ S2 a b c x :=
    le_trans (Nat.mul_le_mul_right _ hM) (S2_ge_card_sq a b c x)
  have h2 : ((100 * x ^ 2 : ℕ) : ℝ) ≤ (S2 a b c x : ℝ) := by exact_mod_cast h1
  have h3 : (10 * (x : ℝ)) ^ 2 ≤ (S2 a b c x : ℝ) := by push_cast at h2 ⊢; nlinarith [h2]
  calc 10 * (x : ℝ) = Real.sqrt ((10 * (x : ℝ)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (S2 a b c x) := Real.sqrt_le_sqrt h3

/-- `1 ≤ log x` for `x ≥ 3`. -/
lemma one_le_log {x : ℕ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < (x : ℝ))]
  linarith [Real.exp_one_lt_d9]

/-- Window hypothesis in real form: `|S₁ − 2n| ≤ √S₂ / 10`. -/
lemma theta_le (a b c x n : ℕ)
    (hn : 100 * (2 * (n : ℤ) - (S1 a b c x : ℤ)) ^ 2 ≤ (S2 a b c x : ℤ)) :
    |(S1 a b c x : ℝ) - 2 * (n : ℝ)| ≤ Real.sqrt (S2 a b c x) / 10 := by
  set θ : ℝ := (S1 a b c x : ℝ) - 2 * (n : ℝ) with hθ
  have hR : 100 * θ ^ 2 ≤ (S2 a b c x : ℝ) := by
    have h2 : ((100 * (2 * (n : ℤ) - (S1 a b c x : ℤ)) ^ 2 : ℤ) : ℝ)
        ≤ (((S2 a b c x : ℤ) : ℤ) : ℝ) := by exact_mod_cast hn
    push_cast at h2
    rw [hθ]
    nlinarith [h2]
  have hkey : Real.sqrt (100 * θ ^ 2) ≤ Real.sqrt (S2 a b c x) := Real.sqrt_le_sqrt hR
  have h1 : Real.sqrt (100 * θ ^ 2) = 10 * |θ| := by
    rw [show (100 : ℝ) * θ ^ 2 = (10 * |θ|) ^ 2 by rw [mul_pow, sq_abs]; norm_num,
      Real.sqrt_sq (by positivity)]
  rw [h1] at hkey
  linarith

/-- `√S₂ ≤ 10 · x · log x` for `x ≥ 3` (band-count upper bound + `Nat.log` bridge). -/
lemma sqrtS2_le_10xL {a b c x : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) (hx : 3 ≤ x) :
    Real.sqrt (S2 a b c x) ≤ 10 * (x : ℝ) * Real.log x := by
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hL1 : 1 ≤ Real.log x := one_le_log hx
  set L : ℝ := Real.log x with hLdef
  set K : ℝ := (Nat.log 2 (2 * x) : ℝ) with hKdef
  -- K ≤ 1 + L / log 2 ≤ 1 + 1.45 L
  have hK1 : K ≤ Real.log (2 * x) / Real.log 2 := natLog_two_le_realLog x (by omega)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hsplit : Real.log ((2 : ℝ) * x) = Real.log 2 + L := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  have hK2 : K ≤ 1 + L / Real.log 2 := by
    rw [hsplit] at hK1
    calc K ≤ (Real.log 2 + L) / Real.log 2 := hK1
      _ = 1 + L / Real.log 2 := by field_simp
  have hK3 : L / Real.log 2 ≤ 1.45 * L := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hL1]
  have hK5 : K + 1 ≤ 5 * L := by nlinarith [hK2, hK3, hL1]
  -- S2 ≤ (K+1)² (2x)² ≤ (10 x L)²
  have hcard := band_card_le_sq ha hb hc hco x
  have hS2 : S2 a b c x ≤ (Nat.log 2 (2 * x) + 1) ^ 2 * (2 * x) ^ 2 :=
    le_trans (S2_upper x) (Nat.mul_le_mul_right _ hcard)
  have hS2R : (S2 a b c x : ℝ) ≤ (K + 1) ^ 2 * (2 * (x : ℝ)) ^ 2 := by
    have := hS2
    have hcast : ((S2 a b c x : ℕ) : ℝ)
        ≤ (((Nat.log 2 (2 * x) + 1) ^ 2 * (2 * x) ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast
    rw [hKdef]
    linarith [hcast]
  have hK0 : (0 : ℝ) ≤ K + 1 := by rw [hKdef]; positivity
  have hfin : (S2 a b c x : ℝ) ≤ (10 * (x : ℝ) * L) ^ 2 := by
    have hsq : (K + 1) ^ 2 ≤ (5 * L) ^ 2 := by nlinarith [hK5, hK0]
    calc (S2 a b c x : ℝ) ≤ (K + 1) ^ 2 * (2 * (x : ℝ)) ^ 2 := hS2R
      _ ≤ (5 * L) ^ 2 * (2 * (x : ℝ)) ^ 2 := by
          apply mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = (10 * (x : ℝ) * L) ^ 2 := by ring
  calc Real.sqrt (S2 a b c x) ≤ Real.sqrt ((10 * (x : ℝ) * L) ^ 2) := Real.sqrt_le_sqrt hfin
    _ = 10 * (x : ℝ) * L := Real.sqrt_sq (by positivity)

/-- **Head lower bound**: on `(0, 1/√S₂]` the Gaussian main term gives
    `∫ G ≥ 3/(16π√S₂)`. -/
lemma head_lower (a b c x n : ℕ) (hx : 3 ≤ x) (hM : 100 ≤ (Band a b c x).card)
    (hθ : |(S1 a b c x : ℝ) - 2 * (n : ℝ)| ≤ Real.sqrt (S2 a b c x) / 10) :
    3 / (16 * Real.pi * Real.sqrt (S2 a b c x))
      ≤ ∫ t in Set.Ioc (0 : ℝ) (1 / Real.sqrt (S2 a b c x)),
          (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t)) := by
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  set V : ℝ := Real.sqrt (S2 a b c x) with hVdef
  have hV10 : 10 * (x : ℝ) ≤ V := sqrtS2_ge_10x hM
  have hVpos : 0 < V := by linarith
  have hV2 : V ^ 2 = (S2 a b c x : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπ15 : Real.pi < 3.15 := Real.pi_lt_d2
  set θ : ℝ := (S1 a b c x : ℝ) - 2 * (n : ℝ) with hθdef
  set t₁ : ℝ := 1 / V with ht₁def
  set t₀ : ℝ := 1 / (2 * Real.pi * V) with ht₀def
  have ht₀pos : 0 < t₀ := by rw [ht₀def]; positivity
  have ht₀t₁ : t₀ ≤ t₁ := by
    rw [ht₀def, ht₁def]
    exact one_div_le_one_div_of_le hVpos (by nlinarith)
  set G : ℝ → ℝ := fun t =>
    (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
      * Real.cos (Real.pi * (θ * t)) with hGdef
  -- pointwise Gaussian lower bound on the whole head interval
  have hG : ∀ t ∈ Set.Ioc (0 : ℝ) t₁,
      Real.exp (-(Real.pi ^ 2 * ((S2 a b c x : ℝ) * t ^ 2))) * (1 / 2) ≤ G t := by
    rintro t ⟨ht0, ht1⟩
    have hst : ∀ s ∈ Band a b c x, 0 ≤ (s : ℝ) * t ∧ (s : ℝ) * t ≤ 1 / 5 := by
      intro s hs
      obtain ⟨-, hxs, h2s⟩ := mem_Band.mp hs
      have hs2x : (s : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast (by omega : s ≤ 2 * x)
      refine ⟨mul_nonneg (Nat.cast_nonneg s) ht0.le, ?_⟩
      have ht1' : t ≤ 1 / (10 * (x : ℝ)) := by
        refine le_trans ht1 ?_
        rw [ht₁def]
        exact one_div_le_one_div_of_le (by positivity) hV10
      calc (s : ℝ) * t ≤ (2 * (x : ℝ)) * (1 / (10 * (x : ℝ))) :=
            mul_le_mul hs2x ht1' ht0.le (by positivity)
        _ = 1 / 5 := by field_simp; ring
    have hsum : ∑ s ∈ Band a b c x, -((Real.pi * ((s : ℝ) * t)) ^ 2)
        = -(Real.pi ^ 2 * ((S2 a b c x : ℝ) * t ^ 2)) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      rw [← sum_sq_band a b c x t, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    have hterm : ∀ s ∈ Band a b c x,
        Real.exp (-((Real.pi * ((s : ℝ) * t)) ^ 2)) ≤ Real.cos (Real.pi * ((s : ℝ) * t)) := by
      intro s hs
      obtain ⟨h0, h5⟩ := hst s hs
      apply cos_ge_exp_neg_sq
      have hup : Real.pi * ((s : ℝ) * t) ≤ Real.pi * (1 / 5) :=
        mul_le_mul_of_nonneg_left h5 Real.pi_pos.le
      nlinarith [mul_nonneg Real.pi_pos.le h0]
    have hP : Real.exp (-(Real.pi ^ 2 * ((S2 a b c x : ℝ) * t ^ 2)))
        ≤ ∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)) := by
      calc Real.exp (-(Real.pi ^ 2 * ((S2 a b c x : ℝ) * t ^ 2)))
          = Real.exp (∑ s ∈ Band a b c x, -((Real.pi * ((s : ℝ) * t)) ^ 2)) := by rw [hsum]
        _ = ∏ s ∈ Band a b c x, Real.exp (-((Real.pi * ((s : ℝ) * t)) ^ 2)) :=
            Real.exp_sum _ _
        _ ≤ ∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)) :=
            Finset.prod_le_prod (fun s _ => (Real.exp_pos _).le) hterm
    have hcosθ : (1 / 2 : ℝ) ≤ Real.cos (Real.pi * (θ * t)) := by
      have h1 : |θ * t| = |θ| * t := by rw [abs_mul, abs_of_pos ht0]
      have h2 : |θ| * t ≤ (V / 10) * (1 / V) :=
        mul_le_mul hθ (by rw [ht₁def] at ht1; exact ht1) ht0.le (by positivity)
      have h3 : (V / 10) * (1 / V) = 1 / 10 := by field_simp
      have habs : |Real.pi * (θ * t)| ≤ Real.pi * (1 / 10) := by
        rw [abs_mul, abs_of_pos Real.pi_pos, h1]
        exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
      have hsq : (Real.pi * (θ * t)) ^ 2 ≤ (Real.pi / 10) ^ 2 := by
        nlinarith [sq_abs (Real.pi * (θ * t)), abs_nonneg (Real.pi * (θ * t))]
      have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi * (θ * t))
      nlinarith [hπ15, Real.pi_pos]
    have hPnn : (0 : ℝ) ≤ ∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)) :=
      le_trans (Real.exp_pos _).le hP
    exact mul_le_mul hP hcosθ (by norm_num) hPnn
  -- continuity and integrability
  have hGcont : Continuous G := by rw [hGdef]; fun_prop
  have hint : ∀ u v : ℝ, u ≤ v → IntegrableOn G (Set.Ioc u v) volume := fun u v huv =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mp (hGcont.intervalIntegrable u v)
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) t₀) (Set.Ioc t₀ t₁) := by
    rw [Set.disjoint_left]; rintro u ⟨_, h1⟩ ⟨h2, _⟩; linarith
  have hsplitI : Set.Ioc (0 : ℝ) t₁ = Set.Ioc 0 t₀ ∪ Set.Ioc t₀ t₁ :=
    (Set.Ioc_union_Ioc_eq_Ioc ht₀pos.le ht₀t₁).symm
  have ht₀sq : Real.pi ^ 2 * ((S2 a b c x : ℝ) * t₀ ^ 2) = 1 / 4 := by
    rw [← hV2, ht₀def]
    field_simp
    ring
  -- the head piece: G ≥ 3/8 on (0, t₀]
  have hhead : (3 / 8) * t₀ ≤ ∫ t in Set.Ioc (0 : ℝ) t₀, G t := by
    have hconst : ∫ _t in Set.Ioc (0 : ℝ) t₀, (3 / 8 : ℝ) = (3 / 8) * t₀ := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le ht₀pos.le, sub_zero,
        smul_eq_mul, mul_comm]
    rw [← hconst]
    refine setIntegral_mono_on (integrableOn_const (by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)) (hint 0 t₀ ht₀pos.le)
      measurableSet_Ioc ?_
    rintro t ⟨ht0, htt₀⟩
    have hGt := hG t ⟨ht0, le_trans htt₀ ht₀t₁⟩
    have hS2nn : (0 : ℝ) ≤ (S2 a b c x : ℝ) := Nat.cast_nonneg _
    have ht2 : t ^ 2 ≤ t₀ ^ 2 := by nlinarith [ht0.le, htt₀]
    have hmono : Real.pi ^ 2 * ((S2 a b c x : ℝ) * t ^ 2)
        ≤ Real.pi ^ 2 * ((S2 a b c x : ℝ) * t₀ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht2 hS2nn) (sq_nonneg Real.pi)
    have hexp : (3 / 4 : ℝ) ≤ Real.exp (-(Real.pi ^ 2 * ((S2 a b c x : ℝ) * t ^ 2))) := by
      have := Real.add_one_le_exp (-(Real.pi ^ 2 * ((S2 a b c x : ℝ) * t ^ 2)))
      linarith [ht₀sq, hmono]
    linarith [hGt, hexp]
  -- the second piece is nonnegative
  have htail0 : 0 ≤ ∫ t in Set.Ioc t₀ t₁, G t := by
    refine setIntegral_nonneg measurableSet_Ioc ?_
    rintro t ⟨htl, htu⟩
    have hGt := hG t ⟨lt_trans ht₀pos htl, htu⟩
    have := Real.exp_pos (-(Real.pi ^ 2 * ((S2 a b c x : ℝ) * t ^ 2)))
    nlinarith
  have hval : (3 / 8) * t₀ = 3 / (16 * Real.pi * V) := by
    rw [ht₀def]
    field_simp
    ring
  rw [hsplitI, setIntegral_union hdisj measurableSet_Ioc (hint 0 t₀ ht₀pos.le)
    (hint t₀ t₁ ht₀t₁)]
  linarith [hhead, htail0]

/-- **Tail bound**: on `[1/√S₂, 1/(8x)]` the Gaussian decay kills the integral. -/
lemma tail_bound (a b c x n : ℕ) (hx : 3 ≤ x) (hM : 100 ≤ (Band a b c x).card) :
    |∫ t in Set.Ioc (1 / Real.sqrt (S2 a b c x)) (1 / (8 * (x : ℝ))),
        (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t))|
      ≤ Real.exp (-2) / (4 * Real.sqrt (S2 a b c x)) := by
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  set V : ℝ := Real.sqrt (S2 a b c x) with hVdef
  have hV10 : 10 * (x : ℝ) ≤ V := sqrtS2_ge_10x hM
  have hVpos : 0 < V := by linarith
  have hV2 : V ^ 2 = (S2 a b c x : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  set θ : ℝ := (S1 a b c x : ℝ) - 2 * (n : ℝ) with hθdef
  set w : ℝ := 1 / (8 * (x : ℝ)) with hwdef
  set t₁ : ℝ := 1 / V with ht₁def
  have ht₁pos : 0 < t₁ := by rw [ht₁def]; positivity
  have ht₁w : t₁ ≤ w := by
    rw [ht₁def, hwdef]
    exact le_trans (one_div_le_one_div_of_le (by positivity) hV10)
      (one_div_le_one_div_of_le (by positivity) (by linarith))
  set G : ℝ → ℝ := fun t =>
    (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
      * Real.cos (Real.pi * (θ * t)) with hGdef
  have hGcont : Continuous G := by rw [hGdef]; fun_prop
  -- pointwise: |G t| ≤ V t · exp(−2V²t²) on [t₁, w]
  have hpt : ∀ t ∈ Set.Icc t₁ w, |G t| ≤ V * t * Real.exp (-(2 * V ^ 2 * t ^ 2)) := by
    rintro t ⟨htl, htu⟩
    have ht0 : 0 < t := lt_of_lt_of_le ht₁pos htl
    have h1 : |G t| ≤ ∏ s ∈ Band a b c x, |Real.cos (Real.pi * ((s : ℝ) * t))| := by
      rw [hGdef]
      simp only []
      rw [abs_mul, ← Finset.abs_prod]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    have h2 : ∀ s ∈ Band a b c x,
        |Real.cos (Real.pi * ((s : ℝ) * t))| ≤ Real.exp (-(2 * ((s : ℝ) * t) ^ 2)) := by
      intro s hs
      obtain ⟨-, hxs, h2s⟩ := mem_Band.mp hs
      have hs2x : (s : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast (by omega : s ≤ 2 * x)
      have h0 : 0 ≤ (s : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht0.le
      have hlt : (s : ℝ) * t < 1 / 2 := by
        have htw : t ≤ 1 / (8 * (x : ℝ)) := by rw [hwdef] at htu; exact htu
        calc (s : ℝ) * t ≤ 2 * (x : ℝ) * (1 / (8 * (x : ℝ))) :=
              mul_le_mul hs2x htw ht0.le (by positivity)
          _ = 1 / 4 := by field_simp; ring
          _ < 1 / 2 := by norm_num
      have hround := round_eq_zero_of' h0 hlt
      have hb := abs_cos_le_exp ((s : ℝ) * t)
      rw [hround] at hb
      simpa using hb
    have h3 : (∏ s ∈ Band a b c x, |Real.cos (Real.pi * ((s : ℝ) * t))|)
        ≤ ∏ s ∈ Band a b c x, Real.exp (-(2 * ((s : ℝ) * t) ^ 2)) :=
      Finset.prod_le_prod (fun s _ => abs_nonneg _) h2
    have h4 : (∏ s ∈ Band a b c x, Real.exp (-(2 * ((s : ℝ) * t) ^ 2)))
        = Real.exp (-(2 * V ^ 2 * t ^ 2)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.sum_neg_distrib]
      congr 1
      calc ∑ s ∈ Band a b c x, 2 * ((s : ℝ) * t) ^ 2
          = 2 * ∑ s ∈ Band a b c x, ((s : ℝ) * t) ^ 2 := by rw [Finset.mul_sum]
        _ = 2 * ((S2 a b c x : ℝ) * t ^ 2) := by rw [sum_sq_band]
        _ = 2 * V ^ 2 * t ^ 2 := by rw [hV2]; ring
    have hVt : 1 ≤ V * t := by
      rw [ht₁def] at htl
      calc (1 : ℝ) = V * (1 / V) := by field_simp
        _ ≤ V * t := mul_le_mul_of_nonneg_left htl hVpos.le
    calc |G t| ≤ ∏ s ∈ Band a b c x, |Real.cos (Real.pi * ((s : ℝ) * t))| := h1
      _ ≤ ∏ s ∈ Band a b c x, Real.exp (-(2 * ((s : ℝ) * t) ^ 2)) := h3
      _ = Real.exp (-(2 * V ^ 2 * t ^ 2)) := h4
      _ ≤ V * t * Real.exp (-(2 * V ^ 2 * t ^ 2)) :=
          le_mul_of_one_le_left (Real.exp_nonneg _) hVt
  -- the antiderivative
  have hF : ∀ t ∈ Set.uIcc t₁ w,
      HasDerivAt (fun u : ℝ => -(Real.exp (-(2 * V ^ 2 * u ^ 2)) / (4 * V)))
        (V * t * Real.exp (-(2 * V ^ 2 * t ^ 2))) t := by
    intro t _
    have h0 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h1 : HasDerivAt (fun u : ℝ => -(2 * V ^ 2 * u ^ 2)) (-(2 * V ^ 2 * (2 * t))) t :=
      (h0.const_mul (2 * V ^ 2)).neg
    have h2 := h1.exp
    have h3 : HasDerivAt (fun u : ℝ => -(Real.exp (-(2 * V ^ 2 * u ^ 2)) / (4 * V)))
        (-(Real.exp (-(2 * V ^ 2 * t ^ 2)) * -(2 * V ^ 2 * (2 * t)) / (4 * V))) t :=
      (h2.div_const (4 * V)).neg
    have heq : V * t * Real.exp (-(2 * V ^ 2 * t ^ 2))
        = -(Real.exp (-(2 * V ^ 2 * t ^ 2)) * -(2 * V ^ 2 * (2 * t)) / (4 * V)) := by
      rw [mul_neg, neg_div, neg_neg, eq_div_iff (by positivity : (4 * V : ℝ) ≠ 0)]
      ring
    rw [heq]
    exact h3
  have hintF : IntervalIntegrable
      (fun t : ℝ => V * t * Real.exp (-(2 * V ^ 2 * t ^ 2))) volume t₁ w :=
    (by fun_prop : Continuous
      (fun t : ℝ => V * t * Real.exp (-(2 * V ^ 2 * t ^ 2)))).intervalIntegrable t₁ w
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hintF
  have ht₁V : 2 * V ^ 2 * t₁ ^ 2 = 2 := by
    rw [ht₁def, div_pow, one_pow]
    field_simp [hVpos.ne']
  calc |∫ t in Set.Ioc t₁ w, G t|
      = |∫ t in t₁..w, G t| := by rw [intervalIntegral.integral_of_le ht₁w]
    _ ≤ ∫ t in t₁..w, |G t| := intervalIntegral.abs_integral_le_integral_abs ht₁w
    _ ≤ ∫ t in t₁..w, V * t * Real.exp (-(2 * V ^ 2 * t ^ 2)) :=
        intervalIntegral.integral_mono_on ht₁w (hGcont.abs.intervalIntegrable t₁ w)
          hintF hpt
    _ = -(Real.exp (-(2 * V ^ 2 * w ^ 2)) / (4 * V))
        - -(Real.exp (-(2 * V ^ 2 * t₁ ^ 2)) / (4 * V)) := hFTC
    _ ≤ Real.exp (-2) / (4 * V) := by
        rw [ht₁V]
        have hpos : 0 < Real.exp (-(2 * V ^ 2 * w ^ 2)) / (4 * V) := by positivity
        linarith

/-- **Major-arc lower bound** (proved, replacing the `major_arc_lower` axiom):
    on the sharpened central window `100(2n−S₁)² ≤ S₂`, the major-arc real part is at least
    `2^{|B|}/(250·x·log x)`. -/
theorem major_arc_lower' (a b c : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) :
    ∃ C₅ : ℝ, 1 ≤ C₅ ∧ ∃ X₃ : ℕ, ∀ x : ℕ, X₃ ≤ x → ∀ n : ℕ,
      100 * (2 * (n : ℤ) - (S1 a b c x : ℤ)) ^ 2 ≤ (S2 a b c x : ℤ) →
        (2 : ℝ) ^ (Band a b c x).card / (C₅ * (x : ℝ) * Real.log x) ≤
          (∫ t in MajorArc x,
            (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re := by
  obtain ⟨X₀, hX₀⟩ := band_card_eventually_ge ha hb hc hco 100
  refine ⟨250, by norm_num, max X₀ 3, fun x hx n hn => ?_⟩
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hM : 100 ≤ (Band a b c x).card := hX₀ x (le_trans (le_max_left _ _) hx)
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hθ := theta_le a b c x n hn
  have hV10 : 10 * (x : ℝ) ≤ Real.sqrt (S2 a b c x) := sqrtS2_ge_10x hM
  have hVpos : 0 < Real.sqrt (S2 a b c x) := by linarith
  have ht₁pos : (0 : ℝ) < 1 / Real.sqrt (S2 a b c x) := by positivity
  have ht₁w : 1 / Real.sqrt (S2 a b c x) ≤ 1 / (8 * (x : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  -- fold the arc onto the head interval
  have hcont : Continuous (fun t : ℝ =>
      2 ^ (Band a b c x).card
        * (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
        * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t))) := by fun_prop
  have hsymm : ∀ u : ℝ,
      2 ^ (Band a b c x).card
        * (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * (1 - u))))
        * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * (1 - u)))
      = 2 ^ (Band a b c x).card
        * (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * u)))
        * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * u)) := fun u => by
    rw [← integrand_re a b c x n (1 - u), ← integrand_re a b c x n u]
    exact integrand_re_reflect a b c x n u
  have hre := major_arc_re_eq a b c x n
  have htwice := setIntegral_majorArc_twice x (by omega)
    (fun t : ℝ =>
      2 ^ (Band a b c x).card
        * (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
        * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t))) hcont hsymm
  -- pull out the 2^M factor
  have hpull : (∫ t in Set.Ioc (0 : ℝ) (1 / (8 * (x : ℝ))),
        2 ^ (Band a b c x).card
          * (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t)))
      = 2 ^ (Band a b c x).card * ∫ t in Set.Ioc (0 : ℝ) (1 / (8 * (x : ℝ))),
          (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t)) := by
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  -- split the head interval at 1/√S₂
  have hGcont : Continuous (fun t : ℝ =>
      (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
        * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t))) := by fun_prop
  have hint1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht₁pos.le).mp
    (hGcont.intervalIntegrable (μ := volume) 0 (1 / Real.sqrt (S2 a b c x)))
  have hint2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht₁w).mp
    (hGcont.intervalIntegrable (μ := volume) (1 / Real.sqrt (S2 a b c x)) (1 / (8 * (x : ℝ))))
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) (1 / Real.sqrt (S2 a b c x)))
      (Set.Ioc (1 / Real.sqrt (S2 a b c x)) (1 / (8 * (x : ℝ)))) := by
    rw [Set.disjoint_left]; rintro u ⟨_, h1⟩ ⟨h2, _⟩; linarith
  have hsplit : (∫ t in Set.Ioc (0 : ℝ) (1 / (8 * (x : ℝ))),
        (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t)))
      = (∫ t in Set.Ioc (0 : ℝ) (1 / Real.sqrt (S2 a b c x)),
          (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t)))
        + ∫ t in Set.Ioc (1 / Real.sqrt (S2 a b c x)) (1 / (8 * (x : ℝ))),
            (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
              * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t)) := by
    rw [← setIntegral_union hdisj measurableSet_Ioc hint1 hint2,
      Set.Ioc_union_Ioc_eq_Ioc ht₁pos.le ht₁w]
  -- head and tail estimates
  have hhead := head_lower a b c x n hx3 hM hθ
  have htail := tail_bound a b c x n hx3 hM
  -- numerics: 1/50 + e⁻²/4 ≤ 3/(16π)
  have hnum : 1 / 50 + Real.exp (-2) / 4 ≤ 3 / (16 * Real.pi) := by
    have hπ : Real.pi < 3.15 := Real.pi_lt_d2
    have hπ0 : 0 < Real.pi := Real.pi_pos
    have he2 : (7.29 : ℝ) < Real.exp 2 := by
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_one_gt_d9]
    have hexp2 : Real.exp (-2) < 1 / 7.29 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_lt_one_div_of_lt (by norm_num) he2
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hexp2, hπ, hπ0, (Real.exp_pos (-2)).le]
  -- combine: the folded integral is at least 1/(50√S₂)
  have hAB : 1 / (50 * Real.sqrt (S2 a b c x))
      ≤ (∫ t in Set.Ioc (0 : ℝ) (1 / Real.sqrt (S2 a b c x)),
          (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t)))
        + ∫ t in Set.Ioc (1 / Real.sqrt (S2 a b c x)) (1 / (8 * (x : ℝ))),
            (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
              * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t)) := by
    have htail' := (abs_le.mp htail).1
    have hstep : 1 / (50 * Real.sqrt (S2 a b c x))
        ≤ 3 / (16 * Real.pi * Real.sqrt (S2 a b c x))
          - Real.exp (-2) / (4 * Real.sqrt (S2 a b c x)) := by
      have e1 : 1 / (50 * Real.sqrt (S2 a b c x)) = (1 / 50) * (1 / Real.sqrt (S2 a b c x)) := by
        ring
      have e2 : 3 / (16 * Real.pi * Real.sqrt (S2 a b c x))
          = (3 / (16 * Real.pi)) * (1 / Real.sqrt (S2 a b c x)) := by ring
      have e3 : Real.exp (-2) / (4 * Real.sqrt (S2 a b c x))
          = (Real.exp (-2) / 4) * (1 / Real.sqrt (S2 a b c x)) := by ring
      rw [e1, e2, e3]
      have hVinv : (0 : ℝ) ≤ 1 / Real.sqrt (S2 a b c x) := by positivity
      nlinarith [mul_nonneg (by linarith [hnum] :
        (0 : ℝ) ≤ 3 / (16 * Real.pi) - Real.exp (-2) / 4 - 1 / 50) hVinv]
    linarith [hhead, htail', hstep]
  -- final comparison of constants
  have hL1 : 1 ≤ Real.log x := one_le_log hx3
  have hVle : Real.sqrt (S2 a b c x) ≤ 10 * (x : ℝ) * Real.log x :=
    sqrtS2_le_10xL (by omega) (by omega) (by omega) hco hx3
  have h2M : (0 : ℝ) < 2 ^ (Band a b c x).card := by positivity
  rw [hre, htwice, hpull, hsplit]
  calc (2 : ℝ) ^ (Band a b c x).card / (250 * (x : ℝ) * Real.log x)
      ≤ (2 : ℝ) ^ (Band a b c x).card / (25 * Real.sqrt (S2 a b c x)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h25 : 25 * Real.sqrt (S2 a b c x) ≤ 250 * (x : ℝ) * Real.log x := by
          nlinarith [hVle]
        exact mul_le_mul_of_nonneg_left h25 h2M.le
    _ = 2 * (2 ^ (Band a b c x).card * (1 / (50 * Real.sqrt (S2 a b c x)))) := by
        field_simp
        ring
    _ ≤ 2 * (2 ^ (Band a b c x).card * _) := by gcongr

end Erdos123Band

#print axioms Erdos123Band.major_arc_lower'
