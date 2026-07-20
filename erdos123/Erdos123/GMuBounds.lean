/-
G-μ — The missing third pair of bounds in Lemma 2.1 ("Band geometry") of the paper.

Lemma 2.1 asserts three two-sided estimates for large `x` (with `L = log x`):
  * `c L² ≤ |B_x| ≤ C L²`   — `gband_card_ge_sq` (GGrid), `gband_card_le_sq` (GSlab)
  * `c x L ≤ σ_x ≤ C x L`   — `gV_lower`, `gV_upper` (GBandAux)
  * `c x L² ≤ μ_x ≤ C x L²` — THIS FILE

Here `W_x = ∑_{s ∈ B_x} s = GS1 a b c p q x` and `μ_x = W_x / 2`.

Contents:
  * `gMu_lower`, `gMu_upper` — two-sided `GS1 ≍ x · (log x)²`
  * `gmu_bounds`             — the same, phrased for `μ_x = GS1 / 2`

Both are pure sandwiches:
  lower   `GS1 = ∑_{s ∈ B} s ≥ |B| · x ≥ c₁ L² · x`
  upper   `GS1 = ∑_{s ∈ B} s ≤ |B| · (p x) ≤ (log₂(2px)+1)² · p x ≤ 16 p · x L²`.
-/
import Erdos123.GBandAux

set_option maxHeartbeats 1000000

namespace Erdos123Band

/-! ## Elementary sandwich brick: `|B| · x ≤ GS1 ≤ |B| · (p x)` -/

/-- Every band element is `≥ x`, so `GS1 ≥ |B_x| · x`. -/
lemma gS1_ge_card_mul (a b c p q x : ℕ) :
    (GBand a b c p q x).card * x ≤ GS1 a b c p q x := by
  classical
  have h : (GBand a b c p q x).card • x ≤ ∑ s ∈ GBand a b c p q x, id s :=
    Finset.card_nsmul_le_sum _ _ _ (fun s hs => (of_mem_GBand hs).2.1)
  simpa [GS1, smul_eq_mul] using h

/-- Every band element is `≤ p·x`, so `GS1 ≤ |B_x| · (p x)`. -/
lemma gS1_le_card_mul {a b c p q : ℕ} (hq : 0 < q) (x : ℕ) :
    GS1 a b c p q x ≤ (GBand a b c p q x).card * (p * x) := by
  classical
  have h : ∑ s ∈ GBand a b c p q x, id s ≤ (GBand a b c p q x).card • (p * x) :=
    Finset.sum_le_card_nsmul _ _ _ (fun s hs => gband_le hq hs)
  simpa [GS1, smul_eq_mul] using h

/-! ## The two-sided bound `GS1 ≍ x · (log x)²` -/

/-- **Lower bound `μ_x ≫ x (log x)²`** (stated for `W_x = GS1`).

`GS1 = ∑_{s ∈ B_x} s ≥ |B_x| · x` and `|B_x| ≥ c₁ (log x)²` by `gband_card_ge_sq`. -/
theorem gMu_lower (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ cM : ℝ, 0 < cM ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      cM * (x : ℝ) * Real.log x ^ 2 ≤ (GS1 a b c p q x : ℝ) := by
  obtain ⟨c₁, hc₁, X₁, hX₁⟩ := gband_card_ge_sq a b c p q ha hb hc hco hq hqp hpd
  refine ⟨c₁, hc₁, max X₁ 3, fun x hx => ?_⟩
  have hx1 : X₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hcard : c₁ * Real.log x ^ 2 ≤ ((GBand a b c p q x).card : ℝ) := hX₁ x hx1
  have hS1 : ((GBand a b c p q x).card : ℝ) * (x : ℝ) ≤ (GS1 a b c p q x : ℝ) := by
    have h := gS1_ge_card_mul a b c p q x
    have h2 : (((GBand a b c p q x).card * x : ℕ) : ℝ) ≤ ((GS1 a b c p q x : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h2
    linarith
  have hstep : c₁ * Real.log x ^ 2 * (x : ℝ) ≤ ((GBand a b c p q x).card : ℝ) * (x : ℝ) :=
    mul_le_mul_of_nonneg_right hcard hxpos.le
  calc c₁ * (x : ℝ) * Real.log x ^ 2 = c₁ * Real.log x ^ 2 * (x : ℝ) := by ring
    _ ≤ ((GBand a b c p q x).card : ℝ) * (x : ℝ) := hstep
    _ ≤ (GS1 a b c p q x : ℝ) := hS1

/-- **Upper bound `μ_x ≪ x (log x)²`** (stated for `W_x = GS1`).

`GS1 ≤ |B_x| · (p x)` and `|B_x| ≤ (log₂(2px)+1)² ≤ (4 log x)²` for `x ≥ max 3 (2p)`.
The `Nat.log → Real.log` step mirrors `gV_upper` verbatim. -/
theorem gMu_upper (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ CM : ℝ, 0 < CM ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      (GS1 a b c p q x : ℝ) ≤ CM * (x : ℝ) * Real.log x ^ 2 := by
  have hp : 0 < p := lt_trans hq hqp
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpc : p < q * c :=
    lt_of_lt_of_le hpd (Nat.mul_le_mul_left q (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨16 * (p : ℝ), by linarith, max 3 (2 * p), fun x hx => ?_⟩
  have hx3 : 3 ≤ x := le_trans (le_max_left _ _) hx
  have hx2p : 2 * p ≤ x := le_trans (le_max_right _ _) hx
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hL1 : 1 ≤ Real.log x := one_le_log hx3
  have h2p : (0 : ℝ) < ((2 * p : ℕ) : ℝ) := by
    have h : 0 < 2 * p := by omega
    exact_mod_cast h
  have hm1 : 1 ≤ 2 * p * x := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  have hKR0 : (0 : ℝ) ≤ ((Nat.log 2 (2 * p * x) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hKle : ((Nat.log 2 (2 * p * x) : ℕ) : ℝ)
      ≤ Real.log ((2 * p * x : ℕ) : ℝ) / Real.log 2 :=
    gnatLog2_le_real (2 * p * x) hm1
  have hsplit : Real.log ((2 * p * x : ℕ) : ℝ)
      = Real.log ((2 * p : ℕ) : ℝ) + Real.log x := by
    rw [show ((2 * p * x : ℕ) : ℝ) = ((2 * p : ℕ) : ℝ) * (x : ℝ) by push_cast; ring,
      Real.log_mul h2p.ne' hxpos.ne']
  have hlog2p : Real.log ((2 * p : ℕ) : ℝ) ≤ Real.log x :=
    Real.log_le_log h2p (by exact_mod_cast hx2p)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hKmul : ((Nat.log 2 (2 * p * x) : ℕ) : ℝ) * Real.log 2 ≤ 2 * Real.log x := by
    have h := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp hKle
    rw [hsplit] at h
    linarith
  have hprod : 0 ≤ ((Nat.log 2 (2 * p * x) : ℕ) : ℝ) * (Real.log 2 - 0.6931471803) :=
    mul_nonneg hKR0 (by linarith)
  have hK4 : ((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1 ≤ 4 * Real.log x := by nlinarith
  -- band count and the first-moment sandwich
  have hcard := gband_card_le_sq (a := a) (b := b) (c := c) (p := p) (q := q)
    (by omega) (by omega) (by omega) hco hq hpc x
  have hS1 := gS1_le_card_mul (a := a) (b := b) (c := c) (p := p) (q := q) hq x
  have hchain : GS1 a b c p q x ≤ (Nat.log 2 (2 * p * x) + 1) ^ 2 * (p * x) :=
    le_trans hS1 (Nat.mul_le_mul_right _ hcard)
  have hchainR : (GS1 a b c p q x : ℝ)
      ≤ (((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) ^ 2 * ((p : ℝ) * (x : ℝ)) := by
    have hc2 : ((GS1 a b c p q x : ℕ) : ℝ)
        ≤ ((((Nat.log 2 (2 * p * x) + 1) ^ 2 * (p * x) : ℕ)) : ℝ) := by
      exact_mod_cast hchain
    calc (GS1 a b c p q x : ℝ)
        ≤ ((((Nat.log 2 (2 * p * x) + 1) ^ 2 * (p * x) : ℕ)) : ℝ) := hc2
      _ = (((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) ^ 2 * ((p : ℝ) * (x : ℝ)) := by
          push_cast; ring
  have hsq : (((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) ^ 2 ≤ (4 * Real.log x) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hK4 2
  calc (GS1 a b c p q x : ℝ)
      ≤ (((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) ^ 2 * ((p : ℝ) * (x : ℝ)) := hchainR
    _ ≤ (4 * Real.log x) ^ 2 * ((p : ℝ) * (x : ℝ)) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = 16 * (p : ℝ) * (x : ℝ) * Real.log x ^ 2 := by ring

/-- **Lemma 2.1, third line**: `c x (log x)² ≤ μ_x ≤ C x (log x)²` for the actual
mean `μ_x = W_x / 2 = GS1 / 2`. Obtained from `gMu_lower`/`gMu_upper` by halving the
constants. -/
theorem gmu_bounds (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ cM CM : ℝ, 0 < cM ∧ 0 < CM ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      cM * (x : ℝ) * Real.log x ^ 2 ≤ (GS1 a b c p q x : ℝ) / 2 ∧
      (GS1 a b c p q x : ℝ) / 2 ≤ CM * (x : ℝ) * Real.log x ^ 2 := by
  obtain ⟨cM, hcM, X₁, hX₁⟩ := gMu_lower a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨CM, hCM, X₂, hX₂⟩ := gMu_upper a b c p q ha hb hc hco hq hqp hpd
  refine ⟨cM / 2, CM / 2, by linarith, by linarith, max X₁ X₂, fun x hx => ?_⟩
  have h1 := hX₁ x (le_trans (le_max_left _ _) hx)
  have h2 := hX₂ x (le_trans (le_max_right _ _) hx)
  constructor
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]; linarith
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]; linarith

end Erdos123Band
