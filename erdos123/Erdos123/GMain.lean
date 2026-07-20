/-
GMain — the assembly of the general-ratio theorem.

  `erdos123_dcomplete_general` : for pairwise-coprime a,b,c > 1 and any rational
  ρ = p/q with 1 < p/q < min(a,b,c), every large n is the sum of a primitive
  (antichain) subset of the band `GBand a b c p q x = Smooth3 ∩ [x, (p/q)x)` for
  some x; plus the real-ρ corollary `erdos123_dcomplete_real`.

Intended route (FAITHFUL_LCLT.md): coverage of the FULL central window
|n − μ_x| ≤ σ_x comes from the local CLT module `Erdos123.GLCLT`
(`glclt_coverage`); the sweep is the paper's μ-record argument; primitivity is
`gband_primitive` (unique-factorization antichain).

STATUS (2026-07-19): THIS FILE COMPILES AND IS SORRY-FREE.
`glclt_coverage` is now proved in `Erdos123.GLCLT` (full central window, no added
hypotheses), and both `erdos123_dcomplete_general` and `erdos123_dcomplete_real` verify
with axiom footprint exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Erdos123.GBand
import Erdos123.GLCLT

set_option maxHeartbeats 1000000

namespace Erdos123Band

/-- **The sweep** (paper §5, faithful full window): as `x` slides, the windows
`|2n − GS1| ≤ √GS2` overlap (`GS1` steps by `≤ p²(x+1)`, half-width `√GS2 ≥ 2p²x`
once the band has `≥ 4p⁴` elements) and cover a half-line. -/
theorem gsweep {a b c p q : ℕ} (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) (X₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∃ x : ℕ, X₀ ≤ x ∧
      (2 * (n : ℤ) - (GS1 a b c p q x : ℤ)) ^ 2 ≤ (GS2 a b c p q x : ℤ) := by
  classical
  obtain ⟨X₁, hX₁⟩ := gband_card_eventually_ge ha hb hc hco hq hqp hpd (4 * p ^ 4)
  set X₂ : ℕ := max (max X₀ X₁) 2 with hX₂def
  have hX₂card : ∀ x : ℕ, X₂ ≤ x → 4 * p ^ 4 ≤ (GBand a b c p q x).card := fun x hx =>
    hX₁ x (le_trans (le_trans (le_max_right X₀ X₁) (le_max_left _ 2)) hx)
  have hp1 : 1 ≤ p := by omega
  have hp4 : 1 ≤ 4 * p ^ 4 := by
    have h1 : 1 ≤ p ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hS2of : ∀ x : ℕ, X₂ ≤ x → 4 * p ^ 4 * x ^ 2 ≤ GS2 a b c p q x := by
    intro x hx
    calc 4 * p ^ 4 * x ^ 2 ≤ (GBand a b c p q x).card * x ^ 2 :=
          Nat.mul_le_mul_right _ (hX₂card x hx)
      _ ≤ GS2 a b c p q x := gS2_ge_card_sq a b c p q x
  refine ⟨GS1 a b c p q X₂ + 1, fun n hn => ?_⟩
  set Q : ℕ → Prop := fun x' => X₂ ≤ x' ∧ GS1 a b c p q x' ≤ 2 * n with hQdef
  have hQ_le : ∀ x', Q x' → x' ≤ 2 * n := by
    intro x' ⟨hx', hs1⟩
    have hcard : 1 ≤ (GBand a b c p q x').card := le_trans hp4 (hX₂card x' hx')
    exact le_trans (gle_S1_of_card_pos hcard) hs1
  have hQX₂ : Q X₂ := ⟨le_refl _, by omega⟩
  have hX₂le : X₂ ≤ 2 * n + 1 := le_trans (hQ_le X₂ hQX₂) (by omega)
  set x : ℕ := Nat.findGreatest Q (2 * n + 1) with hxdef
  have hspec : Q x := Nat.findGreatest_spec hX₂le hQX₂
  have hxle : x ≤ 2 * n := hQ_le x hspec
  have hnot : ¬Q (x + 1) :=
    Nat.findGreatest_is_greatest (P := Q) (n := 2 * n + 1) (k := x + 1)
      (by omega) (by omega)
  have hnext : 2 * n < GS1 a b c p q (x + 1) := by
    by_contra hcon
    exact hnot ⟨le_trans hspec.1 (by omega), by omega⟩
  have hstep := gS1_step_upper (a := a) (b := b) (c := c) (p := p) hq x
  have hS2 := hS2of x hspec.1
  have hx2 : 2 ≤ x := le_trans (le_max_right _ 2) hspec.1
  refine ⟨x, le_trans (le_trans (le_max_left X₀ X₁) (le_max_left _ 2)) hspec.1, ?_⟩
  have h1 : (GS1 a b c p q x : ℤ) ≤ 2 * (n : ℤ) := by exact_mod_cast hspec.2
  have h2 : 2 * (n : ℤ) - (GS1 a b c p q x : ℤ) ≤ (p : ℤ) * p * ((x : ℤ) + 1) := by
    have hz : (2 * n : ℤ) < (GS1 a b c p q (x + 1) : ℤ) := by exact_mod_cast hnext
    have hcast : (GS1 a b c p q (x + 1) : ℤ)
        ≤ (GS1 a b c p q x : ℤ) + (p : ℤ) * p * ((x : ℤ) + 1) := by
      exact_mod_cast hstep
    linarith
  have h3 : (4 : ℤ) * (p : ℤ) ^ 4 * (x : ℤ) ^ 2 ≤ (GS2 a b c p q x : ℤ) := by
    exact_mod_cast hS2
  have hx2' : (2 : ℤ) ≤ (x : ℤ) := by exact_mod_cast hx2
  have hP0 : (0 : ℤ) ≤ (p : ℤ) * p := by positivity
  have hA0 : 0 ≤ 2 * (n : ℤ) - (GS1 a b c p q x : ℤ) := by linarith
  have h4 : (p : ℤ) * p * ((x : ℤ) + 1) ≤ 2 * ((p : ℤ) * p) * (x : ℤ) := by
    nlinarith [hx2', hP0]
  have hAB : 2 * (n : ℤ) - (GS1 a b c p q x : ℤ) ≤ 2 * ((p : ℤ) * p) * (x : ℤ) :=
    le_trans h2 h4
  have h5 : (2 * (n : ℤ) - (GS1 a b c p q x : ℤ)) ^ 2
      ≤ (2 * ((p : ℤ) * p) * (x : ℤ)) ^ 2 := by
    nlinarith [hA0, hAB]
  calc (2 * (n : ℤ) - (GS1 a b c p q x : ℤ)) ^ 2
      ≤ (2 * ((p : ℤ) * p) * (x : ℤ)) ^ 2 := h5
    _ = 4 * (p : ℤ) ^ 4 * (x : ℤ) ^ 2 := by ring
    _ ≤ (GS2 a b c p q x : ℤ) := h3

/-- **Erdős #123, general rational ratio** `ρ = p/q ∈ (1, min(a,b,c))`: every large `n`
is the sum of a primitive subset of the band `Smooth3 ∩ [x, ρx)` for some `x`. -/
theorem erdos123_dcomplete_general (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ x : ℕ, ∃ T : Finset ℕ, T ⊆ GBand a b c p q x ∧ (∀ s ∈ T, s ∈ Smooth3 a b c) ∧
        IsPrimitive T ∧ T.sum id = n := by
  obtain ⟨X₀, hcov⟩ := glclt_coverage a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨N₀, hsweep⟩ := gsweep ha hb hc hco hq hqp hpd X₀
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨x, hx, hwin⟩ := hsweep n hn
  obtain ⟨T, hsub, hsum⟩ := hcov x hx n hwin
  exact ⟨x, T, hsub, fun s hs => (of_mem_GBand (hsub hs)).1,
    (gband_primitive ha hb hc hco hq hpd x).subset hsub, hsum⟩

/-- **Erdős #123, real ratio**: for any real `ρ ∈ (1, min(a,b,c))`, every large `n` is
the sum of a primitive subset of `Smooth3 ∩ [x, ρx)` for some `x` (via a rational
`p/q ∈ (1, ρ)`). -/
theorem erdos123_dcomplete_real (a b c : ℕ) (ρ : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hρ1 : 1 < ρ) (hρd : ρ < min a (min b c)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ x : ℕ, ∃ T : Finset ℕ,
        (∀ s ∈ T, s ∈ Smooth3 a b c ∧ (x : ℝ) ≤ s ∧ (s : ℝ) < ρ * x) ∧
        IsPrimitive T ∧ T.sum id = n := by
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hρ1
  set p : ℕ := r.num.toNat with hpdef
  set q : ℕ := r.den with hqdef
  have hq0 : 0 < q := r.pos
  have hr0 : (0 : ℚ) < r := by
    have h1 : (0 : ℝ) < (r : ℝ) := lt_trans one_pos hr1
    exact_mod_cast h1
  have hnum0 : 0 < r.num := Rat.num_pos.mpr hr0
  have hpn : ((p : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum0.le
  have hp0 : 0 < p := by
    have h1 : (0 : ℤ) < ((p : ℕ) : ℤ) := by rw [hpn]; exact hnum0
    exact_mod_cast h1
  have hpR : ((p : ℕ) : ℝ) = ((r.num : ℤ) : ℝ) := by exact_mod_cast hpn
  have hrcast : (r : ℝ) = (p : ℝ) / (q : ℝ) := by
    rw [Rat.cast_def, hpR, hqdef]
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hqp : q < p := by
    have h1 : (q : ℝ) < (p : ℝ) := by
      have h2 : (1 : ℝ) < (p : ℝ) / (q : ℝ) := by rw [← hrcast]; exact hr1
      rw [lt_div_iff₀ hqR] at h2
      linarith
    exact_mod_cast h1
  have hpd : p < q * min a (min b c) := by
    have hminR : ((min a (min b c) : ℕ) : ℝ) = min (a : ℝ) (min (b : ℝ) (c : ℝ)) := by
      push_cast
      rfl
    have h1 : (p : ℝ) / (q : ℝ) < min (a : ℝ) (min (b : ℝ) (c : ℝ)) := by
      rw [← hrcast, ← hminR]; exact lt_trans hr2 hρd
    have h2 : (p : ℝ) < (q : ℝ) * ((min a (min b c) : ℕ) : ℝ) := by
      rw [hminR]
      rw [div_lt_iff₀ hqR] at h1
      linarith
    have h3 : (p : ℝ) < ((q * min a (min b c) : ℕ) : ℝ) := by
      push_cast
      push_cast at h2
      linarith
    exact_mod_cast h3
  obtain ⟨N₀, hgen⟩ := erdos123_dcomplete_general a b c p q ha hb hc hco hq0 hqp hpd
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  obtain ⟨x, T, hsub, hsmooth, hprim, hsum⟩ := hgen n (le_trans (le_max_left _ _) hn)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hTne : T.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hsum
    omega
  obtain ⟨s₀, hs₀⟩ := hTne
  have hx0 : 0 < x := by
    obtain ⟨-, -, hw⟩ := of_mem_GBand (hsub hs₀)
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · rw [h0, Nat.mul_zero] at hw
      exact absurd hw (Nat.not_lt_zero _)
    · exact h0
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
  refine ⟨x, T, fun s hs => ?_, hprim, hsum⟩
  obtain ⟨hS, hxs, hw⟩ := of_mem_GBand (hsub hs)
  refine ⟨hS, by exact_mod_cast hxs, ?_⟩
  have hcast : (q : ℝ) * (s : ℝ) < (p : ℝ) * (x : ℝ) := by exact_mod_cast hw
  have h1 : (s : ℝ) < (p : ℝ) / (q : ℝ) * (x : ℝ) := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hqR]
    nlinarith [hcast]
  have h2 : (p : ℝ) / (q : ℝ) * (x : ℝ) < ρ * (x : ℝ) := by
    apply mul_lt_mul_of_pos_right _ hxR
    rw [← hrcast]
    exact hr2
  linarith

end Erdos123Band

#print axioms Erdos123Band.erdos123_dcomplete_general
#print axioms Erdos123Band.erdos123_dcomplete_real
