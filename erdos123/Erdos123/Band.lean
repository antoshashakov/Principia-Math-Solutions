/-
ERDŐS PROBLEM #123 — d-COMPLETENESS OF {a^k b^ℓ c^m} FOR PAIRWISE-COPRIME a,b,c > 1
====================================================================================
Campaign master (band + local-CLT route, our independent proof — Erdős–Lewin $250).

  erdos123_dcomplete' :                          (proved in Erdos123/Main.lean)
    ∀ a b c : ℕ, 1 < a → 1 < b → 1 < c → PairwiseCoprime3 a b c →
      IsDComplete (Smooth3 a b c)

Route (writeup: principia-math.com/problems/problem?id=123, CORRECTED 2026-07-16):
the band B_x = S ∩ [x, 3x/2) is a divisibility antichain for free (width 3/2 < 2
beats any divisor ratio ≥ 2 — the published writeup's ρ < min(a,b,c) machinery is
unnecessary); a circle-method argument covers the SHRUNK central window
{n : 100(2n − S1)² ≤ S2} with subset sums of B_x (the paper's full window
{n : (2n − S1)² ≤ S2} needs the local CLT, which is not proved here — see the CAVEAT
below); sliding x sweeps all large n (Nat.findGreatest pin; S1 moves by ≤ 3x+3 per
unit step while the shrunk window half-width √S2/10 stays large enough to overlap).

STATUS (2026-07-19): this file declares NO axioms and states NO headline theorem.
It is the shared definition/brick library for the modules below.  The three labeled
axioms it used to carry (`prop_5_1`, `lemma_5_2`, `major_arc_lower`) and the three
unprimed theorems built on them (`minor_arc_bound`, `lclt_coverage`,
`erdos123_dcomplete`) were DELETED on 2026-07-19: each is strictly superseded by a
proved primed version elsewhere in the tree.  The headline theorem is

  Erdos123Band.erdos123_dcomplete'   (Erdos123/Main.lean)
  #print axioms → [propext, Classical.choice, Quot.sound]   (verified 2026-07-19)

CAVEAT — this is proved for the SHRUNK central window `100(2n−S1)² ≤ S2`, not the
paper's full window `|n−μ_x| ≤ σ_x`.  The statement of `IsDComplete` is unaffected
(the sweep absorbs the shrinkage), but the local-CLT fidelity gap is real and is
recorded in `STATUS.md`.  See `STATUS.md` for the live per-theorem record.

`erdos123_dcomplete'` is obtained by formalizing the paper "Antichain Subset Sums in
Rank-Three Multiplicative Semigroups" (§§2–7) in the sibling modules:
  Slab.lean      — irrational-rotation finite nets, two/three-coordinate slab rounding,
                   three-base unique factorization, |B_x| ≤ (log₂2x+1)²    (paper §2, §3)
  Grid.lean      — the face-preserving bounded-distortion grid embedding   (paper Prop 3.1)
  Routing.lean   — explicit row+path chains, sparse-row/path pigeonhole,
                   cross-ratio propagation, three-term Bézout, corner gcd  (paper Lem 4.1)
  Rigidity.lean  — minor-arc energy floor `lemma_5_2'`                     (paper eq. 5.2)
  LowEnergy.lean — defect-coded measure bound `low_energy_measure`         (paper Prop 5.1
                   at level z = log x; 3 arcs per code, no gcd entropy)
  MajorArcLB.lean— elementary major-arc main term `major_arc_lower'`
                   (pointwise Gaussian bounds; no Fourier transform)       (paper §7)
  Main.lean      — axiom-free assembly with the 1/10-width central window
                   `100(2n−S1)² ≤ S2` and a band-count-2500 sweep.
The earlier notes claiming this route "cannot be closed" referred to the abandoned
cell-decomposition attack (`uniform_cell_theta_bound`); the paper's grid/routing/
rigidity argument, formalized above, settles the minor arc without it.

Verified bricks of THIS file (all machine-checked and reused by the modules above):
  coprime_pow_inj / coprime_pow_ne / log_ratio_irrational   (S-unit unique factorization)
  exists_small_combo / exists_int_step                      (effective near-relation, density)
  pow_succ_le_pow / ladder_count / band_card_eventually_ge  (|B_x| → ∞, geometric ladder)
  cell_quadratic / cell_A_nonneg                            (exact curvature = S2, A ≥ 0)
  mem_Band / band_primitive / IsPrimitive.subset            (band + antichain)
  le_S1_of_card_pos / S2_lower / S1_step_upper / sweep      (the sweep)
  one_add_e_norm / sin_sq_half_ge / abs_cos_le_exp          (LCLT kernel bounds)
  e_add / integral_e / prod_e / subsetSum_fourier          (Fourier subset-sum inversion)
This file contains NO final assembly and NO axioms; the assembly is Main.lean's
`erdos123_dcomplete'`.
-/
import Mathlib
set_option maxHeartbeats 4000000

namespace Erdos123Band

/-! ## Definitions (audited against DeepMind formal-conjectures ErdosProblems/123.lean
and the erdosproblems.com statement; `1 < a,b,c` is the intended nondegenerate
reading — the literal `a,b,c ≥ 1` is false at (1,1,1)). -/

/-- The positive integers representable as `a^k * b^l * c^m` with natural exponents. -/
def Smooth3 (a b c : ℕ) : Set ℕ :=
  {x | ∃ k l m : ℕ, x = a ^ k * b ^ l * c ^ m}

/-- No member of `s` divides another (divisibility antichain on distinct elements). -/
def IsPrimitive (s : Finset ℕ) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ¬x ∣ y

/-- Every sufficiently large natural number is the sum of a primitive finset of `A`. -/
def IsDComplete (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ s : Finset ℕ, (∀ x ∈ s, x ∈ A) ∧ IsPrimitive s ∧ s.sum id = n

/-- Pairwise coprimality of the three bases. -/
def PairwiseCoprime3 (a b c : ℕ) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c

/-- The short multiplicative band `S ∩ [x, 3x/2)` as a finset.
    Width 3/2 < 2 makes it a divisibility antichain automatically. -/
noncomputable def Band (a b c x : ℕ) : Finset ℕ :=
  letI := Classical.decPred (fun s => s ∈ Smooth3 a b c ∧ x ≤ s ∧ 2 * s < 3 * x)
  (Finset.range (2 * x)).filter (fun s => s ∈ Smooth3 a b c ∧ x ≤ s ∧ 2 * s < 3 * x)

/-- Band first moment (`2·μ_x` in the writeup's notation). -/
noncomputable def S1 (a b c x : ℕ) : ℕ := (Band a b c x).sum id

/-- Band second moment (`4·σ_x²` in the writeup's notation). -/
noncomputable def S2 (a b c x : ℕ) : ℕ := (Band a b c x).sum (fun s => s ^ 2)

/-- `e(x) = exp(2πi x)`, the additive character of the circle. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-! ## Arithmetic foundations (reusable S-unit lemmas)

Unique factorization for the two-base monomials + irrationality of the log ratio — the
inputs to the band-count lower bound (multiplicative independence of the bases). Reusable
for any `{a^k b^l …}` S-unit work; see the `problems/` README. -/

/-- For coprime `a,b ≥ 2`, equal monomials force equal exponents (unique factorization). -/
theorem coprime_pow_inj {a b : ℕ} (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b)
    {k l k' l' : ℕ} (h : a ^ k * b ^ l = a ^ k' * b ^ l') : k = k' ∧ l = l' := by
  have key : ∀ {k l k' l' : ℕ}, a ^ k * b ^ l = a ^ k' * b ^ l' → k ≤ k' →
      k = k' ∧ l = l' := by
    intro k l k' l' h hkk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkk
    rw [pow_add, mul_assoc] at h
    have hpos : 0 < a ^ k := pow_pos (by omega) k
    have h2 : b ^ l = a ^ d * b ^ l' := Nat.eq_of_mul_eq_mul_left hpos h
    have hdvd : a ^ d ∣ b ^ l := ⟨b ^ l', by rw [h2]⟩
    have hcop : Nat.Coprime (a ^ d) (b ^ l) := hab.pow d l
    have had1 : a ^ d = 1 := (Nat.gcd_eq_left hdvd).symm.trans hcop
    have hd0 : d = 0 := by
      rcases Nat.pow_eq_one.mp had1 with h1 | h1
      · omega
      · exact h1
    subst hd0
    refine ⟨by omega, ?_⟩
    rw [pow_zero, one_mul] at h2
    exact Nat.pow_right_injective hb h2
  rcases le_total k k' with hkk | hkk
  · exact key h hkk
  · obtain ⟨hk, hl⟩ := key h.symm hkk
    exact ⟨hk.symm, hl.symm⟩

/-- `a^p = b^q` is impossible for coprime `a,b ≥ 2` and `p ≥ 1`. -/
theorem coprime_pow_ne {a b : ℕ} (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b)
    {p q : ℕ} (hp : 1 ≤ p) : a ^ p ≠ b ^ q := by
  intro h
  have h' : a ^ p * b ^ 0 = a ^ 0 * b ^ q := by simpa using h
  obtain ⟨hp0, _⟩ := coprime_pow_inj hab ha hb h'
  omega

/-- `log b / log a` is irrational for coprime `a,b ≥ 2` (⇒ multiplicative independence). -/
theorem log_ratio_irrational {a b : ℕ} (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Irrational (Real.log b / Real.log a) := by
  have hla : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha)
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  rw [Irrational]
  rintro ⟨r, hr⟩
  have hrpos : 0 < (r : ℝ) := by rw [hr]; positivity
  have hrpos' : 0 < r := by exact_mod_cast hrpos
  have hden : 0 < r.den := r.pos
  have hnum : 0 < r.num := Rat.num_pos.mpr hrpos'
  have hrq : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by rw [← Rat.cast_def]
  have heq : (r.den : ℝ) * Real.log b = (r.num : ℝ) * Real.log a := by
    have : Real.log b = (r : ℝ) * Real.log a := by rw [hr]; field_simp
    rw [this, hrq]; field_simp
  set p : ℕ := r.num.toNat with hp
  have hpnum : (r.num : ℝ) = (p : ℝ) := by
    rw [hp]; exact_mod_cast (Int.toNat_of_nonneg hnum.le).symm
  have heq2 : (r.den : ℝ) * Real.log b = (p : ℝ) * Real.log a := by rw [heq, hpnum]
  have hlog : Real.log ((b : ℝ) ^ r.den) = Real.log ((a : ℝ) ^ p) := by
    rw [Real.log_pow, Real.log_pow]; exact_mod_cast heq2
  have hbq : (b : ℝ) ^ r.den = (a : ℝ) ^ p :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hlog
  have hbqn : b ^ r.den = a ^ p := by exact_mod_cast hbq
  have hp1 : 1 ≤ p := by rw [hp]; omega
  exact coprime_pow_ne hab ha hb hp1 hbqn.symm

/-- A small positive ℤ-combination of `log u, log v` exists below any `ε > 0`
    (Mathlib density of `ℤ·log u + ℤ·log v`, from the irrational log ratio). -/
theorem exists_small_combo {u v : ℕ} (huv : Nat.Coprime u v) (hu : 2 ≤ u) (hv : 2 ≤ v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m n : ℤ, 0 < (m : ℝ) * Real.log u + (n : ℝ) * Real.log v ∧
      (m : ℝ) * Real.log u + (n : ℝ) * Real.log v < ε := by
  have hirr : Irrational (Real.log u / Real.log v) := log_ratio_irrational huv.symm hv hu
  have hdense : Dense (AddSubgroup.closure {Real.log u, Real.log v} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  obtain ⟨z, hz1, hz2⟩ :=
    (dense_iff_inter_open.mp hdense) (Set.Ioo 0 ε) isOpen_Ioo (Set.nonempty_Ioo.mpr hε)
  obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hz2
  rw [zsmul_eq_mul, zsmul_eq_mul] at hmn
  exact ⟨m, n, by rw [hmn]; exact hz1.1, by rw [hmn]; exact hz1.2⟩

/-- **Oriented integer near-relation.** A coprime pair `(w,z)` drawn from `{a,b}` and
    exponents `p,q ≥ 1` with `z^p < w^q` yet `(w^q/z^p)^K < 3/2` (i.e. `2(w^q)^K < 3(z^p)^K`)
    — the multiplicative "small step" that seeds the band-count ladder. -/
theorem exists_int_step {a b : ℕ} (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ w z p q : ℕ, 2 ≤ w ∧ 2 ≤ z ∧ Nat.Coprime w z ∧
      (w = a ∧ z = b ∨ w = b ∧ z = a) ∧ 1 ≤ p ∧ 1 ≤ q ∧
      z ^ p < w ^ q ∧ 2 * (w ^ q) ^ K < 3 * (z ^ p) ^ K := by
  have hla : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha)
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set ε : ℝ := Real.log (3 / 2) / K with hεdef
  have hlog32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hεpos : 0 < ε := div_pos hlog32 hKR
  have hε_le : ε ≤ Real.log (3 / 2) := by
    rw [hεdef, div_le_iff₀ hKR]; nlinarith [hlog32, hK1R]
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have h32a : Real.log (3 / 2) < Real.log a := Real.log_lt_log (by norm_num) (by linarith)
  have h32b : Real.log (3 / 2) < Real.log b := Real.log_lt_log (by norm_num) (by linarith)
  have hεa : ε < Real.log a := lt_of_le_of_lt hε_le h32a
  have hεb : ε < Real.log b := lt_of_le_of_lt hε_le h32b
  obtain ⟨m, n, hpos, hlt⟩ := exists_small_combo hab ha hb hεpos
  have hcase : (1 ≤ m ∧ n ≤ -1) ∨ (m ≤ -1 ∧ 1 ≤ n) := by
    have hnotpp : ¬ (0 ≤ m ∧ 0 ≤ n) := by
      rintro ⟨hm, hn⟩
      have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm
      have hnR : (0 : ℝ) ≤ n := by exact_mod_cast hn
      rcases eq_or_lt_of_le hm with hm0 | hm1
      · rcases eq_or_lt_of_le hn with hn0 | hn1
        · rw [← hm0, ← hn0] at hpos; norm_num at hpos
        · have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          nlinarith [hlt, hεb, mul_nonneg hmR hla.le]
      · have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
        nlinarith [hlt, hεa, mul_nonneg hnR hlb.le]
    have hnotnn : ¬ (m ≤ 0 ∧ n ≤ 0) := by
      rintro ⟨hm, hn⟩
      have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast hm
      have hnR : (n : ℝ) ≤ 0 := by exact_mod_cast hn
      nlinarith [hpos, mul_nonpos_of_nonpos_of_nonneg hmR hla.le,
        mul_nonpos_of_nonpos_of_nonneg hnR hlb.le]
    rcases lt_trichotomy m 0 with hm | hm | hm
    · right; refine ⟨by omega, ?_⟩; by_contra hn; push_neg at hn; exact hnotnn ⟨by omega, by omega⟩
    · exfalso
      rcases le_or_gt n 0 with hn | hn
      · exact hnotnn ⟨by omega, hn⟩
      · exact hnotpp ⟨by omega, by omega⟩
    · left; refine ⟨by omega, ?_⟩; by_contra hn; push_neg at hn; exact hnotpp ⟨by omega, by omega⟩
  have key : ∀ (w z P Q : ℕ), 2 ≤ w → 2 ≤ z → 1 ≤ P → 1 ≤ Q →
      0 < (Q : ℝ) * Real.log w - (P : ℝ) * Real.log z →
      (Q : ℝ) * Real.log w - (P : ℝ) * Real.log z < ε →
      z ^ P < w ^ Q ∧ 2 * (w ^ Q) ^ K < 3 * (z ^ P) ^ K := by
    intro w z P Q hw hz hP hQ hgt hlt2
    have hzw : (z : ℝ) ^ P < (w : ℝ) ^ Q := by
      have hl : Real.log ((z : ℝ) ^ P) < Real.log ((w : ℝ) ^ Q) := by
        simp only [Real.log_pow]; linarith
      exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp hl
    refine ⟨by exact_mod_cast hzw, ?_⟩
    have hstep := mul_lt_mul_of_pos_left hlt2 hKR
    have hKε : (K : ℝ) * ε = Real.log (3 / 2) := by rw [hεdef]; field_simp
    rw [hKε, mul_sub] at hstep
    have hreal : 2 * ((w : ℝ) ^ Q) ^ K < 3 * ((z : ℝ) ^ P) ^ K := by
      have hloglt : Real.log (((w : ℝ) ^ Q) ^ K) < Real.log ((3 / 2) * ((z : ℝ) ^ P) ^ K) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
        simp only [Real.log_pow]
        linarith [hstep]
      have hlt3 : ((w : ℝ) ^ Q) ^ K < (3 / 2) * ((z : ℝ) ^ P) ^ K :=
        (Real.log_lt_log_iff (by positivity) (by positivity)).mp hloglt
      linarith
    have hcast : (2 * (w ^ Q) ^ K : ℝ) < (3 * (z ^ P) ^ K : ℝ) := by
      push_cast; push_cast at hreal; linarith
    exact_mod_cast hcast
  rcases hcase with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · have e1 : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ m)
    have e2 : ((-n).toNat : ℝ) = -(n : ℝ) := by
      have : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    refine ⟨a, b, (-n).toNat, m.toNat, ha, hb, hab, Or.inl ⟨rfl, rfl⟩, by omega, by omega, ?_⟩
    have hgt : 0 < (m.toNat : ℝ) * Real.log a - ((-n).toNat : ℝ) * Real.log b := by
      rw [e1, e2]; nlinarith [hpos]
    have hlt2 : (m.toNat : ℝ) * Real.log a - ((-n).toNat : ℝ) * Real.log b < ε := by
      rw [e1, e2]; nlinarith [hlt]
    exact key a b (-n).toNat m.toNat ha hb (by omega) (by omega) hgt hlt2
  · have e1 : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ n)
    have e2 : ((-m).toNat : ℝ) = -(m : ℝ) := by
      have : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    refine ⟨b, a, (-m).toNat, n.toNat, hb, ha, hab.symm, Or.inr ⟨rfl, rfl⟩, by omega, by omega, ?_⟩
    have hgt : 0 < (n.toNat : ℝ) * Real.log b - ((-m).toNat : ℝ) * Real.log a := by
      rw [e1, e2]; nlinarith [hpos]
    have hlt2 : (n.toNat : ℝ) * Real.log b - ((-m).toNat : ℝ) * Real.log a < ε := by
      rw [e1, e2]; nlinarith [hlt]
    exact key b a (-m).toNat n.toNat hb ha (by omega) (by omega) hgt hlt2

/-! ## Cell decomposition — the exact reduction of the LCLT minor arc

(ChatGPT/GPT-5 Pro adversarial round, 2026-07-16, independently referee-checked.) On any
"cell" of `[-1/2,1/2]` where the nearest integers `z_s` to `s·t` are constant, the energy
`Q(t) = Σ_{s∈B} ‖s·t‖² = Σ (s·t − z_s)²` is EXACTLY a parabola with curvature `S₂ = Σ s²`
and a nonnegative vertex height `A`. This turns the entire minor-arc bound into the single
summability inequality `Σ_cells e^{−2A_I} < (1−C_M)/π` — the precise remaining research
kernel (`uniform_cell_theta_bound`), which may require modular-distribution / linear-forms-
in-logs input and is NOT proved here. The curvature and nonnegativity below ARE proved. -/

/-- **Exact cell curvature.** With fixed nearest-integers `z`, the energy `Σ(s·t − z)²`
    equals the parabola `S₂·(t − θ)² + A`, `S₂ = Σ s²`, `θ = (Σ s·z)/S₂`,
    `A = Σ z² − (Σ s·z)²/S₂`. -/
theorem cell_quadratic {ι : Type*} (B : Finset ι) (s z : ι → ℝ)
    (hσ : (∑ i ∈ B, s i ^ 2) ≠ 0) (t : ℝ) :
    (∑ i ∈ B, (s i * t - z i) ^ 2)
      = (∑ i ∈ B, s i ^ 2) * (t - (∑ i ∈ B, s i * z i) / (∑ i ∈ B, s i ^ 2)) ^ 2
        + ((∑ i ∈ B, z i ^ 2) - (∑ i ∈ B, s i * z i) ^ 2 / (∑ i ∈ B, s i ^ 2)) := by
  have expand :
      (∑ i ∈ B, (s i * t - z i) ^ 2)
        = (∑ i ∈ B, s i ^ 2) * t ^ 2 - 2 * t * (∑ i ∈ B, s i * z i)
          + (∑ i ∈ B, z i ^ 2) := by
    rw [Finset.sum_congr rfl
      (fun i _ => show (s i * t - z i) ^ 2
        = s i ^ 2 * t ^ 2 - 2 * t * (s i * z i) + z i ^ 2 from by ring)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum]
  rw [expand]; field_simp; ring

/-- **Cell vertex height is nonnegative** (Cauchy–Schwarz): every cell parabola sits at or
    above the axis, so `A_I ≥ 0` and the minor-arc mass is a sum of Gaussians `e^{−2A_I}·…`. -/
theorem cell_A_nonneg {ι : Type*} (B : Finset ι) (s z : ι → ℝ)
    (hσ : 0 < ∑ i ∈ B, s i ^ 2) :
    0 ≤ (∑ i ∈ B, z i ^ 2) - (∑ i ∈ B, s i * z i) ^ 2 / (∑ i ∈ B, s i ^ 2) := by
  have hcs : (∑ i ∈ B, s i * z i) ^ 2 ≤ (∑ i ∈ B, s i ^ 2) * (∑ i ∈ B, z i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq B s z
  rw [sub_nonneg, div_le_iff₀ hσ]
  nlinarith [hcs]

section Bricks

variable {a b c : ℕ}

/-! ## §1 — the band and its antichain property -/

/-- Membership unfolding for the band. -/
theorem mem_Band {x s : ℕ} :
    s ∈ Band a b c x ↔ s ∈ Smooth3 a b c ∧ x ≤ s ∧ 2 * s < 3 * x := by
  unfold Band
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨by omega, h⟩

/-- The band is a divisibility antichain — a width-3/2 window cannot contain a
    divisor pair, whose ratio is at least 2. No arithmetic input needed. -/
theorem band_primitive (x : ℕ) : IsPrimitive (Band a b c x) := by
  intro u hu v hv hne hdvd
  obtain ⟨-, hux, hu3⟩ := mem_Band.mp hu
  obtain ⟨-, hvx, hv3⟩ := mem_Band.mp hv
  obtain ⟨q, rfl⟩ := hdvd
  have hq2 : 2 ≤ q := by
    rcases q with _ | _ | q
    · simp only [Nat.mul_zero] at hvx hv3
      omega
    · exact absurd (Nat.mul_one u).symm hne
    · omega
  have hmul : u * 2 ≤ u * q := Nat.mul_le_mul_left u hq2
  linarith [hmul, hvx, hv3, hux, hu3]

/-- Primitivity is hereditary. -/
theorem IsPrimitive.subset {s t : Finset ℕ} (h : IsPrimitive t) (hst : s ⊆ t) :
    IsPrimitive s :=
  fun _ hx _ hy hne => h (hst hx) (hst hy) hne

/-! ## §2 — band population (OPEN brick: the effective lower bound) -/

/-- Bernoulli-type: `s^(t+1) ≤ r^t` once `t ≥ s²`, for `2 ≤ s < r`. -/
theorem pow_succ_le_pow {s r : ℕ} (hs : 2 ≤ s) (hsr : s + 1 ≤ r) {t : ℕ} (ht : s * s ≤ t) :
    s ^ (t + 1) ≤ r ^ t := by
  have hsp : (0 : ℝ) < s := by positivity
  have hB : (1 : ℝ) + (t : ℝ) * (1 / s) ≤ (1 + 1 / s) ^ t :=
    one_add_mul_le_pow (le_trans (by norm_num : (-2:ℝ) ≤ 0) (by positivity)) t
  have hst : (0 : ℝ) < (s : ℝ) ^ t := by positivity
  have hts : (s : ℝ) * ((s : ℝ) - 1) ≤ (t : ℝ) := by
    have : ((s * s : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    push_cast at this; nlinarith [this]
  have hLHS : (s : ℝ) ^ (t + 1) ≤ (s : ℝ) ^ t * (1 + t * (1 / s)) := by
    rw [pow_succ]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hst)
    rw [mul_one_div]
    have hd : (s : ℝ) - 1 ≤ (t : ℝ) / s := by rw [le_div_iff₀ hsp]; nlinarith [hts]
    linarith
  have hRHS : (s : ℝ) ^ t * (1 + 1 / s) ^ t = ((s : ℝ) + 1) ^ t := by
    rw [← mul_pow]; congr 1; field_simp
  have hmul : (s : ℝ) ^ t * (1 + t * (1 / s)) ≤ (s : ℝ) ^ t * (1 + 1 / s) ^ t :=
    mul_le_mul_of_nonneg_left hB (le_of_lt hst)
  have hchain : (s : ℝ) ^ (t + 1) ≤ ((s : ℝ) + 1) ^ t := by rw [← hRHS]; linarith
  have hfin : ((s : ℝ) + 1) ^ t ≤ (r : ℝ) ^ t := by
    have hsr' : (s : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hsr
    exact pow_le_pow_left₀ (by positivity) hsr' t
  have : (s : ℝ) ^ (t + 1) ≤ (r : ℝ) ^ t := le_trans hchain hfin
  exact_mod_cast this

/-- **Band-count ladder.** Given the multiplicative step (`z^p < w^q` but the ratio's
    `K`-th power `< 3/2`), the band eventually has `≥ K` elements — the geometric ladder
    `E j = (w^q)^j (z^p)^(N-j)` steps by a factor `< (3/2)^{1/K}`, so `K` consecutive
    elements fit in `[x, 3x/2)`. `hmem` supplies Smooth3 membership of the `(w,z)` submonoid. -/
theorem ladder_count {w z p q K : ℕ}
    (hz : 2 ≤ z) (hp : 1 ≤ p) (hq : 1 ≤ q) (hK : 1 ≤ K)
    (hlt : z ^ p < w ^ q) (hratio : 2 * (w ^ q) ^ K < 3 * (z ^ p) ^ K)
    (hmem : ∀ i j : ℕ, w ^ i * z ^ j ∈ Smooth3 a b c) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → K ≤ (Band a b c x).card := by
  set r : ℕ := w ^ q with hrdef
  set s : ℕ := z ^ p with hsdef
  have hs2 : 2 ≤ s := le_trans hz (by rw [hsdef]; exact Nat.le_self_pow (by omega) z)
  have hsr : s < r := hlt
  have hsr1 : s + 1 ≤ r := hsr
  have hs0 : 0 < s := by omega
  have hr0 : 0 < r := by omega
  set E : ℕ → ℕ → ℕ := fun N j => r ^ j * s ^ (N - j) with hEdef
  have hEpos : ∀ N j, 0 < E N j := fun N j => by simp only [hEdef]; positivity
  have hEmem : ∀ N j, E N j ∈ Smooth3 a b c := by
    intro N j
    simp only [hEdef, hrdef, hsdef, ← pow_mul]
    exact hmem (q * j) (p * (N - j))
  have hIter : ∀ N j i, j + i ≤ N → E N j * r ^ i = E N (j + i) * s ^ i := by
    intro N j i hji
    simp only [hEdef]
    rw [mul_right_comm, ← pow_add, mul_assoc, ← pow_add]
    congr 2 <;> omega
  have hMono : ∀ N j, j + 1 ≤ N → E N j < E N (j + 1) := by
    intro N j hj
    have hrec : E N j * r = E N (j + 1) * s := by
      have := hIter N j 1 (by omega); simpa using this
    have h1 : E N j * s < E N (j + 1) * s := by
      calc E N j * s < E N j * r := mul_lt_mul_of_pos_left hsr (hEpos N j)
        _ = E N (j + 1) * s := hrec
    exact lt_of_mul_lt_mul_right h1 (Nat.zero_le s)
  have hMono' : ∀ N j j', j ≤ j' → j' ≤ N → E N j ≤ E N j' := by
    intro N j j' hjj hj'
    induction j' with
    | zero => exact le_of_eq (by rw [Nat.le_zero.mp hjj])
    | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact le_trans (ih (by omega) (by omega)) (le_of_lt (hMono N k (by omega)))
      · have : j = k + 1 := by omega
        rw [this]
  have hStrict : ∀ N j j', j < j' → j' ≤ N → E N j < E N j' := by
    intro N j j' hjj hj'
    calc E N j < E N (j + 1) := hMono N j (by omega)
      _ ≤ E N j' := hMono' N (j + 1) j' (by omega) hj'
  set m2 : ℕ := s * s with hm2
  refine ⟨s ^ (2 * m2 + K), fun x hxX0 => ?_⟩
  have hx1 : 1 ≤ x := le_trans (Nat.one_le_two_pow.trans (by
    exact Nat.pow_le_pow_left (by omega) _)) hxX0
  have hx0 : 0 < x := hx1
  set N : ℕ := Nat.log s x with hNdef
  have hsN : s ^ N ≤ x := Nat.pow_log_le_self s (by omega)
  have hxlt : x < s ^ (N + 1) := Nat.lt_pow_succ_log_self (by omega) x
  have hNbig : 2 * m2 + K ≤ N := Nat.le_log_of_pow_le (by omega) hxX0
  have hKN : K ≤ N := by omega
  have htbig : s * s ≤ N - K + 1 := by rw [← hm2]; omega
  have hbigmid : x ≤ E N (N - K + 1) := by
    have hchain : s ^ (N + 1) ≤ E N (N - K + 1) := by
      have hEval : E N (N - K + 1) = r ^ (N - K + 1) * s ^ (K - 1) := by
        simp only [hEdef]; congr 2; omega
      rw [hEval]
      have hsplit : s ^ (N + 1) = s ^ (N - K + 1 + 1) * s ^ (K - 1) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit]
      exact Nat.mul_le_mul_right _ (pow_succ_le_pow hs2 hsr1 htbig)
    omega
  have hex : ∃ j, x ≤ E N j := ⟨N - K + 1, hbigmid⟩
  classical
  set J : ℕ := Nat.find hex with hJdef
  have hJspec : x ≤ E N J := Nat.find_spec hex
  have hJle : J ≤ N - K + 1 := Nat.find_le hbigmid
  have hJmin : ∀ j, j < J → E N j < x := by
    intro j hj; have := Nat.find_min hex hj; omega
  have hJsr : E N J * s < x * r := by
    rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
    · have hE0 : E N J = s ^ N := by rw [hJ0]; simp only [hEdef]; simp
      rw [hE0]
      calc s ^ N * s ≤ x * s := Nat.mul_le_mul_right _ hsN
        _ < x * r := mul_lt_mul_of_pos_left hsr hx0
    · have hjm1 : E N (J - 1) < x := hJmin (J - 1) (by omega)
      have hrec : E N (J - 1) * r = E N J * s := by
        have := hIter N (J - 1) 1 (by omega)
        rw [show J - 1 + 1 = J by omega] at this; simpa using this
      calc E N J * s = E N (J - 1) * r := hrec.symm
        _ ≤ (x - 1) * r := Nat.mul_le_mul_right _ (by omega)
        _ < x * r := mul_lt_mul_of_pos_right (by omega) hr0
  have hsK : s ^ K = s ^ (K - 1) * s := by rw [← pow_succ]; congr 1; omega
  have hrK : r ^ K = r ^ (K - 1) * r := by rw [← pow_succ]; congr 1; omega
  have fA : E N (J + K - 1) * s ^ (K - 1) = E N J * r ^ (K - 1) := by
    have hI := hIter N J (K - 1) (by omega)
    rw [show J + (K - 1) = J + K - 1 by omega] at hI
    exact hI.symm
  have hbig : 2 * E N (J + K - 1) * s ^ K < 3 * x * s ^ K := by
    calc 2 * E N (J + K - 1) * s ^ K
        = 2 * (E N (J + K - 1) * s ^ (K - 1)) * s := by rw [hsK]; ring
      _ = 2 * (E N J * r ^ (K - 1)) * s := by rw [fA]
      _ = (E N J * s) * (2 * r ^ (K - 1)) := by ring
      _ < (x * r) * (2 * r ^ (K - 1)) := mul_lt_mul_of_pos_right hJsr (by positivity)
      _ = x * (2 * r ^ K) := by rw [hrK]; ring
      _ < x * (3 * s ^ K) := mul_lt_mul_of_pos_left hratio hx0
      _ = 3 * x * s ^ K := by ring
  have hupper : 2 * E N (J + K - 1) < 3 * x :=
    lt_of_mul_lt_mul_right hbig (Nat.zero_le _)
  have hmaps : ∀ i ∈ Finset.range K, E N (J + i) ∈ Band a b c x := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [mem_Band]
    refine ⟨hEmem N (J + i), le_trans hJspec (hMono' N J (J + i) (by omega) (by omega)), ?_⟩
    have hle : E N (J + i) ≤ E N (J + K - 1) := hMono' N (J + i) (J + K - 1) (by omega) (by omega)
    omega
  have hinj : Set.InjOn (fun i => E N (J + i)) (Finset.range K) := by
    intro i hi i' hi' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd heq (ne_of_lt (hStrict N (J + i) (J + i') (by omega) (by omega)))
    · exact h
    · exact absurd heq.symm (ne_of_lt (hStrict N (J + i') (J + i) (by omega) (by omega)))
  have hcard := Finset.card_le_card_of_injOn (fun i => E N (J + i)) hmaps hinj
  rwa [Finset.card_range] at hcard

/-- **Band population grows without bound** (effective, via multiplicative independence):
    for every `K`, the band `B_x` eventually has at least `K` elements. -/
theorem band_card_eventually_ge (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (K : ℕ) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → K ≤ (Band a b c x).card := by
  rcases Nat.eq_zero_or_pos K with hK0 | hK
  · exact ⟨0, fun x _ => by rw [hK0]; exact Nat.zero_le _⟩
  obtain ⟨w, z, p, q, hw, hz, hwz, horient, hp, hq, hlt, hratio⟩ :=
    exists_int_step hco.1 (by omega) (by omega) K hK
  have hmem : ∀ i j : ℕ, w ^ i * z ^ j ∈ Smooth3 a b c := by
    intro i j
    rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨i, j, 0, by simp⟩
    · exact ⟨j, i, 0, by ring⟩
  exact ladder_count hz hp hq hK hlt hratio hmem

/-! ## §3 — the local-CLT kernel bounds (proven) and the core (OPEN brick) -/

/-- Chord identity: `‖1 + e(α)‖ = 2·|cos(πα)|`. -/
lemma one_add_e_norm (α : ℝ) : ‖1 + e α‖ = 2 * |Real.cos (Real.pi * α)| := by
  have harg : e α = Complex.exp ((↑(2 * Real.pi * α) : ℂ) * Complex.I) := by
    rw [e]; congr 1; push_cast; ring
  have hre : (e α).re = Real.cos (2 * Real.pi * α) := by
    rw [harg]; exact Complex.exp_ofReal_mul_I_re _
  have him : (e α).im = Real.sin (2 * Real.pi * α) := by
    rw [harg]; exact Complex.exp_ofReal_mul_I_im _
  have e1 : Real.cos (2 * Real.pi * α) = 2 * Real.cos (Real.pi * α) ^ 2 - 1 := by
    rw [show 2 * Real.pi * α = 2 * (Real.pi * α) by ring]; exact Real.cos_two_mul _
  have e2 : Real.sin (2 * Real.pi * α)
      = 2 * Real.sin (Real.pi * α) * Real.cos (Real.pi * α) := by
    rw [show 2 * Real.pi * α = 2 * (Real.pi * α) by ring]; exact Real.sin_two_mul _
  have hnn : (0 : ℝ) ≤ 2 * |Real.cos (Real.pi * α)| := by positivity
  rw [← Real.sqrt_sq (norm_nonneg (1 + e α)), ← Real.sqrt_sq hnn]
  congr 1
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, hre, him]
  rw [e1, e2, mul_pow, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * α)]

/-- The exact factorisation `1 + e(α) = 2 cos(πα) · e(α/2)` (Euler), for all real `α`.
    Over the band this gives `∏(1+e(st)) = 2^{|B|}·(∏cos πst)·e(S₁t/2)` — the major-arc entry point. -/
lemma one_add_e_eq (α : ℝ) :
    1 + e α = 2 * (Real.cos (Real.pi * α) : ℂ) * e (α / 2) := by
  have h1 : e (α / 2) = Complex.exp (↑(Real.pi * α) * Complex.I) := by
    rw [e]; congr 1; push_cast; ring
  have hcos : (Real.cos (Real.pi * α) : ℂ)
      = (Complex.exp (↑(Real.pi * α) * Complex.I)
          + Complex.exp (-(↑(Real.pi * α) * Complex.I))) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos]; ring_nf
  have hsq : Complex.exp (↑(Real.pi * α) * Complex.I)
      * Complex.exp (↑(Real.pi * α) * Complex.I) = e α := by
    rw [← Complex.exp_add, e]; congr 1; push_cast; ring
  have hcancel : Complex.exp (-(↑(Real.pi * α) * Complex.I))
      * Complex.exp (↑(Real.pi * α) * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  rw [hcos, h1,
    show (2 : ℂ) * ((Complex.exp (↑(Real.pi * α) * Complex.I)
          + Complex.exp (-(↑(Real.pi * α) * Complex.I))) / 2)
        * Complex.exp (↑(Real.pi * α) * Complex.I)
      = Complex.exp (↑(Real.pi * α) * Complex.I) * Complex.exp (↑(Real.pi * α) * Complex.I)
        + Complex.exp (-(↑(Real.pi * α) * Complex.I)) * Complex.exp (↑(Real.pi * α) * Complex.I) by
      ring]
  rw [hsq, hcancel]; ring

/-- Jordan bound through the half angle: `u² ≤ sin(π·(u/2))²` for `|u| ≤ 1/2`. -/
lemma sin_sq_half_ge (u : ℝ) (hu : |u| ≤ 1 / 2) :
    u ^ 2 ≤ Real.sin (Real.pi * (u / 2)) ^ 2 := by
  have h1 : |u| ≤ Real.sin (Real.pi / 2 * |u|) :=
    Real.le_sin_mul (abs_nonneg u) (by linarith)
  have h2 : Real.sin (Real.pi / 2 * |u|) ^ 2 = Real.sin (Real.pi * (u / 2)) ^ 2 := by
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h, show Real.pi / 2 * u = Real.pi * (u / 2) by ring]
    · rw [h, show Real.pi / 2 * -u = -(Real.pi * (u / 2)) by ring, Real.sin_neg]
      ring
  calc u ^ 2 = |u| ^ 2 := (sq_abs u).symm
    _ ≤ Real.sin (Real.pi / 2 * |u|) ^ 2 := by nlinarith [abs_nonneg u]
    _ = Real.sin (Real.pi * (u / 2)) ^ 2 := h2

/-- The minor-arc kernel bound: `|cos(π y)| ≤ exp(−2·(y − round y)²)`. -/
lemma abs_cos_le_exp (y : ℝ) :
    |Real.cos (Real.pi * y)| ≤ Real.exp (-(2 * (y - round y) ^ 2)) := by
  set m : ℤ := round y with hm
  set u : ℝ := y - (m : ℝ) with hu
  have huabs : |u| ≤ 1 / 2 := by rw [hu, hm]; exact abs_sub_round y
  have hsplit : Real.pi * y = Real.pi * u + (m : ℝ) * Real.pi := by rw [hu]; ring
  have hper : |Real.cos (Real.pi * y)| = |Real.cos (Real.pi * u)| := by
    rw [hsplit, Real.cos_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one,
      one_zpow, one_mul]
  have hhalf : Real.cos (Real.pi * u) = 1 - 2 * Real.sin (Real.pi * (u / 2)) ^ 2 := by
    have hd : Real.cos (2 * (Real.pi * (u / 2)))
        = 2 * Real.cos (Real.pi * (u / 2)) ^ 2 - 1 := Real.cos_two_mul _
    have harg : Real.pi * u = 2 * (Real.pi * (u / 2)) := by ring
    rw [harg, hd]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (u / 2))]
  have hnn : 0 ≤ Real.cos (Real.pi * u) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith [Real.pi_pos, (abs_le.mp huabs).1]
    · nlinarith [Real.pi_pos, (abs_le.mp huabs).2]
  have hsin := sin_sq_half_ge u huabs
  have hchain : |Real.cos (Real.pi * u)| ≤ 1 - 2 * u ^ 2 := by
    rw [abs_of_nonneg hnn, hhalf]
    linarith
  have hexp : 1 - 2 * u ^ 2 ≤ Real.exp (-(2 * u ^ 2)) := by
    have := Real.add_one_le_exp (-(2 * u ^ 2))
    linarith
  rw [hper]
  exact le_trans hchain hexp

/-! ### Anton's route — the energy `Q`, the χ-majorant, and the low-energy set `E_x(z)`

The minor-arc integrand is `χ(t) = ∏_{s∈B}|cos π s t|`; Anton's Prop 5.1 bounds the measure of
the low-energy set `{t : Q_x(t) ≤ z}`, and `χ ≤ exp(−2Q)` (B1, below) turns that measure bound
into the minor-arc integral bound (Lemma 4). `Qenergy`/`chiBand` are defined here; Prop 5.1 is the
research-scale core (grid embedding + tripod routing + gcd rigidity) — see
`paper/ANTON-ROUTE-LEAN-ROADMAP.md`. -/

/-- The energy `Q_x(t) = ∑_{s∈B_x} ‖s t‖²` (distance-to-nearest-integer, squared). -/
noncomputable def Qenergy (a b c x : ℕ) (t : ℝ) : ℝ :=
  ∑ s ∈ Band a b c x, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2

/-- The characteristic-function modulus `χ(t) = ∏_{s∈B_x}|cos(π s t)|` = `|E e(Y_x t)|` —
    the honest minor-arc integrand. -/
noncomputable def chiBand (a b c x : ℕ) (t : ℝ) : ℝ :=
  ∏ s ∈ Band a b c x, |Real.cos (Real.pi * ((s : ℝ) * t))|

/-- `Q_x` is nonnegative. -/
lemma Qenergy_nonneg (a b c x : ℕ) (t : ℝ) : 0 ≤ Qenergy a b c x t :=
  Finset.sum_nonneg (fun s _ => sq_nonneg _)

/-- `χ_x` is nonnegative. -/
lemma chiBand_nonneg (a b c x : ℕ) (t : ℝ) : 0 ≤ chiBand a b c x t :=
  Finset.prod_nonneg (fun s _ => abs_nonneg _)

/-- `round : ℝ → ℤ` is measurable (`round x = ⌊x + 1/2⌋`). -/
lemma measurable_round_real : Measurable (round : ℝ → ℤ) := by
  have h : (round : ℝ → ℤ) = fun x => ⌊x + 1 / 2⌋ := funext round_eq
  rw [h]
  exact Int.measurable_floor.comp (measurable_id.add measurable_const)

/-- `Q_x` is measurable (finite sum of squared measurable sawtooths; `round` is measurable). -/
lemma Qenergy_measurable (a b c x : ℕ) : Measurable (Qenergy a b c x) := by
  unfold Qenergy
  refine Finset.measurable_sum _ (fun s _ => ?_)
  have hst : Measurable (fun t : ℝ => (s : ℝ) * t) := measurable_const.mul measurable_id
  have hround : Measurable (fun t : ℝ => ((round ((s : ℝ) * t) : ℤ) : ℝ)) :=
    (measurable_of_countable _).comp (measurable_round_real.comp hst)
  exact (hst.sub hround).pow_const 2

/-- `exp(−2 Q_x)` is interval-integrable (bounded by 1, measurable). Layer-cake prerequisite. -/
lemma exp_neg_two_Q_intervalIntegrable (a b c x : ℕ) (u v : ℝ) :
    IntervalIntegrable (fun t => Real.exp (-(2 * Qenergy a b c x t)))
      MeasureTheory.volume u v := by
  rw [intervalIntegrable_iff]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    ((Real.measurable_exp.comp
      ((Qenergy_measurable a b c x).const_mul 2).neg)).aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ (fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  calc Real.exp (-(2 * Qenergy a b c x t))
      ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith [Qenergy_nonneg a b c x t])
    _ = 1 := Real.exp_zero

/-- **B1 — the Gaussian majorant** `χ(t) ≤ exp(−2 Q_x(t))`, from the pointwise
    `|cos π y| ≤ exp(−2‖y‖²)` (`abs_cos_le_exp`) multiplied over the band. -/
lemma chi_le_exp_neg_two_Q (a b c x : ℕ) (t : ℝ) :
    chiBand a b c x t ≤ Real.exp (-(2 * Qenergy a b c x t)) := by
  have hle : chiBand a b c x t
      ≤ ∏ s ∈ Band a b c x, Real.exp (-(2 * ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2)) :=
    Finset.prod_le_prod (fun s _ => abs_nonneg _)
      (fun s _ => abs_cos_le_exp ((s : ℝ) * t))
  refine hle.trans (le_of_eq ?_)
  rw [← Real.exp_sum]
  congr 1
  have hpt : ∀ s ∈ Band a b c x,
      (-(2 * ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2))
        = (-2 : ℝ) * ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 := fun s _ => by ring
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, Qenergy]
  ring

/-- `χ_x` is continuous (finite product of `|cos|`-compositions). -/
lemma chiBand_continuous (a b c x : ℕ) : Continuous (chiBand a b c x) := by
  unfold chiBand; fun_prop

/-- `χ_x` is interval-integrable on any interval (continuous). -/
lemma chiBand_intervalIntegrable (a b c x : ℕ) (u v : ℝ) :
    IntervalIntegrable (chiBand a b c x) MeasureTheory.volume u v :=
  (chiBand_continuous a b c x).intervalIntegrable u v

/-- The minor-arc integrand modulus: `∏_{s∈B}‖1 + e(s t)‖ = 2^{|B|}·χ_x(t)` (from
    `one_add_e_norm`, `‖1 + e α‖ = 2|cos πα|`). This is how `χ` enters the subset-sum count. -/
lemma prod_abs_one_add_e (a b c x : ℕ) (t : ℝ) :
    (∏ s ∈ Band a b c x, ‖1 + e ((s : ℝ) * t)‖)
      = 2 ^ (Band a b c x).card * chiBand a b c x t := by
  rw [chiBand, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun s _ => one_add_e_norm ((s : ℝ) * t))

/-- `e` is continuous (`exp` of an affine map). -/
@[fun_prop]
lemma continuous_e : Continuous e := by
  unfold e; exact Complex.continuous_exp.comp (by fun_prop)

/-- `‖e x‖ = 1` (the unit character `e(x)=exp(2πix)`). -/
lemma e_norm (x : ℝ) : ‖e x‖ = 1 := by
  rw [e, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  rw [hre, Real.exp_zero]

/-- **Minor-arc modulus bound.** Over any set `S`, the subset-sum integrand's integral is
    bounded by `2^{|B|}·∫_S χ` (triangle inequality for integrals + `prod_abs_one_add_e` + `‖e‖=1`).
    Feeds the circle-method assembly's minor-arc estimate (`|Re ∫_𝔪| ≤ ‖∫_𝔪‖ ≤ 2^{|B|}∫_𝔪 χ`). -/
lemma norm_setIntegral_prod_le (a b c x n : ℕ) (S : Set ℝ) :
    ‖∫ t in S, (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))‖
      ≤ 2 ^ (Band a b c x).card * ∫ t in S, chiBand a b c x t := by
  calc ‖∫ t in S, (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))‖
      ≤ ∫ t in S, ‖(∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t in S, 2 ^ (Band a b c x).card * chiBand a b c x t := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        dsimp only
        rw [norm_mul, e_norm, mul_one, norm_prod, prod_abs_one_add_e]
    _ = 2 ^ (Band a b c x).card * ∫ t in S, chiBand a b c x t :=
        MeasureTheory.integral_const_mul _ _

/-- Major arc in `Ioc 0 1`: `t` within `1/(8x)` of `0` or `1`. -/
def MajorArc (x : ℕ) : Set ℝ :=
  {t | t ∈ Set.Ioc (0 : ℝ) 1 ∧ (t ≤ 1 / (8 * (x : ℝ)) ∨ 1 - 1 / (8 * (x : ℝ)) ≤ t)}

/-- Minor arc: `Ioc 0 1` minus the major arc. -/
def MinorArc (x : ℕ) : Set ℝ := Set.Ioc (0 : ℝ) 1 \ MajorArc x

/-! ### Fourier subset-sum inversion (the circle-method entry point for `Main.lclt_coverage'`) -/

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp only [e]; rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `∫₀¹ e(k t) dt = [k = 0]` (character orthogonality). -/
lemma integral_e (k : ℤ) :
    ∫ t in (0:ℝ)..1, e ((k : ℝ) * t) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl]
    have hcong : ∀ t ∈ Set.uIcc (0:ℝ) 1, e (((0 : ℤ) : ℝ) * t) = 1 := by
      intro t _; simp only [Int.cast_zero, zero_mul]; simp [e]
    rw [intervalIntegral.integral_congr hcong, intervalIntegral.integral_const]; norm_num
  · rw [if_neg hk]
    set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) with hc
    have hcne : c ≠ 0 := by
      rw [hc]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hk)
    have hexpc : Complex.exp c = 1 := by
      rw [hc, Complex.exp_eq_one_iff]; exact ⟨k, by ring⟩
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun t : ℝ => Complex.exp (c * ↑t) / c) (e ((k : ℝ) * t)) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => c * (↑t : ℂ)) c t := by
        simpa using (Complex.ofRealCLM.hasDerivAt).const_mul c
      have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * ↑t)) (Complex.exp (c * ↑t) * c) t := h1.cexp
      have h3 := h2.div_const c
      rw [mul_div_assoc, div_self hcne, mul_one] at h3
      have hval : e ((k : ℝ) * t) = Complex.exp (c * ↑t) := by rw [e, hc]; push_cast; ring_nf
      rw [hval]; exact h3
    have hcont : IntervalIntegrable (fun t : ℝ => e ((k : ℝ) * t)) MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable; unfold e; fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
    rw [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, hexpc]; ring

/-- `∏_{s∈T} e(s t) = e((Σ_{s∈T} s) t)`. -/
lemma prod_e (T : Finset ℕ) (t : ℝ) :
    (∏ s ∈ T, e ((s : ℝ) * t)) = e (((∑ s ∈ T, s : ℕ) : ℝ) * t) := by
  induction T using Finset.induction with
  | empty => simp [e]
  | @insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← e_add]
    congr 1; push_cast; ring

/-- **Fourier subset-sum inversion.** The number of subsets of `B` summing to `n` is the
    `n`-th Fourier coefficient of `∏(1 + e(s·t))` — the counting identity underlying the
    circle-method form of `Main.lclt_coverage'`. -/
theorem subsetSum_fourier (B : Finset ℕ) (n : ℕ) :
    (∫ t in (0:ℝ)..1, (∏ s ∈ B, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))
      = ((B.powerset.filter (fun T => ∑ s ∈ T, s = n)).card : ℂ) := by
  have hintegrand : ∀ t : ℝ,
      (∏ s ∈ B, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))
        = ∑ T ∈ B.powerset, e ((((∑ s ∈ T, s : ℕ) : ℤ) - n : ℝ) * t) := by
    intro t
    have hprod : (∏ s ∈ B, (1 + e ((s : ℝ) * t)))
        = ∑ T ∈ B.powerset, e (((∑ s ∈ T, s : ℕ) : ℝ) * t) := by
      have hcomm : (∏ s ∈ B, (1 + e ((s : ℝ) * t))) = ∏ s ∈ B, (e ((s : ℝ) * t) + 1) := by
        simp only [add_comm]
      rw [hcomm, Finset.prod_add]
      apply Finset.sum_congr rfl
      intro T _
      rw [Finset.prod_const_one, mul_one, prod_e]
    rw [hprod, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T _
    rw [← e_add]; congr 1; push_cast; ring
  rw [intervalIntegral.integral_congr (fun t _ => hintegrand t)]
  rw [intervalIntegral.integral_finset_sum]
  · have hterm : ∀ T ∈ B.powerset,
        (∫ t in (0:ℝ)..1, e ((((∑ s ∈ T, s : ℕ) : ℤ) - n : ℝ) * t))
          = if (∑ s ∈ T, s) = n then (1 : ℂ) else 0 := by
      intro T _
      have h := integral_e (((∑ s ∈ T, s : ℕ) : ℤ) - n)
      rw [show ((((∑ s ∈ T, s : ℕ) : ℤ) - n : ℝ)) = ((((∑ s ∈ T, s : ℕ) : ℤ) - n : ℤ) : ℝ) by
        push_cast; ring] at *
      rw [h]
      congr 1
      simp only [eq_iff_iff]
      constructor <;> intro hh <;> omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  · intro T _
    apply Continuous.intervalIntegrable; unfold e; fun_prop

/-! ### Circle-method arcs + the major/minor split

These are the shared arc definitions and the pointwise/integrability bricks consumed by the
coverage assembly, which lives in `Erdos123/Main.lean` as `lclt_coverage'`. That assembly closes
the standard circle-method gap: the major-arc real part is `≥ 2^{|B|}/(C₅·x·log x)`
(`MajorArcLB.major_arc_lower'`, proved), while the minor-arc error `2^{|B|}∫_𝔪 χ` is strictly
smaller (`Main.minor_arc_bound'`, proved from `Rigidity.lemma_5_2'` + `LowEnergy.low_energy_measure`).
Nothing in this section is conditional on anything. -/

/-- `MajorArc` is measurable (`Ioc 0 1 ∩ (Iic ε ∪ Ici (1−ε))`). -/
lemma measurableSet_MajorArc (x : ℕ) : MeasurableSet (MajorArc x) := by
  have heq : MajorArc x = Set.Ioc (0 : ℝ) 1 ∩
      (Set.Iic (1 / (8 * (x : ℝ))) ∪ Set.Ici (1 - 1 / (8 * (x : ℝ)))) := by
    ext t; simp only [MajorArc, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union,
      Set.mem_Iic, Set.mem_Ici]
  rw [heq]; exact measurableSet_Ioc.inter (measurableSet_Iic.union measurableSet_Ici)

/-- `MinorArc` is measurable. -/
lemma measurableSet_MinorArc (x : ℕ) : MeasurableSet (MinorArc x) :=
  measurableSet_Ioc.diff (measurableSet_MajorArc x)

/-- **Lemma 4, step 1:** `∫_𝔪 χ ≤ ∫_𝔪 exp(−2Q)` (B1 pointwise + integrability). USEFUL on the
    minor arc precisely because the major arc — where `exp(−2Q)≈1` dominates — is excluded. The
    remaining step is the layer-cake bound on `∫_𝔪 exp(−2Q)` from `LowEnergy.low_energy_measure`
    + `Rigidity.lemma_5_2'` (both proved). -/
lemma integral_chi_le_exp_on_minor (a b c x : ℕ) :
    (∫ t in MinorArc x, chiBand a b c x t)
      ≤ ∫ t in MinorArc x, Real.exp (-(2 * Qenergy a b c x t)) := by
  have hmm : MinorArc x ⊆ Set.Ioc (0 : ℝ) 1 := Set.diff_subset
  have hχ : MeasureTheory.IntegrableOn (chiBand a b c x) (MinorArc x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (chiBand_intervalIntegrable a b c x 0 1))).mono_set hmm
  have hexp : MeasureTheory.IntegrableOn (fun t => Real.exp (-(2 * Qenergy a b c x t)))
      (MinorArc x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (exp_neg_two_Q_intervalIntegrable a b c x 0 1))).mono_set hmm
  exact MeasureTheory.setIntegral_mono_on hχ hexp (measurableSet_MinorArc x)
    (fun t _ => chi_le_exp_neg_two_Q a b c x t)

/-- **Lemma 4, step 2 (layer-cake):** `∫_𝔪 exp(−2Q) = ∫_{level∈(0,1]} vol_𝔪{exp(−2Q) ≥ level}`,
    Cavalieri over the bounded nonnegative integrand `exp(−2Q) ≤ 1`. -/
lemma exp_layercake_on_minor (a b c x : ℕ) :
    (∫ t in MinorArc x, Real.exp (-(2 * Qenergy a b c x t)))
      = ∫ level in Set.Ioc (0 : ℝ) 1,
          (MeasureTheory.volume.restrict (MinorArc x)).real
            {t | level ≤ Real.exp (-(2 * Qenergy a b c x t))} := by
  have hint : MeasureTheory.IntegrableOn (fun t => Real.exp (-(2 * Qenergy a b c x t)))
      (MinorArc x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (exp_neg_two_Q_intervalIntegrable a b c x 0 1))).mono_set Set.diff_subset
  exact hint.integral_eq_integral_Ioc_meas_le
    (MeasureTheory.ae_of_all _ (fun t => Real.exp_nonneg _))
    (MeasureTheory.ae_of_all _ (fun t => by
      calc Real.exp (-(2 * Qenergy a b c x t)) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (by nlinarith [Qenergy_nonneg a b c x t])
        _ = 1 := Real.exp_zero))

/-- **Crude band-count upper bound** `|B_x| ≤ (log₂(2x)+1)³` — the band injects into the exponent
    box `[0,K]³` (each of `k,ℓ,m ≤ log₂(2x)` since `2^k ≤ a^k ≤ s < 2x`). Feeds the `S2 ≤ polylog·x²`
    estimate in `Main.minor_arc_bound'`. -/
lemma band_card_upper (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (x : ℕ) :
    (Band a b c x).card ≤ (Nat.log 2 (2 * x) + 1) ^ 3 := by
  set K := Nat.log 2 (2 * x) with hK
  have hsub : Band a b c x ⊆
      Finset.image (fun p : ℕ × ℕ × ℕ => a ^ p.1 * b ^ p.2.1 * c ^ p.2.2)
        (Finset.range (K + 1) ×ˢ Finset.range (K + 1) ×ˢ Finset.range (K + 1)) := by
    intro s hs
    obtain ⟨⟨k, l, m, hklm⟩, hxs, h2s⟩ := mem_Band.mp hs
    have hs2x : s < 2 * x := by omega
    have hbpos : 0 < b ^ l := pow_pos (by omega) l
    have hcpos : 0 < c ^ m := pow_pos (by omega) m
    have hapos : 0 < a ^ k := pow_pos (by omega) k
    have hak : a ^ k ≤ s := by
      rw [hklm, mul_assoc]; exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hbpos hcpos)
    have hbl : b ^ l ≤ s := by
      rw [hklm]; calc b ^ l ≤ a ^ k * b ^ l := Nat.le_mul_of_pos_left _ hapos
        _ ≤ a ^ k * b ^ l * c ^ m := Nat.le_mul_of_pos_right _ hcpos
    have hcm : c ^ m ≤ s := by
      rw [hklm]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hapos hbpos)
    have hbound : ∀ d e : ℕ, 2 ≤ d → d ^ e ≤ s → e ≤ K := by
      intro d e hd hde
      rw [hK]
      refine Nat.le_log_of_pow_le (by norm_num) ?_
      calc 2 ^ e ≤ d ^ e := Nat.pow_le_pow_left hd e
        _ ≤ s := hde
        _ ≤ 2 * x := by omega
    refine Finset.mem_image.mpr ⟨(k, l, m), ?_, hklm.symm⟩
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hbound a k ha hak),
      Nat.lt_succ_of_le (hbound b l hb hbl), Nat.lt_succ_of_le (hbound c m hc hcm)⟩
  calc (Band a b c x).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.range (K + 1) ×ˢ Finset.range (K + 1) ×ˢ Finset.range (K + 1)).card :=
        Finset.card_image_le
    _ = (K + 1) ^ 3 := by
        rw [Finset.card_product, Finset.card_product, Finset.card_range]; ring

/-- `S2 = ∑_{s∈B} s² ≤ |B_x|·(2x)²` (each band element is `< 2x`). With `band_card_upper` this
    gives `S2 ≤ polylog·x²`, hence `√S2 ≤ polylog·x` for the major-arc main-term comparison. -/
lemma S2_upper (x : ℕ) : S2 a b c x ≤ (Band a b c x).card * (2 * x) ^ 2 := by
  unfold S2
  calc (Band a b c x).sum (fun s => s ^ 2)
      ≤ (Band a b c x).sum (fun _ => (2 * x) ^ 2) := by
        refine Finset.sum_le_sum (fun s hs => ?_)
        obtain ⟨_, _, h2s⟩ := mem_Band.mp hs
        exact Nat.pow_le_pow_left (by omega) 2
    _ = (Band a b c x).card * (2 * x) ^ 2 := by rw [Finset.sum_const, smul_eq_mul]

/-- The minor-arc low-energy measure is bounded by the `[0,1)` measure of
    `LowEnergy.low_energy_measure`: `MinorArc ⊆ Ioc 0 1`
    and the extra endpoint `{1}` is null. -/
lemma minor_meas_le {x : ℕ} {z M : ℝ}
    (hz : MeasureTheory.volume {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ Qenergy a b c x t ≤ z}
            ≤ ENNReal.ofReal M) :
    MeasureTheory.volume {t : ℝ | t ∈ MinorArc x ∧ Qenergy a b c x t ≤ z} ≤ ENNReal.ofReal M := by
  have hsub : {t : ℝ | t ∈ MinorArc x ∧ Qenergy a b c x t ≤ z}
      ⊆ {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ Qenergy a b c x t ≤ z} ∪ ({1} : Set ℝ) := by
    rintro t ⟨htm, htq⟩
    have htioc : t ∈ Set.Ioc (0 : ℝ) 1 := htm.1
    rcases eq_or_lt_of_le htioc.2 with h1 | h1
    · exact Or.inr h1
    · exact Or.inl ⟨⟨le_of_lt htioc.1, h1⟩, htq⟩
  calc MeasureTheory.volume {t : ℝ | t ∈ MinorArc x ∧ Qenergy a b c x t ≤ z}
      ≤ MeasureTheory.volume
          ({t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ Qenergy a b c x t ≤ z} ∪ ({1} : Set ℝ)) :=
        MeasureTheory.measure_mono hsub
    _ ≤ MeasureTheory.volume {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ Qenergy a b c x t ≤ z}
          + MeasureTheory.volume ({1} : Set ℝ) := MeasureTheory.measure_union_le _ _
    _ ≤ ENNReal.ofReal M := by rw [Real.volume_singleton, add_zero]; exact hz

/-- Level ↔ energy: `{t : level ≤ exp(−2Q_x t)} = {t : Q_x t ≤ −log(level)/2}` for `level > 0`. -/
lemma level_set_eq (a b c x : ℕ) {level : ℝ} (hlevel : 0 < level) :
    {t : ℝ | level ≤ Real.exp (-(2 * Qenergy a b c x t))}
      = {t : ℝ | Qenergy a b c x t ≤ -Real.log level / 2} := by
  ext t
  simp only [Set.mem_setOf_eq]
  rw [← Real.log_le_iff_le_exp hlevel]
  constructor <;> intro h <;> linarith

/-- **Direct energy-split** bound for `∫_𝔪 exp(−2Q)`: split `𝔪` at energy `L = log x` into the
    low-energy part (`exp(−2Q) ≤ exp(−2κ₀L)`, small measure `≤ M`) and the high-energy part
    (`exp(−2Q) < exp(−2L)`, measure `≤ 1`). Avoids the layer-cake level integral. -/
lemma minor_exp_integral_le (a b c x : ℕ) {κ₀ Mbound : ℝ}
    (hfloor : ∀ t ∈ MinorArc x, κ₀ * Real.log x ≤ Qenergy a b c x t)
    (hmeas : (MeasureTheory.volume
        {t : ℝ | t ∈ MinorArc x ∧ Qenergy a b c x t ≤ Real.log x}).toReal ≤ Mbound) :
    (∫ t in MinorArc x, Real.exp (-(2 * Qenergy a b c x t)))
      ≤ Real.exp (-(2 * κ₀ * Real.log x)) * Mbound + Real.exp (-(2 * Real.log x)) := by
  have hmeas𝔪 : MeasurableSet (MinorArc x) := measurableSet_MinorArc x
  have hmeasQ : MeasurableSet {t : ℝ | Qenergy a b c x t ≤ Real.log x} :=
    measurableSet_le (Qenergy_measurable a b c x) measurable_const
  have hInt : MeasureTheory.IntegrableOn (fun t => Real.exp (-(2 * Qenergy a b c x t)))
      (MinorArc x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (exp_neg_two_Q_intervalIntegrable a b c x 0 1))).mono_set Set.diff_subset
  have hvolIoc : MeasureTheory.volume (Set.Ioc (0 : ℝ) 1) < ⊤ := by
    rw [Real.volume_Ioc]; simp
  have hfin : ∀ S : Set ℝ, S ⊆ MinorArc x → MeasureTheory.volume S < ⊤ := fun S hS =>
    lt_of_le_of_lt (MeasureTheory.measure_mono (hS.trans Set.diff_subset)) hvolIoc
  rw [← MeasureTheory.integral_inter_add_sdiff hmeasQ hInt]
  refine add_le_add ?_ ?_
  · -- low-energy part
    have hsetle : (∫ t in MinorArc x ∩ {t | Qenergy a b c x t ≤ Real.log x},
          Real.exp (-(2 * Qenergy a b c x t)))
        ≤ ∫ _t in MinorArc x ∩ {t | Qenergy a b c x t ≤ Real.log x},
            Real.exp (-(2 * κ₀ * Real.log x)) := by
      refine MeasureTheory.setIntegral_mono_on (hInt.mono_set Set.inter_subset_left)
        (MeasureTheory.integrableOn_const (hfin _ Set.inter_subset_left).ne)
        (hmeas𝔪.inter hmeasQ) (fun t ht => ?_)
      exact Real.exp_le_exp.mpr (by linarith [hfloor t ht.1])
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hsetle
    refine hsetle.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    rw [show MinorArc x ∩ {t | Qenergy a b c x t ≤ Real.log x}
        = {t : ℝ | t ∈ MinorArc x ∧ Qenergy a b c x t ≤ Real.log x} from by
      ext t; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]]
    exact hmeas
  · -- high-energy part
    have hsetle : (∫ t in MinorArc x \ {t | Qenergy a b c x t ≤ Real.log x},
          Real.exp (-(2 * Qenergy a b c x t)))
        ≤ ∫ _t in MinorArc x \ {t | Qenergy a b c x t ≤ Real.log x},
            Real.exp (-(2 * Real.log x)) := by
      refine MeasureTheory.setIntegral_mono_on (hInt.mono_set Set.diff_subset)
        (MeasureTheory.integrableOn_const (hfin _ Set.diff_subset).ne)
        (hmeas𝔪.diff hmeasQ) (fun t ht => ?_)
      have hQ : Real.log x < Qenergy a b c x t := by
        have h2 := ht.2; simp only [Set.mem_setOf_eq, not_le] at h2; exact h2
      exact Real.exp_le_exp.mpr (by linarith)
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hsetle
    refine hsetle.trans ?_
    rw [mul_comm]
    refine (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)).trans (le_of_eq (mul_one _))
    calc (MeasureTheory.volume (MinorArc x \ {t | Qenergy a b c x t ≤ Real.log x})).toReal
        ≤ (MeasureTheory.volume (Set.Ioc (0 : ℝ) 1)).toReal :=
          ENNReal.toReal_mono hvolIoc.ne
            (MeasureTheory.measure_mono (Set.diff_subset.trans Set.diff_subset))
      _ = 1 := by rw [Real.volume_Ioc]; simp

/-- Growth: `(log x)^p · x^{−q} → 0` for `q > 0` (power beats any log power). -/
lemma poly_log_rpow_tendsto {p q : ℝ} (hq : 0 < q) :
    Filter.Tendsto (fun x : ℝ => Real.log x ^ p * x ^ (-q)) Filter.atTop (nhds 0) := by
  have h : (fun x : ℝ => Real.log x ^ p) =o[Filter.atTop] (fun x => x ^ q) :=
    isLittleO_log_rpow_rpow_atTop p hq
  refine (h.tendsto_div_nhds_zero).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le, div_eq_mul_inv]

/-- `Nat.log 2 (2x) ≤ log(2x)/log 2` — bridges the polylog band-count bound to `Real.log`. -/
lemma natLog_two_le_realLog (x : ℕ) (hx : 1 ≤ x) :
    (Nat.log 2 (2 * x) : ℝ) ≤ Real.log (2 * x) / Real.log 2 := by
  have hpow : (2 : ℝ) ^ Nat.log 2 (2 * x) ≤ (2 * x : ℝ) := by
    have := Nat.pow_log_le_self 2 (show 2 * x ≠ 0 by omega)
    calc (2 : ℝ) ^ Nat.log 2 (2 * x) = ((2 ^ Nat.log 2 (2 * x) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * x : ℕ) : ℝ) := by exact_mod_cast this
      _ = (2 * x : ℝ) := by push_cast; ring
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  calc (Nat.log 2 (2 * x) : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ Nat.log 2 (2 * x)) := by
        rw [Real.log_pow]
    _ ≤ Real.log (2 * x) := Real.log_le_log (by positivity) hpow

/-- Over the band: `∏(1+e(st)) = 2^{|B|}·(∏cos πst)·e(S₁t/2)` (product of `one_add_e_eq`). -/
lemma prod_one_add_e_eq (a b c x : ℕ) (t : ℝ) :
    (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t)))
      = 2 ^ (Band a b c x).card
        * ((∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)) : ℝ) : ℂ)
        * e ((S1 a b c x : ℝ) * t / 2) := by
  simp only [one_add_e_eq]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Complex.ofReal_prod]
  congr 1
  rw [show (∏ s ∈ Band a b c x, e ((s : ℝ) * t / 2))
      = ∏ s ∈ Band a b c x, e ((s : ℝ) * (t / 2)) from by
    refine Finset.prod_congr rfl (fun s _ => ?_); rw [mul_div_assoc], prod_e]
  congr 1
  rw [S1]
  simp only [id_eq]
  ring

/-- The real part of the subset-sum integrand on the band:
    `Re(∏(1+e(st))·e(−nt)) = 2^{|B|}·(∏cos πst)·cos(π(S₁−2n)t)`. -/
lemma integrand_re (a b c x n : ℕ) (t : ℝ) :
    ((∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = 2 ^ (Band a b c x).card * (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
        * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t)) := by
  have hre : ∀ β : ℝ, (e β).re = Real.cos (2 * Real.pi * β) := by
    intro β
    have hb : e β = Complex.exp ((↑(2 * Real.pi * β) : ℂ) * Complex.I) := by
      rw [e]; congr 1; push_cast; ring
    rw [hb, Complex.exp_ofReal_mul_I_re]
  rw [prod_one_add_e_eq, mul_assoc, ← e_add,
    show ((2 : ℂ) ^ (Band a b c x).card
          * ((∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)) : ℝ) : ℂ))
        = (((2 : ℝ) ^ (Band a b c x).card
            * (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t))) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, hre]
  congr 1
  rw [show 2 * Real.pi * ((S1 a b c x : ℝ) * t / 2 + -((n : ℝ) * t))
      = Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t) by ring]

/-- Weierstrass product inequality `1 − Σa ≤ ∏(1−a)` for `a ∈ [0,1]`. (General; REUSED from the
    Goldbach campaign's `MajorArcMainTerm.lean` rather than re-derived — a shared circle-method lemma
    library is the right home for `e`/`e_add`/this, currently duplicated across problem files.) -/
lemma prod_one_sub_ge {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert j t hj IH =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have haj0 : 0 ≤ a j := ha j (Finset.mem_insert_self j t)
    have hIH : 1 - ∑ i ∈ t, a i ≤ ∏ i ∈ t, (1 - a i) :=
      IH (fun i hi => ha i (Finset.mem_insert_of_mem hi))
        (fun i hi => ha1 i (Finset.mem_insert_of_mem hi))
    have hsum0 : 0 ≤ ∑ i ∈ t, a i :=
      Finset.sum_nonneg (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have h1 : (1 - a j) * (1 - ∑ i ∈ t, a i) ≤ (1 - a j) * ∏ i ∈ t, (1 - a i) :=
      mul_le_mul_of_nonneg_left hIH (by linarith [ha1 j (Finset.mem_insert_self j t)])
    nlinarith [h1, haj0, hsum0, mul_nonneg haj0 hsum0]

/-- **∏cos lower bound** on the major arc: `∏cos(πst) ≥ 1 − π²S₂t²/2` (Weierstrass + `cos y ≥ 1−y²/2`),
    valid where each `(πst)² ≤ 2`. The natural product lower bound feeding the Gaussian main term. -/
lemma prod_cos_ge (a b c x : ℕ) (t : ℝ)
    (ht : ∀ s ∈ Band a b c x, (Real.pi * ((s : ℝ) * t)) ^ 2 ≤ 2) :
    1 - Real.pi ^ 2 * (S2 a b c x : ℝ) * t ^ 2 / 2
      ≤ ∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)) := by
  have hstep1 : (∏ s ∈ Band a b c x, (1 - (Real.pi * ((s : ℝ) * t)) ^ 2 / 2))
      ≤ ∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)) := by
    refine Finset.prod_le_prod (fun s hs => ?_) (fun s _ => Real.one_sub_sq_div_two_le_cos)
    have := ht s hs; nlinarith [this]
  refine le_trans ?_ hstep1
  have hweier := prod_one_sub_ge (Band a b c x) (fun s => (Real.pi * ((s : ℝ) * t)) ^ 2 / 2)
    (fun s _ => by positivity) (fun s hs => by have := ht s hs; linarith)
  have hL : Real.pi ^ 2 * (S2 a b c x : ℝ) * t ^ 2 / 2
      = ∑ s ∈ Band a b c x, (Real.pi * ((s : ℝ) * t)) ^ 2 / 2 := by
    rw [S2]; push_cast; rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  exact le_trans (le_of_eq (by rw [hL])) hweier

/-- `Re(∫_𝔐 integrand) = ∫_𝔐 2^{|B|}(∏cos)cos(π(S₁−2n)t)` — reduces the major-arc lower bound to a
    real-analysis Gaussian estimate (`integral_re` + `integrand_re`). -/
lemma major_arc_re_eq (a b c x n : ℕ) :
    (∫ t in MajorArc x,
        (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = ∫ t in MajorArc x, 2 ^ (Band a b c x).card
          * (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t)) := by
  have hInt : MeasureTheory.IntegrableOn
      (fun t => (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))
      (MajorArc x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      ((by fun_prop : Continuous
        (fun t => (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))).intervalIntegrable
        0 1))).mono_set (fun t ht => ht.1)
  have hre_int : (∫ t in MajorArc x,
        (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = ∫ t in MajorArc x,
          ((∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re := by
    simpa using (Complex.reCLM.integral_comp_comm hInt).symm
  rw [hre_int]
  exact MeasureTheory.setIntegral_congr_fun (measurableSet_MajorArc x)
    (fun t _ => integrand_re a b c x n t)

/-! ## §4 — the sweep (proven, conditional only on the band count) -/

/-- Every band element is at least `x`, so a nonempty band has `S1 ≥ x`. -/
lemma le_S1_of_card_pos {x : ℕ} (h : 1 ≤ (Band a b c x).card) : x ≤ S1 a b c x := by
  obtain ⟨s, hs⟩ := Finset.card_pos.mp h
  calc x ≤ s := (mem_Band.mp hs).2.1
    _ = id s := rfl
    _ ≤ S1 a b c x := Finset.single_le_sum (fun i _ => Nat.zero_le (id i)) hs

/-- With at least 25 band elements, `S2 ≥ 25·x²`. -/
lemma S2_lower {x : ℕ} (h : 25 ≤ (Band a b c x).card) : 25 * x ^ 2 ≤ S2 a b c x := by
  have hstep : (Band a b c x).card • (x ^ 2) ≤ (Band a b c x).sum (fun s => s ^ 2) := by
    apply Finset.card_nsmul_le_sum
    intro s hs
    exact Nat.pow_le_pow_left (mem_Band.mp hs).2.1 2
  have hmul : 25 * x ^ 2 ≤ (Band a b c x).card * x ^ 2 := Nat.mul_le_mul_right _ h
  calc 25 * x ^ 2 ≤ (Band a b c x).card * x ^ 2 := hmul
    _ = (Band a b c x).card • (x ^ 2) := (smul_eq_mul _ _).symm
    _ ≤ S2 a b c x := hstep

/-- One unit step moves `S1` up by at most `3x + 3`: the entering elements satisfy
    `3x ≤ 2s < 3x + 3`, so there are at most two of them, each at most `3x/2 + 1`. -/
lemma S1_step_upper (x : ℕ) : S1 a b c (x + 1) ≤ S1 a b c x + (3 * x + 3) := by
  classical
  have hsplit :
      ((Band a b c (x + 1)) \ (Band a b c x)).sum id
        + ((Band a b c (x + 1)) ∩ (Band a b c x)).sum id
      = S1 a b c (x + 1) := by
    rw [← Finset.sdiff_inter_self_left (Band a b c (x + 1)) (Band a b c x)]
    exact Finset.sum_sdiff Finset.inter_subset_left
  have h1 : ((Band a b c (x + 1)) ∩ (Band a b c x)).sum id ≤ S1 a b c x :=
    Finset.sum_le_sum_of_subset Finset.inter_subset_right
  have hsub : (Band a b c (x + 1)) \ (Band a b c x)
      ⊆ Finset.Icc ((3 * x) / 2) ((3 * x) / 2 + 1) := by
    intro s hs
    obtain ⟨hmem, hnot⟩ := Finset.mem_sdiff.mp hs
    obtain ⟨hS, hge, hlt⟩ := mem_Band.mp hmem
    have hxle : x ≤ s := by omega
    have h2s : 3 * x ≤ 2 * s := by
      by_contra hcon
      exact hnot (mem_Band.mpr ⟨hS, hxle, by omega⟩)
    rw [Finset.mem_Icc]
    omega
  have h2 : ((Band a b c (x + 1)) \ (Band a b c x)).sum id ≤ 3 * x + 3 := by
    calc ((Band a b c (x + 1)) \ (Band a b c x)).sum id
        ≤ (Finset.Icc ((3 * x) / 2) ((3 * x) / 2 + 1)).sum id :=
          Finset.sum_le_sum_of_subset hsub
      _ = (3 * x) / 2 + ((3 * x) / 2 + 1) := by
          rw [show Finset.Icc ((3 * x) / 2) ((3 * x) / 2 + 1)
              = {(3 * x) / 2, (3 * x) / 2 + 1} by
            ext y
            simp [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
            omega]
          rw [Finset.sum_insert (by simp)]
          simp
      _ ≤ 3 * x + 3 := by omega
  omega

/-- The sweep: as `x` slides, the central windows overlap (`S1` steps by ≤ 3x+3,
    half-width `√S2 ≥ 5x`) and cover a half-line. -/
theorem sweep (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (X₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∃ x : ℕ, X₀ ≤ x ∧
      (2 * (n : ℤ) - (S1 a b c x : ℤ)) ^ 2 ≤ (S2 a b c x : ℤ) := by
  classical
  obtain ⟨X₁, hX₁⟩ := band_card_eventually_ge ha hb hc hco 25
  set X₂ : ℕ := max (max X₀ X₁) 2 with hX₂def
  have hX₂card : ∀ x : ℕ, X₂ ≤ x → 25 ≤ (Band a b c x).card := fun x hx =>
    hX₁ x (le_trans (le_trans (le_max_right X₀ X₁) (le_max_left _ 2)) hx)
  refine ⟨S1 a b c X₂ + 1, fun n hn => ?_⟩
  set Q : ℕ → Prop := fun x' => X₂ ≤ x' ∧ S1 a b c x' ≤ 2 * n with hQdef
  have hQ_le : ∀ x', Q x' → x' ≤ 2 * n := by
    intro x' ⟨hx', hs1⟩
    exact le_trans (le_S1_of_card_pos (le_trans (by norm_num) (hX₂card x' hx'))) hs1
  have hQX₂ : Q X₂ := ⟨le_refl _, by omega⟩
  have hX₂le : X₂ ≤ 2 * n + 1 := le_trans (hQ_le X₂ hQX₂) (by omega)
  set x : ℕ := Nat.findGreatest Q (2 * n + 1) with hxdef
  have hspec : Q x := Nat.findGreatest_spec hX₂le hQX₂
  have hxle : x ≤ 2 * n := hQ_le x hspec
  have hnot : ¬Q (x + 1) :=
    Nat.findGreatest_is_greatest (P := Q) (n := 2 * n + 1) (k := x + 1)
      (by omega) (by omega)
  have hnext : 2 * n < S1 a b c (x + 1) := by
    by_contra hcon
    exact hnot ⟨le_trans hspec.1 (by omega), by omega⟩
  have hstep := S1_step_upper (a := a) (b := b) (c := c) x
  have hS2 := S2_lower (hX₂card x hspec.1)
  have hx2 : 2 ≤ x := le_trans (le_max_right _ 2) hspec.1
  refine ⟨x, le_trans (le_trans (le_max_left X₀ X₁) (le_max_left _ 2)) hspec.1, ?_⟩
  have h1 : (S1 a b c x : ℤ) ≤ 2 * (n : ℤ) := by exact_mod_cast hspec.2
  have h2 : 2 * (n : ℤ) - (S1 a b c x : ℤ) ≤ 3 * (x : ℤ) + 3 := by
    have hz : (2 * n : ℤ) < (S1 a b c (x + 1) : ℤ) := by exact_mod_cast hnext
    have hcast : (S1 a b c (x + 1) : ℤ) ≤ (S1 a b c x : ℤ) + (3 * (x : ℤ) + 3) := by
      exact_mod_cast hstep
    omega
  have h3 : (25 : ℤ) * (x : ℤ) ^ 2 ≤ (S2 a b c x : ℤ) := by exact_mod_cast hS2
  have hx2' : (2 : ℤ) ≤ (x : ℤ) := by exact_mod_cast hx2
  nlinarith [sq_nonneg (2 * (n : ℤ) - (S1 a b c x : ℤ))]

end Bricks

/-! ## Final assembly

The final assembly of Erdős #123 does NOT live in this file.  It is
`Erdos123Band.erdos123_dcomplete'` in `Erdos123/Main.lean`, built from `lclt_coverage'`
and `sweep'` (both in Main.lean).  The `sweep` above is the full-window variant; it is
proved, but nothing currently consumes it — `Main.sweep'` is the 1/10-window version the
assembly actually uses.  See `STATUS.md`. -/

end Erdos123Band
