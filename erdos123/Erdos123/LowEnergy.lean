/-
M3b — The low-energy measure bound (paper Proposition 5.1, at the single level z = log x).

  `low_energy_measure` :  vol {t ∈ [0,1) : Q_x(t) ≤ log x} ≤ (1/x)·(log x)^C₄.

Method (a simplification of the paper's code-counting):  for `t` of energy `≤ L` the
grid has `≲ L` bad vertices, so some middle row and central path carry only boundedly
many.  Encode `t` by the (boundedly many) nonzero edge defects along that row+path.
Any two `t, t'` with the same code have value sequences whose DIFFERENCE satisfies the
homogeneous edge relations, hence propagates as `Δ_v = r·s_v`; the three face weights
of the untrimmed chain have gcd `1`, so `r ∈ ℤ` and the two root values agree modulo
`s_root`.  Since both root values lie in `[0, s_root]`, each code confines `t` to at
most `3` intervals of length `1/s_root ≤ 1/x`.  The number of codes is polynomial in
`n ≍ log x`, giving the bound.

No goodness of the root is needed (a `1/2`-window replaces the `δ`-window), and no
gcd entropy appears because the untrimmed chain endpoints lie exactly on the faces.
-/
import Erdos123.Rigidity

set_option maxHeartbeats 1600000

open scoped ENNReal

namespace Erdos123Band

/-! ## Round bookkeeping -/

lemma round_nonneg_of_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ round y := by
  rw [round_eq]
  exact Int.floor_nonneg.mpr (by linarith)

lemma round_le_nat {s : ℕ} {y : ℝ} (hy0 : 0 ≤ y) (hy : y < (s : ℝ)) : round y ≤ (s : ℤ) := by
  rw [round_eq]
  have h1 : y + 1 / 2 < (s : ℝ) + 1 / 2 := by linarith
  have h2 : ⌊y + 1 / 2⌋ ≤ ⌊(1 : ℝ) / 2 + (s : ℕ)⌋ := by
    apply Int.floor_mono
    push_cast
    linarith
  have h3 : ⌊(1 : ℝ) / 2 + (s : ℕ)⌋ = (s : ℤ) := by
    rw [Int.floor_add_natCast]
    norm_num
  omega

lemma abs_sub_le_abs_add_abs (u v : ℝ) : |u - v| ≤ |u| + |v| := by
  calc |u - v| = |u + -v| := by ring_nf
    _ ≤ |u| + |-v| := abs_add_le _ _
    _ = |u| + |v| := by rw [abs_neg]

/-- `choose n k ≤ (n+1)^k`. -/
lemma choose_le_succ_pow (n : ℕ) : ∀ k, Nat.choose n k ≤ (n + 1) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ m ih =>
    have hid : Nat.choose n (m + 1) * (m + 1) = Nat.choose n m * (n - m) :=
      Nat.choose_succ_right_eq n m
    have h1 : Nat.choose n (m + 1) ≤ Nat.choose n (m + 1) * (m + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    calc Nat.choose n (m + 1) ≤ Nat.choose n m * (n - m) := by omega
      _ ≤ (n + 1) ^ m * (n + 1) := by
          apply Nat.mul_le_mul ih (by omega)
      _ = (n + 1) ^ (m + 1) := (pow_succ _ _).symm

section LowEnergy

variable {a b c : ℕ}

/-! ## The Finset grid carrier and the bad-vertex count -/

/-! ## Chain data attached to a grid map

(The Finset grid carrier `TriF`, `mem_TriF` and the bad-count bound `badF_card_le`
are provided by `Erdos123.Rigidity`.) -/

/-- Row weight sequence. -/
def rwS (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q : ℕ) : ℕ → ℕ :=
  fun i => wt a b c (Φ (rowV n q i))

/-- Path weight sequence. -/
def pwS (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q j : ℕ) : ℕ → ℕ :=
  fun s => wt a b c (Φ (pathV n q j s))

/-- Row edge coefficients. -/
def rwA (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q : ℕ) : ℕ → ℕ :=
  fun i => edgeA a b c (Φ (rowV n q i)) (Φ (rowV n q (i + 1)))

def rwB (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q : ℕ) : ℕ → ℕ :=
  fun i => edgeA a b c (Φ (rowV n q (i + 1))) (Φ (rowV n q i))

/-- Path edge coefficients. -/
def pwA (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q j : ℕ) : ℕ → ℕ :=
  fun s => edgeA a b c (Φ (pathV n q j s)) (Φ (pathV n q j (s + 1)))

def pwB (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q j : ℕ) : ℕ → ℕ :=
  fun s => edgeA a b c (Φ (pathV n q j (s + 1))) (Φ (pathV n q j s))

/-- Row nearest-integer values at frequency `t`. -/
noncomputable def rdv (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q : ℕ) (t : ℝ) : ℕ → ℤ :=
  fun i => round ((rwS a b c n Φ q i : ℝ) * t)

noncomputable def pdv (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q j : ℕ) (t : ℝ) : ℕ → ℤ :=
  fun s => round ((pwS a b c n Φ q j s : ℝ) * t)

/-- Row edge defects at frequency `t`. -/
noncomputable def rdef (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q : ℕ) (t : ℝ) : ℕ → ℤ :=
  fun i => (rwB a b c n Φ q i : ℤ) * rdv a b c n Φ q t (i + 1)
    - (rwA a b c n Φ q i : ℤ) * rdv a b c n Φ q t i

noncomputable def pdef (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q j : ℕ) (t : ℝ) : ℕ → ℤ :=
  fun s => (pwB a b c n Φ q j s : ℤ) * pdv a b c n Φ q j t (s + 1)
    - (pwA a b c n Φ q j s : ℤ) * pdv a b c n Φ q j t s

/-! ## The difference-divisibility core -/

/-- **Chain difference divisibility.**  If two frequencies share every row defect
along a middle row `q` and every path defect along a central path `j`, then their
root values differ by a multiple of the root weight. -/
theorem chain_diff_dvd (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c)
    {x n : ℕ} (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ)
    (hband : ∀ v ∈ Tri n, wt a b c (Φ v) ∈ Band a b c x)
    (hface : ∀ v ∈ Tri n,
      (v.1 = 0 → (Φ v).1 = 0) ∧ (v.2.1 = 0 → (Φ v).2.1 = 0) ∧
      (v.2.2 = 0 → (Φ v).2.2 = 0))
    (hx1 : 1 ≤ x) (hn : 48 ≤ n) {q j : ℕ} (hq : q ∈ midQ n) (hj : j ∈ midJ q)
    (t t' : ℝ)
    (hrd : ∀ i, i < q → rdef a b c n Φ q t i = rdef a b c n Φ q t' i)
    (hpd : ∀ s, s < n - q → pdef a b c n Φ q j t s = pdef a b c n Φ q j t' s) :
    (rwS a b c n Φ q 0 : ℤ) ∣ (rdv a b c n Φ q t 0 - rdv a b c n Φ q t' 0) := by
  obtain ⟨hq1, hq2⟩ := midQ_bounds hq
  obtain ⟨hj1, hj2⟩ := midJ_bounds hj
  have hjq : j ≤ q := by omega
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hc0 : 0 < c := by omega
  -- positivity of the weights
  have hrs : ∀ i, i ≤ q → 0 < rwS a b c n Φ q i := by
    intro i hi
    have hmem := hband _ (rowV_mem_Tri hn hq hi)
    have h1 := (mem_Band.mp hmem).2.1
    show 0 < wt a b c (Φ (rowV n q i))
    omega
  have hps : ∀ s, s ≤ n - q → 0 < pwS a b c n Φ q j s := by
    intro s hs
    have hmem := hband _ (pathV_mem_Tri hn hq hj hs)
    have h1 := (mem_Band.mp hmem).2.1
    show 0 < wt a b c (Φ (pathV n q j s))
    omega
  -- positivity of the edge coefficients
  have hrB : ∀ i, i < q → 0 < rwB a b c n Φ q i := by
    intro i _
    exact edgeA_pos ha0 hb0 hc0 _ _
  have hpB : ∀ s, s < n - q → 0 < pwB a b c n Φ q j s := by
    intro s _
    exact edgeA_pos ha0 hb0 hc0 _ _
  -- the weight edge relations
  have hrrel : ∀ i, i < q →
      rwA a b c n Φ q i * rwS a b c n Φ q i
        = rwB a b c n Φ q i * rwS a b c n Φ q (i + 1) := by
    intro i _
    exact edgeA_mul_wt a b c _ _
  have hprel : ∀ s, s < n - q →
      pwA a b c n Φ q j s * pwS a b c n Φ q j s
        = pwB a b c n Φ q j s * pwS a b c n Φ q j (s + 1) := by
    intro s _
    exact edgeA_mul_wt a b c _ _
  -- the difference sequences and their relations
  set Δr : ℕ → ℤ := fun i => rdv a b c n Φ q t i - rdv a b c n Φ q t' i with hΔr
  set Δp : ℕ → ℤ := fun s => pdv a b c n Φ q j t s - pdv a b c n Φ q j t' s with hΔp
  have hrdΔ : ∀ i, i < q →
      (rwB a b c n Φ q i : ℤ) * Δr (i + 1) = (rwA a b c n Φ q i : ℤ) * Δr i := by
    intro i hi
    have h := hrd i hi
    simp only [rdef] at h
    simp only [hΔr]
    linear_combination h
  have hpdΔ : ∀ s, s < n - q →
      (pwB a b c n Φ q j s : ℤ) * Δp (s + 1) = (pwA a b c n Φ q j s : ℤ) * Δp s := by
    intro s hs
    have h := hpd s hs
    simp only [pdef] at h
    simp only [hΔp]
    linear_combination h
  -- junction
  have hjuncV : pathV n q j 0 = rowV n q (q - j) := pathV_zero hjq
  have hjunc_s : pwS a b c n Φ q j 0 = rwS a b c n Φ q (q - j) := by
    simp only [pwS, rwS, hjuncV]
  have hjunc_d : Δp 0 = Δr (q - j) := by
    simp only [hΔp, hΔr, pdv, rdv, pwS, rwS, hjuncV]
  -- the three face weights
  have hrow0 : rowV n q 0 = ((0 : ℕ), q, n - q) := by
    simp only [rowV, Nat.sub_zero]
  have hrowq : rowV n q q = (q, (0 : ℕ), n - q) := by
    simp only [rowV, Nat.sub_self]
  have hpathP : pathV n q j (n - q) = (q - j + (n - q), j, (0 : ℕ)) := by
    simp only [pathV, Nat.sub_self]
  have hmem0 : rowV n q 0 ∈ Tri n := rowV_mem_Tri hn hq (by omega)
  have hmemq : rowV n q q ∈ Tri n := rowV_mem_Tri hn hq (le_refl q)
  have hmemP : pathV n q j (n - q) ∈ Tri n := pathV_mem_Tri hn hq hj (le_refl _)
  have hface0 := (hface _ hmem0).1
  have hfaceq := (hface _ hmemq).2.1
  have hfaceP := (hface _ hmemP).2.2
  have hk0 : (Φ (rowV n q 0)).1 = 0 := by
    apply hface0
    rw [hrow0]
  have hl0 : (Φ (rowV n q q)).2.1 = 0 := by
    apply hfaceq
    rw [hrowq]
  have hm0 : (Φ (pathV n q j (n - q))).2.2 = 0 := by
    apply hfaceP
    rw [hpathP]
  have hw0 : rwS a b c n Φ q 0
      = b ^ (Φ (rowV n q 0)).2.1 * c ^ (Φ (rowV n q 0)).2.2 := by
    simp only [rwS, wt, hk0, pow_zero, one_mul]
  have hwq : rwS a b c n Φ q q
      = a ^ (Φ (rowV n q q)).1 * c ^ (Φ (rowV n q q)).2.2 := by
    simp only [rwS, wt, hl0, pow_zero, mul_one]
  have hwP : pwS a b c n Φ q j (n - q)
      = a ^ (Φ (pathV n q j (n - q))).1 * b ^ (Φ (pathV n q j (n - q))).2.1 := by
    simp only [pwS, wt, hm0, pow_zero, mul_one]
  have hgcd : Nat.gcd (Nat.gcd (rwS a b c n Φ q 0) (rwS a b c n Φ q q))
      (pwS a b c n Φ q j (n - q)) = 1 := by
    rw [hw0, hwq, hwP]
    exact corner_gcd_eq_one hco _ _ _ _ _ _
  exact chain_dvd (rwS a b c n Φ q) (pwS a b c n Φ q j) Δr Δp
    (rwA a b c n Φ q) (rwB a b c n Φ q) (pwA a b c n Φ q j) (pwB a b c n Φ q j)
    hrs hps hrB hpB hrrel hprel hrdΔ hpdΔ (q - j) (by omega) hjunc_s hjunc_d hgcd

/-! ## Codes -/

/-- The code type: `(q, j, row defect table, path defect table)`. -/
abbrev CodeT := ℕ × ℕ × Finset (ℕ × ℤ) × Finset (ℕ × ℤ)

/-- Defect tables: subsets of `[0,n] × [−K,K]` of size at most `B`. -/
noncomputable def DefCodes (n K B : ℕ) : Finset (Finset (ℕ × ℤ)) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.Icc (-(K : ℤ)) (K : ℤ))).powerset.filter
    (fun S => S.card ≤ B)

/-- The full code space. -/
noncomputable def Codes (n K B : ℕ) : Finset CodeT :=
  (Finset.range (n + 1)) ×ˢ ((Finset.range (n + 1)) ×ˢ
    ((DefCodes n K B) ×ˢ (DefCodes n K B)))

lemma DefCodes_card_le (n K B : ℕ) :
    (DefCodes n K B).card ≤ (B + 1) * ((n + 1) * (2 * K + 2)) ^ B := by
  classical
  set P : Finset (ℕ × ℤ) := (Finset.range (n + 1)) ×ˢ (Finset.Icc (-(K : ℤ)) (K : ℤ))
    with hP
  have hPcard : P.card = (n + 1) * (2 * K + 1) := by
    rw [hP, Finset.card_product, Finset.card_range, Int.card_Icc]
    congr 1
    omega
  have hsub : DefCodes n K B ⊆
      (Finset.range (B + 1)).biUnion (fun k => Finset.powersetCard k P) := by
    intro S hS
    rw [DefCodes, Finset.mem_filter, Finset.mem_powerset] at hS
    rw [Finset.mem_biUnion]
    exact ⟨S.card, by rw [Finset.mem_range]; omega,
      Finset.mem_powersetCard.mpr ⟨hS.1, rfl⟩⟩
  calc (DefCodes n K B).card
      ≤ ((Finset.range (B + 1)).biUnion (fun k => Finset.powersetCard k P)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (B + 1), (Finset.powersetCard k P).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (B + 1), ((n + 1) * (2 * K + 2)) ^ B := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_range] at hk
        rw [Finset.card_powersetCard, hPcard]
        calc Nat.choose ((n + 1) * (2 * K + 1)) k
            ≤ ((n + 1) * (2 * K + 1) + 1) ^ k := choose_le_succ_pow _ k
          _ ≤ ((n + 1) * (2 * K + 2)) ^ k := by
              apply Nat.pow_le_pow_left
              nlinarith [Nat.zero_le n, Nat.zero_le K]
          _ ≤ ((n + 1) * (2 * K + 2)) ^ B := by
              apply Nat.pow_le_pow_right (by positivity) (by omega)
    _ = (B + 1) * ((n + 1) * (2 * K + 2)) ^ B := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

lemma Codes_card_le (n K B : ℕ) :
    (Codes n K B).card ≤ (B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) * (n + 1) ^ (2 * B + 2) := by
  have h1 : (Codes n K B).card
      = (n + 1) * ((n + 1) * ((DefCodes n K B).card * (DefCodes n K B).card)) := by
    rw [Codes, Finset.card_product, Finset.card_product, Finset.card_product,
      Finset.card_range]
  rw [h1]
  have h2 := DefCodes_card_le n K B
  have h3 : (DefCodes n K B).card * (DefCodes n K B).card
      ≤ ((B + 1) * ((n + 1) * (2 * K + 2)) ^ B) * ((B + 1) * ((n + 1) * (2 * K + 2)) ^ B) :=
    Nat.mul_le_mul h2 h2
  calc (n + 1) * ((n + 1) * ((DefCodes n K B).card * (DefCodes n K B).card))
      ≤ (n + 1) * ((n + 1) * (((B + 1) * ((n + 1) * (2 * K + 2)) ^ B)
          * ((B + 1) * ((n + 1) * (2 * K + 2)) ^ B))) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_left
        exact h3
    _ = (B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) * (n + 1) ^ (2 * B + 2) := by
        rw [mul_pow]
        ring

/-- The compatibility set of a code. -/
def SCode (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (cd : CodeT) : Set ℝ :=
  {t | (∀ p ∈ cd.2.2.1, rdef a b c n Φ cd.1 t p.1 = p.2) ∧
       (∀ i, i < cd.1 → i ∉ cd.2.2.1.image Prod.fst → rdef a b c n Φ cd.1 t i = 0) ∧
       (∀ p ∈ cd.2.2.2, pdef a b c n Φ cd.1 cd.2.1 t p.1 = p.2) ∧
       (∀ s, s < n - cd.1 → s ∉ cd.2.2.2.image Prod.fst →
         pdef a b c n Φ cd.1 cd.2.1 t s = 0)}

/-- Two members of the same compatibility set share all chain defects. -/
lemma SCode_defects_eq {n : ℕ} {Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ} {cd : CodeT} {t t' : ℝ}
    (ht : t ∈ SCode a b c n Φ cd) (ht' : t' ∈ SCode a b c n Φ cd) :
    (∀ i, i < cd.1 → rdef a b c n Φ cd.1 t i = rdef a b c n Φ cd.1 t' i) ∧
    (∀ s, s < n - cd.1 →
      pdef a b c n Φ cd.1 cd.2.1 t s = pdef a b c n Φ cd.1 cd.2.1 t' s) := by
  classical
  obtain ⟨hr1, hr2, hp1, hp2⟩ := ht
  obtain ⟨hr1', hr2', hp1', hp2'⟩ := ht'
  constructor
  · intro i hi
    by_cases hmem : i ∈ cd.2.2.1.image Prod.fst
    · rw [Finset.mem_image] at hmem
      obtain ⟨p, hp, hpi⟩ := hmem
      rw [← hpi]
      rw [hr1 p hp, hr1' p hp]
    · rw [hr2 i hi hmem, hr2' i hi hmem]
  · intro s hs
    by_cases hmem : s ∈ cd.2.2.2.image Prod.fst
    · rw [Finset.mem_image] at hmem
      obtain ⟨p, hp, hpi⟩ := hmem
      rw [← hpi]
      rw [hp1 p hp, hp1' p hp]
    · rw [hp2 s hs hmem, hp2' s hs hmem]

/-! ## The three-arc trap -/

/-- Three closed intervals of radius `1/(2x)` around `(ν + k·s₀)/s₀`, `k ∈ {−1,0,1}`. -/
def arc3 (s₀ : ℕ) (ν : ℤ) (x : ℕ) : Set ℝ :=
  Set.Icc (((ν : ℝ) - s₀) / s₀ - 1 / (2 * x)) (((ν : ℝ) - s₀) / s₀ + 1 / (2 * x)) ∪
  (Set.Icc ((ν : ℝ) / s₀ - 1 / (2 * x)) ((ν : ℝ) / s₀ + 1 / (2 * x)) ∪
    Set.Icc (((ν : ℝ) + s₀) / s₀ - 1 / (2 * x)) (((ν : ℝ) + s₀) / s₀ + 1 / (2 * x)))

lemma arc3_volume (s₀ : ℕ) (ν : ℤ) (x : ℕ) :
    MeasureTheory.volume (arc3 s₀ ν x) ≤ ENNReal.ofReal (3 / (x : ℝ)) := by
  have hIcc : ∀ z : ℝ, MeasureTheory.volume
      (Set.Icc (z - 1 / (2 * (x : ℝ))) (z + 1 / (2 * (x : ℝ)))) = ENNReal.ofReal (1 / x) := by
    intro z
    rw [Real.volume_Icc]
    congr 1
    ring
  calc MeasureTheory.volume (arc3 s₀ ν x)
      ≤ MeasureTheory.volume
          (Set.Icc (((ν : ℝ) - s₀) / s₀ - 1 / (2 * x)) (((ν : ℝ) - s₀) / s₀ + 1 / (2 * x)))
        + (MeasureTheory.volume
            (Set.Icc ((ν : ℝ) / s₀ - 1 / (2 * x)) ((ν : ℝ) / s₀ + 1 / (2 * x)))
          + MeasureTheory.volume
            (Set.Icc (((ν : ℝ) + s₀) / s₀ - 1 / (2 * x)) (((ν : ℝ) + s₀) / s₀ + 1 / (2 * x)))) := by
        refine le_trans
          (MeasureTheory.measure_union_le (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
            _ _) ?_
        exact add_le_add le_rfl
          (MeasureTheory.measure_union_le (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
            _ _)
    _ = ENNReal.ofReal (1 / x) + (ENNReal.ofReal (1 / x) + ENNReal.ofReal (1 / x)) := by
        rw [hIcc, hIcc, hIcc]
    _ ≤ ENNReal.ofReal (3 / (x : ℝ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        apply le_of_eq
        ring

/-- Membership in the three-arc trap. -/
lemma mem_arc3 {s₀ x : ℕ} {ν ν' : ℤ} {t : ℝ} (hxs : x ≤ s₀) (hx : 1 ≤ x)
    (hnear : |(s₀ : ℝ) * t - (ν' : ℝ)| ≤ 1 / 2)
    (hcong : ν' = ν - s₀ ∨ ν' = ν ∨ ν' = ν + s₀) :
    t ∈ arc3 s₀ ν x := by
  have hs₀ : (0 : ℝ) < (s₀ : ℝ) := by
    have : 0 < s₀ := by omega
    exact_mod_cast this
  have hxR : (0 : ℝ) < (x : ℝ) := by
    have : 0 < x := by omega
    exact_mod_cast this
  have hxs' : (x : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hxs
  have hdist : |t - (ν' : ℝ) / s₀| ≤ 1 / (2 * x) := by
    have h1 : |t - (ν' : ℝ) / s₀| = |(s₀ : ℝ) * t - ν'| / s₀ := by
      rw [show t - (ν' : ℝ) / s₀ = ((s₀ : ℝ) * t - ν') / s₀ by field_simp, abs_div,
        abs_of_pos hs₀]
    rw [h1]
    have e1 : |(s₀ : ℝ) * t - (ν' : ℝ)| / s₀ ≤ (1 / 2) / s₀ := by
      rw [div_le_div_iff₀ hs₀ hs₀]
      nlinarith [hnear, hs₀]
    have e2 : (1 / 2 : ℝ) / s₀ ≤ (1 / 2) / x := by
      rw [div_le_div_iff₀ hs₀ hxR]
      nlinarith [hxs']
    calc |(s₀ : ℝ) * t - (ν' : ℝ)| / s₀ ≤ (1 / 2) / s₀ := e1
      _ ≤ (1 / 2) / x := e2
      _ = 1 / (2 * x) := by ring
  have hmem : t ∈ Set.Icc ((ν' : ℝ) / s₀ - 1 / (2 * x)) ((ν' : ℝ) / s₀ + 1 / (2 * x)) := by
    rw [Set.mem_Icc]
    have := abs_le.mp hdist
    constructor <;> linarith [this.1, this.2]
  rcases hcong with h | h | h
  · left
    have hcast : (ν' : ℝ) = (ν : ℝ) - s₀ := by rw [h]; push_cast; ring
    rwa [hcast] at hmem
  · right; left
    have hcast : (ν' : ℝ) = (ν : ℝ) := by rw [h]
    rwa [hcast] at hmem
  · right; right
    have hcast : (ν' : ℝ) = (ν : ℝ) + s₀ := by rw [h]; push_cast; ring
    rwa [hcast] at hmem

/-! ## Defect identities and bounds -/

/-- The defect, recentered at the fractional parts. -/
lemma rdef_cast {n : ℕ} (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q : ℕ) (t : ℝ) (i : ℕ) :
    ((rdef a b c n Φ q t i : ℤ) : ℝ)
      = (rwB a b c n Φ q i : ℝ)
          * ((rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t)
        - (rwA a b c n Φ q i : ℝ)
          * ((rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t) := by
  have hrel : rwA a b c n Φ q i * rwS a b c n Φ q i
      = rwB a b c n Φ q i * rwS a b c n Φ q (i + 1) := edgeA_mul_wt a b c _ _
  have hrelR : (rwA a b c n Φ q i : ℝ) * (rwS a b c n Φ q i : ℝ)
      = (rwB a b c n Φ q i : ℝ) * (rwS a b c n Φ q (i + 1) : ℝ) := by exact_mod_cast hrel
  simp only [rdef]
  push_cast
  linear_combination (-t) * hrelR

lemma pdef_cast {n : ℕ} (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q j : ℕ) (t : ℝ) (s : ℕ) :
    ((pdef a b c n Φ q j t s : ℤ) : ℝ)
      = (pwB a b c n Φ q j s : ℝ)
          * ((pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t)
        - (pwA a b c n Φ q j s : ℝ)
          * ((pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t) := by
  have hrel : pwA a b c n Φ q j s * pwS a b c n Φ q j s
      = pwB a b c n Φ q j s * pwS a b c n Φ q j (s + 1) := edgeA_mul_wt a b c _ _
  have hrelR : (pwA a b c n Φ q j s : ℝ) * (pwS a b c n Φ q j s : ℝ)
      = (pwB a b c n Φ q j s : ℝ) * (pwS a b c n Φ q j (s + 1) : ℝ) := by exact_mod_cast hrel
  simp only [pdef]
  push_cast
  linear_combination (-t) * hrelR

/-! ## The measure bound -/

/-- **Low-energy measure bound** (paper Prop 5.1 at the level `z = log x`):
the set of frequencies in `[0,1)` of energy at most `log x` has measure at most
`(log x)^C₄ / x`. -/
theorem low_energy_measure (a b c : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) :
    ∃ C₄ : ℕ, 1 ≤ C₄ ∧ ∃ X₂ : ℕ, ∀ x : ℕ, X₂ ≤ x →
      MeasureTheory.volume
          {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ Qenergy a b c x t ≤ Real.log x}
        ≤ ENNReal.ofReal (1 / (x : ℝ) * Real.log x ^ C₄) := by
  classical
  have ha2 : 2 ≤ a := ha
  have hb2 : 2 ≤ b := hb
  have hc2 : 2 ≤ c := hc
  obtain ⟨c₀, C₀, D, hc₀, hC₀, hD1, X₀g, hX₀g2, hgrid⟩ := grid_embedding ha2 hb2 hc2 hco
  set K : ℕ := (a * b * c) ^ D with hKdef
  have habc8 : 8 ≤ a * b * c := by
    calc 8 = 2 * 2 * 2 := by norm_num
      _ ≤ a * b * c := Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  have hK8 : 8 ≤ K := by
    rw [hKdef]
    calc 8 ≤ a * b * c := habc8
      _ = (a * b * c) ^ 1 := (pow_one _).symm
      _ ≤ (a * b * c) ^ D := Nat.pow_le_pow_right (le_trans (by norm_num) habc8) hD1
  have hKR : (8 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK8
  set δ : ℝ := 1 / (4 * K) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    positivity
  set B1 : ℕ := ⌈4 / (c₀ * δ ^ 2)⌉₊ with hB1def
  set B2 : ℕ := ⌈7 / (c₀ * δ ^ 2)⌉₊ with hB2def
  set B : ℕ := 2 * (B1 + B2 + 2) with hBdef
  set C₄ : ℕ := 2 * B + 3 with hC₄def
  set CCn : ℕ := (B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) with hCCndef
  set T₃ : ℝ := 3 * (CCn : ℝ) * (2 * C₀) ^ (2 * B + 2) + 1 with hT₃def
  set X₂ : ℕ := max X₀g (max 3 (max ⌈Real.exp (96 / c₀)⌉₊
    (max ⌈Real.exp T₃⌉₊ ⌈Real.exp (1 / C₀)⌉₊))) with hX₂def
  refine ⟨C₄, by omega, X₂, fun x hx => ?_⟩
  simp only [hX₂def, max_le_iff] at hx
  obtain ⟨hxX₀g, hx3, hxc₀, hxT₃, hxC₀⟩ := hx
  have hx1 : 1 ≤ x := by omega
  have hx0R : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  set L : ℝ := Real.log x with hLdef
  have hthresh : ∀ T : ℝ, ⌈Real.exp T⌉₊ ≤ x → T ≤ L := by
    intro T hT
    have h1 : Real.exp T ≤ (x : ℝ) := by
      calc Real.exp T ≤ (⌈Real.exp T⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (x : ℝ) := by exact_mod_cast hT
    calc T = Real.log (Real.exp T) := (Real.log_exp T).symm
      _ ≤ L := Real.log_le_log (Real.exp_pos T) h1
  have hL96 : 96 / c₀ ≤ L := hthresh _ hxc₀
  have hLT₃ : T₃ ≤ L := hthresh _ hxT₃
  have hLC₀ : 1 / C₀ ≤ L := hthresh _ hxC₀
  have hL0 : 0 < L := by
    have h96 : (0 : ℝ) < 96 / c₀ := by positivity
    linarith
  obtain ⟨n, Φ, ⟨hnlow, hnhigh⟩, hband, hinj, hface, hjump⟩ := hgrid x hxX₀g
  have hc₀L96 : (96 : ℝ) ≤ c₀ * L := by
    have h1 : c₀ * (96 / c₀) ≤ c₀ * L := mul_le_mul_of_nonneg_left hL96 hc₀.le
    rw [mul_div_cancel₀ _ hc₀.ne'] at h1
    linarith
  have hn96 : 96 ≤ n := by
    have h1 : (96 : ℝ) ≤ (n : ℝ) := by
      calc (96 : ℝ) ≤ c₀ * L := hc₀L96
        _ = c₀ * Real.log x := by rw [hLdef]
        _ ≤ (n : ℝ) := hnlow
    exact_mod_cast h1
  have hn48 : 48 ≤ n := by omega
  set E : Set ℝ := {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ Qenergy a b c x t ≤ Real.log x}
    with hEdef
  -- the arc assignment
  set Amap : CodeT → Set ℝ := fun cd =>
    if h : (E ∩ SCode a b c n Φ cd).Nonempty then
      arc3 (rwS a b c n Φ cd.1 0) (rdv a b c n Φ cd.1 h.choose 0) x
    else ∅ with hAmapdef
  -- THE COVERING
  have hcover : ∀ t ∈ E, ∃ cd ∈ Codes n K B, t ∈ Amap cd := by
    intro t htE
    obtain ⟨ht01, htQ⟩ := htE
    obtain ⟨ht0, ht1⟩ := ht01
    -- bad vertices and their count
    set Bad : ℕ × ℕ × ℕ → Prop := fun v =>
      δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| with hBaddef
    set H : ℕ := ((TriF n).filter (fun v =>
      δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)|)).card with hHdef
    have hHQ : (H : ℝ) * δ ^ 2 ≤ Qenergy a b c x t :=
      badF_card_le a b c x n Φ t δ hδ0 hband hinj
    have hHδL : (H : ℝ) * δ ^ 2 ≤ L := by
      calc (H : ℝ) * δ ^ 2 ≤ Qenergy a b c x t := hHQ
        _ ≤ Real.log x := htQ
        _ = L := by rw [hLdef]
    -- the sparse row and path
    have hHhyp : ∀ F : Finset (ℕ × ℕ × ℕ), (∀ v ∈ F, v ∈ Tri n ∧ Bad v) → F.card ≤ H := by
      intro F hF
      rw [hHdef]
      apply Finset.card_le_card
      intro v hv
      obtain ⟨hv1, hv2⟩ := hF v hv
      rw [Finset.mem_filter]
      exact ⟨mem_TriF.mpr hv1, hv2⟩
    obtain ⟨q, hq, j, hj, hrowH, hpathH⟩ := exists_sparse_row_and_path hn48 Bad H hHhyp
    obtain ⟨hq1, hq2⟩ := midQ_bounds hq
    obtain ⟨hj1, hj2⟩ := midJ_bounds hj
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hc₀L_le_n : c₀ * L ≤ (n : ℝ) := by
      calc c₀ * L = c₀ * Real.log x := by rw [hLdef]
        _ ≤ (n : ℝ) := hnlow
    -- row/path mark-count bounds, in the multiplied-out form
    have hkey : ∀ m k : ℕ, n * m ≤ k * H → (m : ℝ) * (c₀ * δ ^ 2) ≤ (k : ℝ) := by
      intro m k hmk
      have hnm : (n : ℝ) * m ≤ (k : ℝ) * H := by exact_mod_cast hmk
      have e1 : c₀ * L * ((m : ℝ) * δ ^ 2) ≤ (n : ℝ) * ((m : ℝ) * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hc₀L_le_n (by positivity)
      have e2 : (n : ℝ) * m * δ ^ 2 ≤ (k : ℝ) * H * δ ^ 2 :=
        mul_le_mul_of_nonneg_right hnm (by positivity)
      have e3 : (k : ℝ) * ((H : ℝ) * δ ^ 2) ≤ (k : ℝ) * L :=
        mul_le_mul_of_nonneg_left hHδL (by positivity)
      have h1 : (m : ℝ) * (c₀ * δ ^ 2) * L ≤ (k : ℝ) * L := by nlinarith [e1, e2, e3]
      exact le_of_mul_le_mul_right h1 hL0
    have hrow_le : (rowBad Bad n q).card ≤ B1 := by
      have h2 : ((rowBad Bad n q).card : ℝ) ≤ 4 / (c₀ * δ ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        have h := hkey _ 4 hrowH
        calc ((rowBad Bad n q).card : ℝ) * (c₀ * δ ^ 2) ≤ ((4 : ℕ) : ℝ) := h
          _ = 4 := by norm_num
      calc (rowBad Bad n q).card = ⌈((rowBad Bad n q).card : ℝ)⌉₊ :=
            (Nat.ceil_natCast _).symm
        _ ≤ ⌈(4 : ℝ) / (c₀ * δ ^ 2)⌉₊ := Nat.ceil_mono h2
        _ ≤ B1 := by rw [hB1def]
    have hpath_le : (pathBad Bad n q j).card ≤ B2 := by
      have h2 : ((pathBad Bad n q j).card : ℝ) ≤ 7 / (c₀ * δ ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        have h := hkey _ 7 hpathH
        calc ((pathBad Bad n q j).card : ℝ) * (c₀ * δ ^ 2) ≤ ((7 : ℕ) : ℝ) := h
          _ = 7 := by norm_num
      calc (pathBad Bad n q j).card = ⌈((pathBad Bad n q j).card : ℝ)⌉₊ :=
            (Nat.ceil_natCast _).symm
        _ ≤ ⌈(7 : ℝ) / (c₀ * δ ^ 2)⌉₊ := Nat.ceil_mono h2
        _ ≤ B2 := by rw [hB2def]
    -- edge-coefficient bounds along the chain
    have hrow_coeff : ∀ i, i < q → rwA a b c n Φ q i ≤ K ∧ rwB a b c n Φ q i ≤ K := by
      intro i hi
      have hv := rowV_mem_Tri (n := n) hn48 hq (by omega : i ≤ q)
      have hw := rowV_mem_Tri (n := n) hn48 hq (by omega : i + 1 ≤ q)
      have hadj := rowV_adjacent (n := n) (q := q) (i := i) (by omega)
      have hj6 := hjump _ hv _ hw hadj
      constructor
      · exact edgeA_le (by omega) (by omega) (by omega) hj6.2.1
          hj6.2.2.2.1 hj6.2.2.2.2.2 |>.trans_eq hKdef.symm
      · exact edgeA_le (by omega) (by omega) (by omega) hj6.1
          hj6.2.2.1 hj6.2.2.2.2.1 |>.trans_eq hKdef.symm
    have hpath_coeff : ∀ s, s < n - q →
        pwA a b c n Φ q j s ≤ K ∧ pwB a b c n Φ q j s ≤ K := by
      intro s hs
      have hv := pathV_mem_Tri (n := n) hn48 hq hj (by omega : s ≤ n - q)
      have hw := pathV_mem_Tri (n := n) hn48 hq hj (by omega : s + 1 ≤ n - q)
      have hadj := pathV_adjacent (n := n) (q := q) (j := j) (s := s) (by omega) (by omega)
      have hj6 := hjump _ hv _ hw hadj
      constructor
      · exact edgeA_le (by omega) (by omega) (by omega) hj6.2.1
          hj6.2.2.2.1 hj6.2.2.2.2.2 |>.trans_eq hKdef.symm
      · exact edgeA_le (by omega) (by omega) (by omega) hj6.1
          hj6.2.2.1 hj6.2.2.2.2.1 |>.trans_eq hKdef.symm
    -- defect size bound (always ≤ K)
    have hrdef_le : ∀ i, i < q → rdef a b c n Φ q t i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      intro i hi
      obtain ⟨hA, hB⟩ := hrow_coeff i hi
      have hid := rdef_cast (a := a) (b := b) (c := c) (n := n) Φ q t i
      have h1 : |(rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t|
          ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have h2 : |(rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t| ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have hAR : (rwA a b c n Φ q i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (rwB a b c n Φ q i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB
      have habs : |((rdef a b c n Φ q t i : ℤ) : ℝ)| ≤ (K : ℝ) := by
        rw [hid]
        have hA0 : (0 : ℝ) ≤ (rwA a b c n Φ q i : ℝ) := by positivity
        have hB0 : (0 : ℝ) ≤ (rwB a b c n Φ q i : ℝ) := by positivity
        calc |(rwB a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t)
            - (rwA a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t)|
            ≤ |(rwB a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t)|
              + |(rwA a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (rwB a b c n Φ q i : ℝ) * (1 / 2) + (rwA a b c n Φ q i : ℝ) * (1 / 2) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1 hB0
              · exact mul_le_mul_of_nonneg_left h2 hA0
          _ ≤ (K : ℝ) * (1 / 2) + (K : ℝ) * (1 / 2) := by
              apply add_le_add
              · apply mul_le_mul_of_nonneg_right hBR (by norm_num)
              · apply mul_le_mul_of_nonneg_right hAR (by norm_num)
          _ = (K : ℝ) := by ring
      rw [Finset.mem_Icc]
      have := abs_le.mp habs
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2
    have hpdef_le : ∀ s, s < n - q →
        pdef a b c n Φ q j t s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      intro s hs
      obtain ⟨hA, hB⟩ := hpath_coeff s hs
      have hid := pdef_cast (a := a) (b := b) (c := c) (n := n) Φ q j t s
      have h1 : |(pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t|
          ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have h2 : |(pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t| ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have hAR : (pwA a b c n Φ q j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (pwB a b c n Φ q j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB
      have habs : |((pdef a b c n Φ q j t s : ℤ) : ℝ)| ≤ (K : ℝ) := by
        rw [hid]
        have hA0 : (0 : ℝ) ≤ (pwA a b c n Φ q j s : ℝ) := by positivity
        have hB0 : (0 : ℝ) ≤ (pwB a b c n Φ q j s : ℝ) := by positivity
        calc |(pwB a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t)
            - (pwA a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t)|
            ≤ |(pwB a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t)|
              + |(pwA a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (pwB a b c n Φ q j s : ℝ) * (1 / 2) + (pwA a b c n Φ q j s : ℝ) * (1 / 2) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1 hB0
              · exact mul_le_mul_of_nonneg_left h2 hA0
          _ ≤ (K : ℝ) * (1 / 2) + (K : ℝ) * (1 / 2) := by
              apply add_le_add
              · apply mul_le_mul_of_nonneg_right hBR (by norm_num)
              · apply mul_le_mul_of_nonneg_right hAR (by norm_num)
          _ = (K : ℝ) := by ring
      rw [Finset.mem_Icc]
      have := abs_le.mp habs
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2
    -- nonzero defects only next to bad vertices
    have hgood_of_notbad : ∀ v, ¬Bad v →
        |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| ≤ δ := by
      intro v hv
      rw [hBaddef] at hv
      push_neg at hv
      exact hv
    have h2Kδ : 2 * (K : ℝ) * δ < 1 := by
      rw [hδdef]
      have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
      rw [show 2 * (K : ℝ) * (1 / (4 * K)) = 1 / 2 by field_simp; ring]
      norm_num
    have hrdef_zero : ∀ i, i < q → ¬Bad (rowV n q i) → ¬Bad (rowV n q (i + 1)) →
        rdef a b c n Φ q t i = 0 := by
      intro i hi hg1 hg2
      obtain ⟨hA, hB⟩ := hrow_coeff i hi
      have hid := rdef_cast (a := a) (b := b) (c := c) (n := n) Φ q t i
      have h1 := hgood_of_notbad _ hg2
      have h2 := hgood_of_notbad _ hg1
      have h1' : |(rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t| ≤ δ := by
        rw [abs_sub_comm]
        exact h1
      have h2' : |(rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t| ≤ δ := by
        rw [abs_sub_comm]
        exact h2
      have hAR : (rwA a b c n Φ q i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (rwB a b c n Φ q i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB
      have hA0 : (0 : ℝ) ≤ (rwA a b c n Φ q i : ℝ) := by positivity
      have hB0 : (0 : ℝ) ≤ (rwB a b c n Φ q i : ℝ) := by positivity
      have habs : |((rdef a b c n Φ q t i : ℤ) : ℝ)| < 1 := by
        rw [hid]
        calc |(rwB a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t)
            - (rwA a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t)|
            ≤ |(rwB a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t)|
              + |(rwA a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (rwB a b c n Φ q i : ℝ) * δ + (rwA a b c n Φ q i : ℝ) * δ := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1' hB0
              · exact mul_le_mul_of_nonneg_left h2' hA0
          _ ≤ (K : ℝ) * δ + (K : ℝ) * δ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right hBR hδ0.le
              · exact mul_le_mul_of_nonneg_right hAR hδ0.le
          _ = 2 * (K : ℝ) * δ := by ring
          _ < 1 := h2Kδ
      have h3 : |rdef a b c n Φ q t i| < 1 := by exact_mod_cast habs
      rw [abs_lt] at h3
      omega
    have hpdef_zero : ∀ s, s < n - q → ¬Bad (pathV n q j s) → ¬Bad (pathV n q j (s + 1)) →
        pdef a b c n Φ q j t s = 0 := by
      intro s hs hg1 hg2
      obtain ⟨hA, hB⟩ := hpath_coeff s hs
      have hid := pdef_cast (a := a) (b := b) (c := c) (n := n) Φ q j t s
      have h1 := hgood_of_notbad _ hg2
      have h2 := hgood_of_notbad _ hg1
      have h1' : |(pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t|
          ≤ δ := by
        rw [abs_sub_comm]
        exact h1
      have h2' : |(pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t| ≤ δ := by
        rw [abs_sub_comm]
        exact h2
      have hAR : (pwA a b c n Φ q j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (pwB a b c n Φ q j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB
      have hA0 : (0 : ℝ) ≤ (pwA a b c n Φ q j s : ℝ) := by positivity
      have hB0 : (0 : ℝ) ≤ (pwB a b c n Φ q j s : ℝ) := by positivity
      have habs : |((pdef a b c n Φ q j t s : ℤ) : ℝ)| < 1 := by
        rw [hid]
        calc |(pwB a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t)
            - (pwA a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t)|
            ≤ |(pwB a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t)|
              + |(pwA a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (pwB a b c n Φ q j s : ℝ) * δ + (pwA a b c n Φ q j s : ℝ) * δ := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1' hB0
              · exact mul_le_mul_of_nonneg_left h2' hA0
          _ ≤ (K : ℝ) * δ + (K : ℝ) * δ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right hBR hδ0.le
              · exact mul_le_mul_of_nonneg_right hAR hδ0.le
          _ = 2 * (K : ℝ) * δ := by ring
          _ < 1 := h2Kδ
      have h3 : |pdef a b c n Φ q j t s| < 1 := by exact_mod_cast habs
      rw [abs_lt] at h3
      omega
    -- the defect tables
    set rdfF : Finset ℕ := (Finset.range q).filter (fun i => rdef a b c n Φ q t i ≠ 0)
      with hrdfFdef
    set pdfF : Finset ℕ :=
      (Finset.range (n - q)).filter (fun s => pdef a b c n Φ q j t s ≠ 0) with hpdfFdef
    set rdf : Finset (ℕ × ℤ) := rdfF.image (fun i => (i, rdef a b c n Φ q t i)) with hrdfdef
    set pdf : Finset (ℕ × ℤ) := pdfF.image (fun s => (s, pdef a b c n Φ q j t s))
      with hpdfdef
    -- their sizes
    have hrdfF_sub : rdfF ⊆ (rowBad Bad n q) ∪ (rowBad Bad n q).image (fun i => i - 1) := by
      intro i hi
      rw [hrdfFdef, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hiq, hine⟩ := hi
      by_cases hb1 : Bad (rowV n q i)
      · apply Finset.mem_union_left
        rw [rowBad, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hb1⟩
      · by_cases hb2 : Bad (rowV n q (i + 1))
        · apply Finset.mem_union_right
          rw [Finset.mem_image]
          refine ⟨i + 1, ?_, by omega⟩
          rw [rowBad, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hb2⟩
        · exact absurd (hrdef_zero i hiq hb1 hb2) hine
    have hpdfF_sub : pdfF ⊆ (pathBad Bad n q j) ∪ (pathBad Bad n q j).image (fun s => s - 1) := by
      intro s hs
      rw [hpdfFdef, Finset.mem_filter, Finset.mem_range] at hs
      obtain ⟨hsq, hsne⟩ := hs
      by_cases hb1 : Bad (pathV n q j s)
      · apply Finset.mem_union_left
        rw [pathBad, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hb1⟩
      · by_cases hb2 : Bad (pathV n q j (s + 1))
        · apply Finset.mem_union_right
          rw [Finset.mem_image]
          refine ⟨s + 1, ?_, by omega⟩
          rw [pathBad, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hb2⟩
        · exact absurd (hpdef_zero s hsq hb1 hb2) hsne
    have hrdf_card : rdf.card ≤ B := by
      calc rdf.card ≤ rdfF.card := Finset.card_image_le
        _ ≤ ((rowBad Bad n q) ∪ (rowBad Bad n q).image (fun i => i - 1)).card :=
            Finset.card_le_card hrdfF_sub
        _ ≤ (rowBad Bad n q).card + ((rowBad Bad n q).image (fun i => i - 1)).card :=
            Finset.card_union_le _ _
        _ ≤ (rowBad Bad n q).card + (rowBad Bad n q).card := by
            have := Finset.card_image_le (s := rowBad Bad n q) (f := fun i => i - 1)
            omega
        _ ≤ B1 + B1 := by
            have := hrow_le
            omega
        _ ≤ B := by
            rw [hBdef]
            omega
    have hpdf_card : pdf.card ≤ B := by
      calc pdf.card ≤ pdfF.card := Finset.card_image_le
        _ ≤ ((pathBad Bad n q j) ∪ (pathBad Bad n q j).image (fun s => s - 1)).card :=
            Finset.card_le_card hpdfF_sub
        _ ≤ (pathBad Bad n q j).card + ((pathBad Bad n q j).image (fun s => s - 1)).card :=
            Finset.card_union_le _ _
        _ ≤ (pathBad Bad n q j).card + (pathBad Bad n q j).card := by
            have := Finset.card_image_le (s := pathBad Bad n q j) (f := fun s => s - 1)
            omega
        _ ≤ B2 + B2 := by
            have := hpath_le
            omega
        _ ≤ B := by
            rw [hBdef]
            omega
    -- the code and its membership
    have hcdmem : ((q, j, rdf, pdf) : CodeT) ∈ Codes n K B := by
      rw [Codes]
      simp only [Finset.mem_product, Finset.mem_range]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [DefCodes, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · intro p hp
          rw [hrdfdef, Finset.mem_image] at hp
          obtain ⟨i, hi, rfl⟩ := hp
          rw [hrdfFdef, Finset.mem_filter, Finset.mem_range] at hi
          simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨by omega, hrdef_le i hi.1⟩
        · exact hrdf_card
      · rw [DefCodes, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · intro p hp
          rw [hpdfdef, Finset.mem_image] at hp
          obtain ⟨s, hs, rfl⟩ := hp
          rw [hpdfFdef, Finset.mem_filter, Finset.mem_range] at hs
          simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨by omega, hpdef_le s hs.1⟩
        · exact hpdf_card
    -- t is compatible with its own code
    have hrdf_fst : rdf.image Prod.fst = rdfF := by
      rw [hrdfdef, Finset.image_image]
      exact Finset.image_id'
    have hpdf_fst : pdf.image Prod.fst = pdfF := by
      rw [hpdfdef, Finset.image_image]
      exact Finset.image_id'
    have htS : t ∈ SCode a b c n Φ (q, j, rdf, pdf) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro p hp
        rw [hrdfdef, Finset.mem_image] at hp
        obtain ⟨i, _, rfl⟩ := hp
        rfl
      · intro i hi hnot
        rw [show ((q, j, rdf, pdf) : CodeT).2.2.1 = rdf from rfl, hrdf_fst, hrdfFdef] at hnot
        by_contra hne
        exact hnot (by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hi, hne⟩)
      · intro p hp
        rw [hpdfdef, Finset.mem_image] at hp
        obtain ⟨s, _, rfl⟩ := hp
        rfl
      · intro s hs hnot
        rw [show ((q, j, rdf, pdf) : CodeT).2.2.2 = pdf from rfl, hpdf_fst, hpdfFdef] at hnot
        by_contra hne
        exact hnot (by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hs, hne⟩)
    -- the arc trap
    have hne : (E ∩ SCode a b c n Φ (q, j, rdf, pdf)).Nonempty :=
      ⟨t, ⟨⟨ht0, ht1⟩, htQ⟩, htS⟩
    refine ⟨(q, j, rdf, pdf), hcdmem, ?_⟩
    have hAeq : Amap (q, j, rdf, pdf)
        = arc3 (rwS a b c n Φ q 0) (rdv a b c n Φ q hne.choose 0) x := by
      rw [hAmapdef]
      exact dif_pos hne
    rw [hAeq]
    obtain ⟨ht'E, ht'S⟩ := hne.choose_spec
    obtain ⟨⟨ht'0, ht'1⟩, _⟩ := ht'E
    -- the difference divisibility between t and the chosen representative
    obtain ⟨hdefr, hdefp⟩ := SCode_defects_eq (a := a) (b := b) (c := c) htS ht'S
    have hdvd := chain_diff_dvd ha2 hb2 hc2 hco Φ hband hface hx1 hn48 hq hj
      t hne.choose hdefr hdefp
    obtain ⟨r, hr⟩ := hdvd
    -- both root values lie in [0, s₀]
    have hs₀mem := hband _ (rowV_mem_Tri hn48 hq (by omega : 0 ≤ q))
    have hs₀x : x ≤ rwS a b c n Φ q 0 := by
      have h1 := (mem_Band.mp hs₀mem).2.1
      exact h1
    have hs₀0 : 0 < rwS a b c n Φ q 0 := by omega
    have hs₀R : (0 : ℝ) < (rwS a b c n Φ q 0 : ℝ) := by exact_mod_cast hs₀0
    have hbound : ∀ u : ℝ, 0 ≤ u → u < 1 →
        0 ≤ rdv a b c n Φ q u 0 ∧ rdv a b c n Φ q u 0 ≤ (rwS a b c n Φ q 0 : ℤ) := by
      intro u hu0 hu1
      constructor
      · apply round_nonneg_of_nonneg
        positivity
      · apply round_le_nat (by positivity)
        calc (rwS a b c n Φ q 0 : ℝ) * u < (rwS a b c n Φ q 0 : ℝ) * 1 :=
              mul_lt_mul_of_pos_left hu1 hs₀R
          _ = (rwS a b c n Φ q 0 : ℝ) := mul_one _
    obtain ⟨hb1, hb2⟩ := hbound t ht0 ht1
    obtain ⟨hb1', hb2'⟩ := hbound hne.choose ht'0 ht'1
    have hs₀Z : (0 : ℤ) < (rwS a b c n Φ q 0 : ℤ) := by exact_mod_cast hs₀0
    have hprodlo : -((rwS a b c n Φ q 0 : ℕ) : ℤ) ≤ ((rwS a b c n Φ q 0 : ℕ) : ℤ) * r := by
      rw [← hr]
      omega
    have hprodhi : ((rwS a b c n Φ q 0 : ℕ) : ℤ) * r ≤ ((rwS a b c n Φ q 0 : ℕ) : ℤ) := by
      rw [← hr]
      omega
    have hrlo : -1 ≤ r := by nlinarith [hprodlo, hs₀Z]
    have hrhi : r ≤ 1 := by nlinarith [hprodhi, hs₀Z]
    have hcong : rdv a b c n Φ q t 0 = rdv a b c n Φ q hne.choose 0 - rwS a b c n Φ q 0
        ∨ rdv a b c n Φ q t 0 = rdv a b c n Φ q hne.choose 0
        ∨ rdv a b c n Φ q t 0 = rdv a b c n Φ q hne.choose 0 + rwS a b c n Φ q 0 := by
      interval_cases r
      · left; omega
      · right; left; omega
      · right; right; omega
    have hnear : |(rwS a b c n Φ q 0 : ℝ) * t - (rdv a b c n Φ q t 0 : ℝ)| ≤ 1 / 2 :=
      abs_sub_round _
    exact mem_arc3 hs₀x hx1 hnear hcong
  -- FROM COVERING TO MEASURE
  have hsubset : E ⊆ ⋃ cd ∈ Codes n K B, Amap cd := by
    intro t ht
    obtain ⟨cd, hcd, hmem⟩ := hcover t ht
    exact Set.mem_biUnion hcd hmem
  have hvol_arc : ∀ cd ∈ Codes n K B,
      MeasureTheory.volume (Amap cd) ≤ ENNReal.ofReal (3 / (x : ℝ)) := by
    intro cd _
    by_cases h : (E ∩ SCode a b c n Φ cd).Nonempty
    · have hAeq : Amap cd
          = arc3 (rwS a b c n Φ cd.1 0) (rdv a b c n Φ cd.1 h.choose 0) x := by
        rw [hAmapdef]
        exact dif_pos h
      rw [hAeq]
      exact arc3_volume _ _ _
    · have hAeq : Amap cd = ∅ := by
        rw [hAmapdef]
        exact dif_neg h
      rw [hAeq]
      simp
  calc MeasureTheory.volume E
      ≤ MeasureTheory.volume (⋃ cd ∈ Codes n K B, Amap cd) :=
        MeasureTheory.measure_mono hsubset
    _ ≤ ∑ cd ∈ Codes n K B, MeasureTheory.volume (Amap cd) :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ Codes n K B, ENNReal.ofReal (3 / (x : ℝ)) :=
        Finset.sum_le_sum hvol_arc
    _ = ((Codes n K B).card : ℝ≥0∞) * ENNReal.ofReal (3 / (x : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (1 / (x : ℝ) * Real.log x ^ C₄) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        -- the counting estimate
        have hcards : ((Codes n K B).card : ℝ)
            ≤ (CCn : ℝ) * ((n : ℝ) + 1) ^ (2 * B + 2) := by
          have h1 := Codes_card_le n K B
          have h2 : ((Codes n K B).card : ℝ)
              ≤ (((B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) * (n + 1) ^ (2 * B + 2) : ℕ) : ℝ) := by
            exact_mod_cast h1
          calc ((Codes n K B).card : ℝ)
              ≤ (((B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) * (n + 1) ^ (2 * B + 2) : ℕ) : ℝ) := h2
            _ = (CCn : ℝ) * ((n : ℝ) + 1) ^ (2 * B + 2) := by
                rw [hCCndef]
                push_cast
                ring
        have hn1 : ((n : ℝ) + 1) ≤ 2 * C₀ * L := by
          have h1 : (n : ℝ) ≤ C₀ * L := by
            calc (n : ℝ) ≤ C₀ * Real.log x := hnhigh
              _ = C₀ * L := by rw [hLdef]
          have h2 : (1 : ℝ) ≤ C₀ * L := by
            have h3 : C₀ * (1 / C₀) ≤ C₀ * L := mul_le_mul_of_nonneg_left hLC₀ hC₀.le
            rw [mul_div_cancel₀ _ hC₀.ne'] at h3
            linarith
          linarith
        have hCCn0 : (0 : ℝ) ≤ (CCn : ℝ) := by positivity
        have hL2B : (0 : ℝ) ≤ L ^ (2 * B + 2) := by positivity
        have hfinal : 3 * ((Codes n K B).card : ℝ) ≤ L ^ C₄ := by
          calc 3 * ((Codes n K B).card : ℝ)
              ≤ 3 * ((CCn : ℝ) * ((n : ℝ) + 1) ^ (2 * B + 2)) := by linarith [hcards]
            _ ≤ 3 * ((CCn : ℝ) * (2 * C₀ * L) ^ (2 * B + 2)) := by
                apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
                apply mul_le_mul_of_nonneg_left ?_ hCCn0
                apply pow_le_pow_left₀ (by positivity) hn1
            _ = (3 * (CCn : ℝ) * (2 * C₀) ^ (2 * B + 2)) * L ^ (2 * B + 2) := by
                rw [mul_pow]
                ring
            _ ≤ L * L ^ (2 * B + 2) := by
                apply mul_le_mul_of_nonneg_right ?_ hL2B
                rw [hT₃def] at hLT₃
                linarith
            _ = L ^ (2 * B + 3) := by
                rw [← pow_succ']
            _ = L ^ C₄ := by rw [hC₄def]
        calc ((Codes n K B).card : ℝ) * (3 / (x : ℝ))
            = (3 * ((Codes n K B).card : ℝ)) / (x : ℝ) := by ring
          _ ≤ L ^ C₄ / (x : ℝ) := by
              have hmul := mul_le_mul_of_nonneg_right hfinal hx0R.le
              rw [div_le_div_iff₀ hx0R hx0R]
              linarith [hmul]
          _ = 1 / (x : ℝ) * Real.log x ^ C₄ := by
              rw [hLdef]
              ring

end LowEnergy

end Erdos123Band

#print axioms Erdos123Band.low_energy_measure
