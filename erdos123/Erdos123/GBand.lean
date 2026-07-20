/-
G0 — The general-ratio band `GBand a b c p q x = S ∩ [x, (p/q)·x)` for a rational
ratio `ρ = p/q ∈ (1, min a (min b c))`, generalizing the hard-coded `ρ = 3/2` of
`Erdos123.Band`.

Contents:
  * `GBand`, `GS1`, `GS2`, `mem_GBand`, `of_mem_GBand`
  * `smooth3_dvd_exponents` — divisibility in `Smooth3` is componentwise on exponents
  * `gband_primitive`      — the antichain property for ANY ratio `< min(a,b,c)`
                             (the paper's argument: a divisor pair has ratio ≥ min(a,b,c))
  * `geta_pos`, `geta_lt_log` — the slab width `η = log p − log q`
  * `gexists_int_step`, `gladder_count`, `gband_card_eventually_ge` — the band count → ∞
  * `GQenergy`, `GchiBand`, `GMajorArc` (width `q/(8px)`), `GMinorArc`
    and the full kernel/integral machinery copied from `Erdos123.Band`
  * `gle_S1_of_card_pos`, `gS1_step_upper`, `gS2_ge_card_sq`, `gS2_upper` — sweep bricks

Everything here is axiom-free (the three labeled axioms of `Erdos123.Band` are NOT used).
-/
import Erdos123.Slab

set_option maxHeartbeats 1000000

namespace Erdos123Band

/-! ## The band, its moments, and membership -/

/-- The general-ratio multiplicative band `S ∩ [x, (p/q)·x)` as a finset. -/
noncomputable def GBand (a b c p q x : ℕ) : Finset ℕ :=
  letI := Classical.decPred (fun s => s ∈ Smooth3 a b c ∧ x ≤ s ∧ q * s < p * x)
  (Finset.range (2 * p * x)).filter (fun s => s ∈ Smooth3 a b c ∧ x ≤ s ∧ q * s < p * x)

/-- Band first moment. -/
noncomputable def GS1 (a b c p q x : ℕ) : ℕ := (GBand a b c p q x).sum id

/-- Band second moment. -/
noncomputable def GS2 (a b c p q x : ℕ) : ℕ := (GBand a b c p q x).sum (fun s => s ^ 2)

/-- Forward membership unfolding (no hypothesis on `q` needed). -/
theorem of_mem_GBand {a b c p q x s : ℕ} (h : s ∈ GBand a b c p q x) :
    s ∈ Smooth3 a b c ∧ x ≤ s ∧ q * s < p * x := by
  unfold GBand at h
  simp only [Finset.mem_filter, Finset.mem_range] at h
  exact h.2

/-- Membership in the band (for `0 < q` the range bound is automatic). -/
theorem mem_GBand {a b c p q : ℕ} (hq : 0 < q) {x s : ℕ} :
    s ∈ GBand a b c p q x ↔ s ∈ Smooth3 a b c ∧ x ≤ s ∧ q * s < p * x := by
  unfold GBand
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    have hs : s ≤ q * s := Nat.le_mul_of_pos_left s hq
    have h1 : s < p * x := lt_of_le_of_lt hs h.2.2
    have h2 : p * x ≤ 2 * p * x := by
      have hp2 : p ≤ 2 * p := by omega
      exact Nat.mul_le_mul_right x hp2
    exact lt_of_lt_of_le h1 h2

/-- Every band element is at most `p·x` (for `0 < q`). -/
lemma gband_le {a b c p q x s : ℕ} (hq : 0 < q) (h : s ∈ GBand a b c p q x) :
    s ≤ p * x := by
  obtain ⟨-, -, hw⟩ := of_mem_GBand h
  have hs : s ≤ q * s := Nat.le_mul_of_pos_left s hq
  exact le_of_lt (lt_of_le_of_lt hs hw)

/-! ## The antichain property via three-base unique factorization -/

/-- **Componentwise divisibility.** For pairwise-coprime bases `≥ 2`, divisibility of
three-base monomials forces componentwise inequality of the exponents. -/
theorem smooth3_dvd_exponents {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) {k1 l1 m1 k2 l2 m2 : ℕ}
    (h : a ^ k1 * b ^ l1 * c ^ m1 ∣ a ^ k2 * b ^ l2 * c ^ m2) :
    k1 ≤ k2 ∧ l1 ≤ l2 ∧ m1 ≤ m2 := by
  obtain ⟨hab, hac, hbc⟩ := hco
  have key : ∀ u v w : ℕ, 2 ≤ u → Nat.Coprime u v → Nat.Coprime u w →
      ∀ e1 e2 f2 g2 : ℕ, u ^ e1 ∣ u ^ e2 * v ^ f2 * w ^ g2 → e1 ≤ e2 := by
    intro u v w hu huv huw e1 e2 f2 g2 hdvd
    have hdvd' : u ^ e1 ∣ u ^ e2 * (v ^ f2 * w ^ g2) := by
      rwa [← mul_assoc]
    have hcop : Nat.Coprime (u ^ e1) (v ^ f2 * w ^ g2) :=
      Nat.Coprime.mul_right (huv.pow e1 f2) (huw.pow e1 g2)
    have h2 : u ^ e1 ∣ u ^ e2 := by
      rcases hdvd' with ⟨d, hd⟩
      have h3 : u ^ e1 ∣ (v ^ f2 * w ^ g2) * u ^ e2 := ⟨d, by rw [← hd]; ring⟩
      exact (Nat.Coprime.dvd_of_dvd_mul_left hcop) h3
    by_contra hlt
    push_neg at hlt
    have h4 : u ^ e1 ≤ u ^ e2 := Nat.le_of_dvd (pow_pos (by omega) _) h2
    have h5 : u ^ e2 < u ^ e1 := Nat.pow_lt_pow_right (by omega) (by omega)
    exact absurd h4 (not_le.mpr h5)
  refine ⟨?_, ?_, ?_⟩
  · exact key a b c ha hab hac k1 k2 l2 m2 (dvd_trans ⟨b ^ l1 * c ^ m1, by ring⟩ h)
  · exact key b a c hb hab.symm hbc l1 l2 k2 m2
      (dvd_trans ⟨a ^ k1 * c ^ m1, by ring⟩ (h.trans ⟨1, by ring⟩))
  · exact key c a b hc hac.symm hbc.symm m1 m2 k2 l2
      (dvd_trans ⟨a ^ k1 * b ^ l1, by ring⟩ (h.trans ⟨1, by ring⟩))

/-- **The general band is a divisibility antichain.** A divisor pair inside `Smooth3`
has ratio `≥ min a (min b c) > p/q`, which does not fit in the band. -/
theorem gband_primitive {a b c p q : ℕ} (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q)
    (hpd : p < q * min a (min b c)) (x : ℕ) :
    IsPrimitive (GBand a b c p q x) := by
  intro u hu v hv hne hdvd
  obtain ⟨huS, hux, huw⟩ := of_mem_GBand hu
  obtain ⟨hvS, hvx, hvw⟩ := of_mem_GBand hv
  obtain ⟨k1, l1, m1, hu'⟩ := huS
  obtain ⟨k2, l2, m2, hv'⟩ := hvS
  subst hu' hv'
  obtain ⟨hk, hl, hm⟩ :=
    smooth3_dvd_exponents (by omega) (by omega) (by omega) hco hdvd
  set W : ℕ := a ^ (k2 - k1) * (b ^ (l2 - l1) * c ^ (m2 - m1)) with hW
  have hfact : a ^ k2 * b ^ l2 * c ^ m2 = a ^ k1 * b ^ l1 * c ^ m1 * W := by
    rw [hW]
    have e1 : a ^ k2 = a ^ k1 * a ^ (k2 - k1) := by rw [← pow_add]; congr 1; omega
    have e2 : b ^ l2 = b ^ l1 * b ^ (l2 - l1) := by rw [← pow_add]; congr 1; omega
    have e3 : c ^ m2 = c ^ m1 * c ^ (m2 - m1) := by rw [← pow_add]; congr 1; omega
    rw [e1, e2, e3]; ring
  -- some exponent gap is positive (else u = v)
  have hgap : k1 < k2 ∨ l1 < l2 ∨ m1 < m2 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    have hk' : k1 = k2 := by omega
    have hl' : l1 = l2 := by omega
    have hm' : m1 = m2 := by omega
    exact hne (by rw [hk', hl', hm'])
  set d : ℕ := min a (min b c) with hd
  have hda : d ≤ a := min_le_left _ _
  have hdb : d ≤ b := le_trans (min_le_right _ _) (min_le_left _ _)
  have hdc : d ≤ c := le_trans (min_le_right _ _) (min_le_right _ _)
  -- the multiplier W is at least d
  have hdW : d ≤ W := by
    rcases hgap with hg | hg | hg
    · have h1 : a ≤ a ^ (k2 - k1) := by
        calc a = a ^ 1 := (pow_one a).symm
          _ ≤ a ^ (k2 - k1) := Nat.pow_le_pow_right (by omega) (by omega)
      calc d ≤ a := hda
        _ ≤ a ^ (k2 - k1) := h1
        _ ≤ W := by
            rw [hW]
            exact Nat.le_mul_of_pos_right _
              (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
    · have h1 : b ≤ b ^ (l2 - l1) := by
        calc b = b ^ 1 := (pow_one b).symm
          _ ≤ b ^ (l2 - l1) := Nat.pow_le_pow_right (by omega) (by omega)
      calc d ≤ b := hdb
        _ ≤ b ^ (l2 - l1) := h1
        _ ≤ W := by
            rw [hW, ← mul_assoc, mul_comm (a ^ (k2 - k1)) (b ^ (l2 - l1)), mul_assoc]
            exact Nat.le_mul_of_pos_right _
              (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
    · have h1 : c ≤ c ^ (m2 - m1) := by
        calc c = c ^ 1 := (pow_one c).symm
          _ ≤ c ^ (m2 - m1) := Nat.pow_le_pow_right (by omega) (by omega)
      calc d ≤ c := hdc
        _ ≤ c ^ (m2 - m1) := h1
        _ ≤ W := by
            rw [hW, show a ^ (k2 - k1) * (b ^ (l2 - l1) * c ^ (m2 - m1))
              = c ^ (m2 - m1) * (a ^ (k2 - k1) * b ^ (l2 - l1)) by ring]
            exact Nat.le_mul_of_pos_right _
              (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
  -- the contradiction chain: q·v < p·x ≤ p·u < q·d·u ≤ q·v
  set u : ℕ := a ^ k1 * b ^ l1 * c ^ m1 with hu'
  set v : ℕ := a ^ k2 * b ^ l2 * c ^ m2 with hv'
  have hupos : 0 < u := by
    rw [hu']
    exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
      (pow_pos (by omega) _)
  have h1 : p * x ≤ p * u := Nat.mul_le_mul_left p hux
  have h2 : p * u < q * d * u := by
    have hqd : p < q * d := by rw [hd]; exact hpd
    exact (Nat.mul_lt_mul_right hupos).mpr hqd
  have h3 : q * d * u ≤ q * v := by
    have h4 : d * u ≤ W * u := Nat.mul_le_mul_right u hdW
    have h5 : W * u = v := by rw [hfact]; ring
    calc q * d * u = q * (d * u) := by ring
      _ ≤ q * (W * u) := Nat.mul_le_mul_left q h4
      _ = q * v := by rw [h5]
  exact absurd (calc q * v < p * x := hvw
    _ ≤ p * u := h1
    _ < q * d * u := h2
    _ ≤ q * v := h3) (lt_irrefl _)

/-! ## The slab width `η = log p − log q` -/

/-- `η = log p − log q > 0` when `0 < q < p`. -/
lemma geta_pos {p q : ℕ} (hq : 0 < q) (hqp : q < p) :
    (0 : ℝ) < Real.log p - Real.log q := by
  have h : Real.log q < Real.log p :=
    Real.log_lt_log (by exact_mod_cast hq) (by exact_mod_cast hqp)
  linarith

/-- `η = log p − log q < log d` when `p < q·d`. -/
lemma geta_lt_log {p q d : ℕ} (hq : 0 < q) (hp : 0 < p) (hpd : p < q * d) :
    Real.log p - Real.log q < Real.log d := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, Nat.mul_zero] at hpd; omega
    · exact h0
  have h1 : Real.log p < Real.log (q * d) :=
    Real.log_lt_log (by exact_mod_cast hp) (by exact_mod_cast hpd)
  have h2 : Real.log ((q : ℝ) * (d : ℝ)) = Real.log q + Real.log d :=
    Real.log_mul (by exact_mod_cast hq.ne') (by exact_mod_cast hd.ne')
  rw [h2] at h1
  linarith

/-! ## The band-count ladder (general ratio) -/

/-- **Oriented integer near-relation, general ratio.** A coprime pair `(w,z)` drawn from
`{a,b}` and exponents `P,Q ≥ 1` with `z^P < w^Q` yet `q·(w^Q)^K < p·(z^P)^K`
(i.e. `(w^Q/z^P)^K < p/q`). -/
theorem gexists_int_step {a b p q : ℕ} (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hq : 0 < q) (hqp : q < p) (hpa : p < q * a) (hpb : p < q * b)
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ w z P Q : ℕ, 2 ≤ w ∧ 2 ≤ z ∧ Nat.Coprime w z ∧
      (w = a ∧ z = b ∨ w = b ∧ z = a) ∧ 1 ≤ P ∧ 1 ≤ Q ∧
      z ^ P < w ^ Q ∧ q * (w ^ Q) ^ K < p * (z ^ P) ^ K := by
  have hp0 : 0 < p := by omega
  have hla : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha)
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set η : ℝ := Real.log p - Real.log q with hηdef
  have hη : 0 < η := geta_pos hq hqp
  set ε : ℝ := η / K with hεdef
  have hεpos : 0 < ε := div_pos hη hKR
  have hε_le : ε ≤ η := by
    rw [hεdef, div_le_iff₀ hKR]; nlinarith [hη, hK1R]
  have hηa : η < Real.log a := geta_lt_log hq hp0 hpa
  have hηb : η < Real.log b := geta_lt_log hq hp0 hpb
  have hεa : ε < Real.log a := lt_of_le_of_lt hε_le hηa
  have hεb : ε < Real.log b := lt_of_le_of_lt hε_le hηb
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
    · right; refine ⟨by omega, ?_⟩; by_contra hn; push_neg at hn
      exact hnotnn ⟨by omega, by omega⟩
    · exfalso
      rcases le_or_gt n 0 with hn | hn
      · exact hnotnn ⟨by omega, hn⟩
      · exact hnotpp ⟨by omega, by omega⟩
    · left; refine ⟨by omega, ?_⟩; by_contra hn; push_neg at hn
      exact hnotpp ⟨by omega, by omega⟩
  have key : ∀ (w z P Q : ℕ), 2 ≤ w → 2 ≤ z → 1 ≤ P → 1 ≤ Q →
      0 < (Q : ℝ) * Real.log w - (P : ℝ) * Real.log z →
      (Q : ℝ) * Real.log w - (P : ℝ) * Real.log z < ε →
      z ^ P < w ^ Q ∧ q * (w ^ Q) ^ K < p * (z ^ P) ^ K := by
    intro w z P Q hw hz hP hQ hgt hlt2
    have hzw : (z : ℝ) ^ P < (w : ℝ) ^ Q := by
      have hl : Real.log ((z : ℝ) ^ P) < Real.log ((w : ℝ) ^ Q) := by
        simp only [Real.log_pow]; linarith
      exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp hl
    refine ⟨by exact_mod_cast hzw, ?_⟩
    have hstep := mul_lt_mul_of_pos_left hlt2 hKR
    have hKε : (K : ℝ) * ε = η := by rw [hεdef]; field_simp
    rw [hKε, mul_sub, hηdef] at hstep
    have hq0R : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hp0R : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
    have hreal : (q : ℝ) * ((w : ℝ) ^ Q) ^ K < (p : ℝ) * ((z : ℝ) ^ P) ^ K := by
      have hloglt : Real.log ((q : ℝ) * ((w : ℝ) ^ Q) ^ K)
          < Real.log ((p : ℝ) * ((z : ℝ) ^ P) ^ K) := by
        rw [Real.log_mul hq0R.ne' (by positivity), Real.log_mul hp0R.ne' (by positivity)]
        simp only [Real.log_pow]
        linarith [hstep]
      exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp hloglt
    have hcast : ((q * (w ^ Q) ^ K : ℕ) : ℝ) < ((p * (z ^ P) ^ K : ℕ) : ℝ) := by
      push_cast; push_cast at hreal; linarith
    exact_mod_cast hcast
  rcases hcase with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · have e1 : (m.toNat : ℝ) = (m : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ m)
    have e2 : ((-n).toNat : ℝ) = -(n : ℝ) := by
      have : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    refine ⟨a, b, (-n).toNat, m.toNat, ha, hb, hab, Or.inl ⟨rfl, rfl⟩, by omega, by omega, ?_⟩
    have hgt : 0 < (m.toNat : ℝ) * Real.log a - ((-n).toNat : ℝ) * Real.log b := by
      rw [e1, e2]; nlinarith [hpos]
    have hlt2 : (m.toNat : ℝ) * Real.log a - ((-n).toNat : ℝ) * Real.log b < ε := by
      rw [e1, e2]; nlinarith [hlt]
    exact key a b (-n).toNat m.toNat ha hb (by omega) (by omega) hgt hlt2
  · have e1 : (n.toNat : ℝ) = (n : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ n)
    have e2 : ((-m).toNat : ℝ) = -(m : ℝ) := by
      have : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    refine ⟨b, a, (-m).toNat, n.toNat, hb, ha, hab.symm, Or.inr ⟨rfl, rfl⟩, by omega, by omega, ?_⟩
    have hgt : 0 < (n.toNat : ℝ) * Real.log b - ((-m).toNat : ℝ) * Real.log a := by
      rw [e1, e2]; nlinarith [hpos]
    have hlt2 : (n.toNat : ℝ) * Real.log b - ((-m).toNat : ℝ) * Real.log a < ε := by
      rw [e1, e2]; nlinarith [hlt]
    exact key b a (-m).toNat n.toNat hb ha (by omega) (by omega) hgt hlt2

/-- **Band-count ladder, general ratio.** Given the multiplicative step (`z^P < w^Q` but
the ratio's `K`-th power `< p/q`), the band eventually has `≥ K` elements. -/
theorem gladder_count {a b c p q w z P Q K : ℕ}
    (hz : 2 ≤ z) (hq : 0 < q) (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hK : 1 ≤ K)
    (hlt : z ^ P < w ^ Q) (hratio : q * (w ^ Q) ^ K < p * (z ^ P) ^ K)
    (hmem : ∀ i j : ℕ, w ^ i * z ^ j ∈ Smooth3 a b c) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → K ≤ (GBand a b c p q x).card := by
  set r : ℕ := w ^ Q with hrdef
  set s : ℕ := z ^ P with hsdef
  have hs2 : 2 ≤ s := le_trans hz (by rw [hsdef]; exact Nat.le_self_pow (by omega) z)
  have hsr : s < r := hlt
  have hsr1 : s + 1 ≤ r := hsr
  have hs0 : 0 < s := by omega
  have hr0 : 0 < r := by omega
  set E : ℕ → ℕ → ℕ := fun N j => r ^ j * s ^ (N - j) with hEdef
  have hEpos : ∀ N j, 0 < E N j := fun N j => by
    simp only [hEdef]
    exact Nat.mul_pos (pow_pos hr0 _) (pow_pos hs0 _)
  have hEmem : ∀ N j, E N j ∈ Smooth3 a b c := by
    intro N j
    simp only [hEdef, hrdef, hsdef, ← pow_mul]
    exact hmem (Q * j) (P * (N - j))
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
  have hbig : q * E N (J + K - 1) * s ^ K < p * x * s ^ K := by
    calc q * E N (J + K - 1) * s ^ K
        = q * (E N (J + K - 1) * s ^ (K - 1)) * s := by rw [hsK]; ring
      _ = q * (E N J * r ^ (K - 1)) * s := by rw [fA]
      _ = (E N J * s) * (q * r ^ (K - 1)) := by ring
      _ < (x * r) * (q * r ^ (K - 1)) :=
          mul_lt_mul_of_pos_right hJsr (Nat.mul_pos hq (pow_pos hr0 _))
      _ = x * (q * r ^ K) := by rw [hrK]; ring
      _ < x * (p * s ^ K) := mul_lt_mul_of_pos_left hratio hx0
      _ = p * x * s ^ K := by ring
  have hupper : q * E N (J + K - 1) < p * x :=
    lt_of_mul_lt_mul_right hbig (Nat.zero_le _)
  have hmaps : ∀ i ∈ Finset.range K, E N (J + i) ∈ GBand a b c p q x := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [mem_GBand hq]
    refine ⟨hEmem N (J + i), le_trans hJspec (hMono' N J (J + i) (by omega) (by omega)), ?_⟩
    have hle : E N (J + i) ≤ E N (J + K - 1) :=
      hMono' N (J + i) (J + K - 1) (by omega) (by omega)
    calc q * E N (J + i) ≤ q * E N (J + K - 1) := Nat.mul_le_mul_left q hle
      _ < p * x := hupper
  have hinj : Set.InjOn (fun i => E N (J + i)) (Finset.range K) := by
    intro i hi i' hi' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd heq (ne_of_lt (hStrict N (J + i) (J + i') (by omega) (by omega)))
    · exact h
    · exact absurd heq.symm (ne_of_lt (hStrict N (J + i') (J + i) (by omega) (by omega)))
  have hcard := Finset.card_le_card_of_injOn (fun i => E N (J + i)) hmaps hinj
  rwa [Finset.card_range] at hcard

/-- **Band population grows without bound** (general ratio). -/
theorem gband_card_eventually_ge {a b c p q : ℕ} (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) (K : ℕ) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → K ≤ (GBand a b c p q x).card := by
  rcases Nat.eq_zero_or_pos K with hK0 | hK
  · exact ⟨0, fun x _ => by rw [hK0]; exact Nat.zero_le _⟩
  have hpa : p < q * a :=
    lt_of_lt_of_le hpd (Nat.mul_le_mul_left q (min_le_left _ _))
  have hpb : p < q * b :=
    lt_of_lt_of_le hpd (Nat.mul_le_mul_left q
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  obtain ⟨w, z, P, Q, hw, hz, hwz, horient, hP, hQ, hlt, hratio⟩ :=
    gexists_int_step hco.1 (by omega) (by omega) hq hqp hpa hpb K hK
  have hmem : ∀ i j : ℕ, w ^ i * z ^ j ∈ Smooth3 a b c := by
    intro i j
    rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨i, j, 0, by simp⟩
    · exact ⟨j, i, 0, by ring⟩
  exact gladder_count hz hq hP hQ hK hlt hratio hmem

/-! ## Energy, χ-majorant, arcs (general ratio) -/

/-- The energy `Q_x(t) = ∑_{s∈B_x} ‖s t‖²` over the general band. -/
noncomputable def GQenergy (a b c p q x : ℕ) (t : ℝ) : ℝ :=
  ∑ s ∈ GBand a b c p q x, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2

/-- The characteristic-function modulus `χ(t) = ∏_{s∈B_x}|cos(π s t)|`. -/
noncomputable def GchiBand (a b c p q x : ℕ) (t : ℝ) : ℝ :=
  ∏ s ∈ GBand a b c p q x, |Real.cos (Real.pi * ((s : ℝ) * t))|

lemma GQenergy_nonneg (a b c p q x : ℕ) (t : ℝ) : 0 ≤ GQenergy a b c p q x t :=
  Finset.sum_nonneg (fun s _ => sq_nonneg _)

lemma GchiBand_nonneg (a b c p q x : ℕ) (t : ℝ) : 0 ≤ GchiBand a b c p q x t :=
  Finset.prod_nonneg (fun s _ => abs_nonneg _)

lemma GQenergy_measurable (a b c p q x : ℕ) : Measurable (GQenergy a b c p q x) := by
  unfold GQenergy
  refine Finset.measurable_sum _ (fun s _ => ?_)
  have hst : Measurable (fun t : ℝ => (s : ℝ) * t) := measurable_const.mul measurable_id
  have hround : Measurable (fun t : ℝ => ((round ((s : ℝ) * t) : ℤ) : ℝ)) :=
    (measurable_of_countable _).comp (measurable_round_real.comp hst)
  exact (hst.sub hround).pow_const 2

lemma gexp_neg_two_Q_intervalIntegrable (a b c p q x : ℕ) (u v : ℝ) :
    IntervalIntegrable (fun t => Real.exp (-(2 * GQenergy a b c p q x t)))
      MeasureTheory.volume u v := by
  rw [intervalIntegrable_iff]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    ((Real.measurable_exp.comp
      ((GQenergy_measurable a b c p q x).const_mul 2).neg)).aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ (fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  calc Real.exp (-(2 * GQenergy a b c p q x t))
      ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith [GQenergy_nonneg a b c p q x t])
    _ = 1 := Real.exp_zero

/-- **B1 — the Gaussian majorant** `χ(t) ≤ exp(−2 Q_x(t))` over the general band. -/
lemma gchi_le_exp_neg_two_Q (a b c p q x : ℕ) (t : ℝ) :
    GchiBand a b c p q x t ≤ Real.exp (-(2 * GQenergy a b c p q x t)) := by
  have hle : GchiBand a b c p q x t
      ≤ ∏ s ∈ GBand a b c p q x, Real.exp (-(2 * ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2)) :=
    Finset.prod_le_prod (fun s _ => abs_nonneg _)
      (fun s _ => abs_cos_le_exp ((s : ℝ) * t))
  refine hle.trans (le_of_eq ?_)
  rw [← Real.exp_sum]
  congr 1
  have hpt : ∀ s ∈ GBand a b c p q x,
      (-(2 * ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2))
        = (-2 : ℝ) * ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 := fun s _ => by ring
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, GQenergy]
  ring

lemma GchiBand_continuous (a b c p q x : ℕ) : Continuous (GchiBand a b c p q x) := by
  unfold GchiBand; fun_prop

lemma GchiBand_intervalIntegrable (a b c p q x : ℕ) (u v : ℝ) :
    IntervalIntegrable (GchiBand a b c p q x) MeasureTheory.volume u v :=
  (GchiBand_continuous a b c p q x).intervalIntegrable u v

lemma gprod_abs_one_add_e (a b c p q x : ℕ) (t : ℝ) :
    (∏ s ∈ GBand a b c p q x, ‖1 + e ((s : ℝ) * t)‖)
      = 2 ^ (GBand a b c p q x).card * GchiBand a b c p q x t := by
  rw [GchiBand, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun s _ => one_add_e_norm ((s : ℝ) * t))

/-- Minor-arc modulus bound over any set `S` (general band). -/
lemma gnorm_setIntegral_prod_le (a b c p q x n : ℕ) (S : Set ℝ) :
    ‖∫ t in S, (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))‖
      ≤ 2 ^ (GBand a b c p q x).card * ∫ t in S, GchiBand a b c p q x t := by
  calc ‖∫ t in S, (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))‖
      ≤ ∫ t in S, ‖(∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t in S, 2 ^ (GBand a b c p q x).card * GchiBand a b c p q x t := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        dsimp only
        rw [norm_mul, e_norm, mul_one, norm_prod, gprod_abs_one_add_e]
    _ = 2 ^ (GBand a b c p q x).card * ∫ t in S, GchiBand a b c p q x t :=
        MeasureTheory.integral_const_mul _ _

/-- Major arc in `Ioc 0 1`, width `q/(8px)`: for band elements `s < (p/q)x` this keeps
`|s·t| ≤ 1/8` uniformly in the ratio. -/
def GMajorArc (p q x : ℕ) : Set ℝ :=
  {t | t ∈ Set.Ioc (0 : ℝ) 1 ∧
    (t ≤ (q : ℝ) / (8 * (p : ℝ) * (x : ℝ)) ∨ 1 - (q : ℝ) / (8 * (p : ℝ) * (x : ℝ)) ≤ t)}

/-- Minor arc: `Ioc 0 1` minus the major arc. -/
def GMinorArc (p q x : ℕ) : Set ℝ := Set.Ioc (0 : ℝ) 1 \ GMajorArc p q x

lemma gmeasurableSet_MajorArc (p q x : ℕ) : MeasurableSet (GMajorArc p q x) := by
  have heq : GMajorArc p q x = Set.Ioc (0 : ℝ) 1 ∩
      (Set.Iic ((q : ℝ) / (8 * (p : ℝ) * (x : ℝ)))
        ∪ Set.Ici (1 - (q : ℝ) / (8 * (p : ℝ) * (x : ℝ)))) := by
    ext t; simp only [GMajorArc, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union,
      Set.mem_Iic, Set.mem_Ici]
  rw [heq]; exact measurableSet_Ioc.inter (measurableSet_Iic.union measurableSet_Ici)

lemma gmeasurableSet_MinorArc (p q x : ℕ) : MeasurableSet (GMinorArc p q x) :=
  measurableSet_Ioc.diff (gmeasurableSet_MajorArc p q x)

lemma gintegral_chi_le_exp_on_minor (a b c p q x : ℕ) :
    (∫ t in GMinorArc p q x, GchiBand a b c p q x t)
      ≤ ∫ t in GMinorArc p q x, Real.exp (-(2 * GQenergy a b c p q x t)) := by
  have hmm : GMinorArc p q x ⊆ Set.Ioc (0 : ℝ) 1 := Set.diff_subset
  have hχ : MeasureTheory.IntegrableOn (GchiBand a b c p q x) (GMinorArc p q x)
      MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (GchiBand_intervalIntegrable a b c p q x 0 1))).mono_set hmm
  have hexp : MeasureTheory.IntegrableOn (fun t => Real.exp (-(2 * GQenergy a b c p q x t)))
      (GMinorArc p q x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (gexp_neg_two_Q_intervalIntegrable a b c p q x 0 1))).mono_set hmm
  exact MeasureTheory.setIntegral_mono_on hχ hexp (gmeasurableSet_MinorArc p q x)
    (fun t _ => gchi_le_exp_neg_two_Q a b c p q x t)

/-- The minor-arc low-energy measure is bounded by the `[0,1)` measure. -/
lemma gminor_meas_le {a b c p q x : ℕ} {z M : ℝ}
    (hz : MeasureTheory.volume {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ z}
            ≤ ENNReal.ofReal M) :
    MeasureTheory.volume {t : ℝ | t ∈ GMinorArc p q x ∧ GQenergy a b c p q x t ≤ z}
      ≤ ENNReal.ofReal M := by
  have hsub : {t : ℝ | t ∈ GMinorArc p q x ∧ GQenergy a b c p q x t ≤ z}
      ⊆ {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ z} ∪ ({1} : Set ℝ) := by
    rintro t ⟨htm, htq⟩
    have htioc : t ∈ Set.Ioc (0 : ℝ) 1 := htm.1
    rcases eq_or_lt_of_le htioc.2 with h1 | h1
    · exact Or.inr h1
    · exact Or.inl ⟨⟨le_of_lt htioc.1, h1⟩, htq⟩
  calc MeasureTheory.volume {t : ℝ | t ∈ GMinorArc p q x ∧ GQenergy a b c p q x t ≤ z}
      ≤ MeasureTheory.volume
          ({t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ z} ∪ ({1} : Set ℝ)) :=
        MeasureTheory.measure_mono hsub
    _ ≤ MeasureTheory.volume {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ z}
          + MeasureTheory.volume ({1} : Set ℝ) := MeasureTheory.measure_union_le _ _
    _ ≤ ENNReal.ofReal M := by rw [Real.volume_singleton, add_zero]; exact hz

/-- Direct energy-split bound for `∫_𝔪 exp(−2Q)` (general band). -/
lemma gminor_exp_integral_le (a b c p q x : ℕ) {κ₀ Mbound : ℝ}
    (hfloor : ∀ t ∈ GMinorArc p q x, κ₀ * Real.log x ≤ GQenergy a b c p q x t)
    (hmeas : (MeasureTheory.volume
        {t : ℝ | t ∈ GMinorArc p q x ∧ GQenergy a b c p q x t ≤ Real.log x}).toReal ≤ Mbound) :
    (∫ t in GMinorArc p q x, Real.exp (-(2 * GQenergy a b c p q x t)))
      ≤ Real.exp (-(2 * κ₀ * Real.log x)) * Mbound + Real.exp (-(2 * Real.log x)) := by
  have hmeas𝔪 : MeasurableSet (GMinorArc p q x) := gmeasurableSet_MinorArc p q x
  have hmeasQ : MeasurableSet {t : ℝ | GQenergy a b c p q x t ≤ Real.log x} :=
    measurableSet_le (GQenergy_measurable a b c p q x) measurable_const
  have hInt : MeasureTheory.IntegrableOn (fun t => Real.exp (-(2 * GQenergy a b c p q x t)))
      (GMinorArc p q x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (gexp_neg_two_Q_intervalIntegrable a b c p q x 0 1))).mono_set Set.diff_subset
  have hvolIoc : MeasureTheory.volume (Set.Ioc (0 : ℝ) 1) < ⊤ := by
    rw [Real.volume_Ioc]; simp
  have hfin : ∀ S : Set ℝ, S ⊆ GMinorArc p q x → MeasureTheory.volume S < ⊤ := fun S hS =>
    lt_of_le_of_lt (MeasureTheory.measure_mono (hS.trans Set.diff_subset)) hvolIoc
  rw [← MeasureTheory.integral_inter_add_sdiff hmeasQ hInt]
  refine add_le_add ?_ ?_
  · have hsetle : (∫ t in GMinorArc p q x ∩ {t | GQenergy a b c p q x t ≤ Real.log x},
          Real.exp (-(2 * GQenergy a b c p q x t)))
        ≤ ∫ _t in GMinorArc p q x ∩ {t | GQenergy a b c p q x t ≤ Real.log x},
            Real.exp (-(2 * κ₀ * Real.log x)) := by
      refine MeasureTheory.setIntegral_mono_on (hInt.mono_set Set.inter_subset_left)
        (MeasureTheory.integrableOn_const (hfin _ Set.inter_subset_left).ne)
        (hmeas𝔪.inter hmeasQ) (fun t ht => ?_)
      exact Real.exp_le_exp.mpr (by linarith [hfloor t ht.1])
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hsetle
    refine hsetle.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    rw [show GMinorArc p q x ∩ {t | GQenergy a b c p q x t ≤ Real.log x}
        = {t : ℝ | t ∈ GMinorArc p q x ∧ GQenergy a b c p q x t ≤ Real.log x} from by
      ext t; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]]
    exact hmeas
  · have hsetle : (∫ t in GMinorArc p q x \ {t | GQenergy a b c p q x t ≤ Real.log x},
          Real.exp (-(2 * GQenergy a b c p q x t)))
        ≤ ∫ _t in GMinorArc p q x \ {t | GQenergy a b c p q x t ≤ Real.log x},
            Real.exp (-(2 * Real.log x)) := by
      refine MeasureTheory.setIntegral_mono_on (hInt.mono_set Set.diff_subset)
        (MeasureTheory.integrableOn_const (hfin _ Set.diff_subset).ne)
        (hmeas𝔪.diff hmeasQ) (fun t ht => ?_)
      have hQ : Real.log x < GQenergy a b c p q x t := by
        have h2 := ht.2; simp only [Set.mem_setOf_eq, not_le] at h2; exact h2
      exact Real.exp_le_exp.mpr (by linarith)
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hsetle
    refine hsetle.trans ?_
    rw [mul_comm]
    refine (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)).trans (le_of_eq (mul_one _))
    calc (MeasureTheory.volume
          (GMinorArc p q x \ {t | GQenergy a b c p q x t ≤ Real.log x})).toReal
        ≤ (MeasureTheory.volume (Set.Ioc (0 : ℝ) 1)).toReal :=
          ENNReal.toReal_mono hvolIoc.ne
            (MeasureTheory.measure_mono (Set.diff_subset.trans Set.diff_subset))
      _ = 1 := by rw [Real.volume_Ioc]; simp

/-- Over the band: `∏(1+e(st)) = 2^{|B|}·(∏cos πst)·e(S₁t/2)` (general ratio). -/
lemma gprod_one_add_e_eq (a b c p q x : ℕ) (t : ℝ) :
    (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t)))
      = 2 ^ (GBand a b c p q x).card
        * ((∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)) : ℝ) : ℂ)
        * e ((GS1 a b c p q x : ℝ) * t / 2) := by
  simp only [one_add_e_eq]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Complex.ofReal_prod]
  congr 1
  rw [show (∏ s ∈ GBand a b c p q x, e ((s : ℝ) * t / 2))
      = ∏ s ∈ GBand a b c p q x, e ((s : ℝ) * (t / 2)) from by
    refine Finset.prod_congr rfl (fun s _ => ?_); rw [mul_div_assoc], prod_e]
  congr 1
  rw [GS1]
  simp only [id_eq]
  ring

/-- Real part of the subset-sum integrand on the general band. -/
lemma gintegrand_re (a b c p q x n : ℕ) (t : ℝ) :
    ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = 2 ^ (GBand a b c p q x).card
        * (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
        * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) := by
  have hre : ∀ β : ℝ, (e β).re = Real.cos (2 * Real.pi * β) := by
    intro β
    have hb : e β = Complex.exp ((↑(2 * Real.pi * β) : ℂ) * Complex.I) := by
      rw [e]; congr 1; push_cast; ring
    rw [hb, Complex.exp_ofReal_mul_I_re]
  rw [gprod_one_add_e_eq, mul_assoc, ← e_add,
    show ((2 : ℂ) ^ (GBand a b c p q x).card
          * ((∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)) : ℝ) : ℂ))
        = (((2 : ℝ) ^ (GBand a b c p q x).card
            * (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t))) : ℝ) : ℂ) by
      push_cast; ring,
    Complex.re_ofReal_mul, hre]
  congr 1
  rw [show 2 * Real.pi * ((GS1 a b c p q x : ℝ) * t / 2 + -((n : ℝ) * t))
      = Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t) by ring]

/-- `Re(∫_𝔐 integrand) = ∫_𝔐 2^{|B|}(∏cos)cos(π(S₁−2n)t)` (general ratio). -/
lemma gmajor_arc_re_eq (a b c p q x n : ℕ) :
    (∫ t in GMajorArc p q x,
        (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = ∫ t in GMajorArc p q x, 2 ^ (GBand a b c p q x).card
          * (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) := by
  have hInt : MeasureTheory.IntegrableOn
      (fun t => (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))
      (GMajorArc p q x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      ((by fun_prop : Continuous
        (fun t => (∏ s ∈ GBand a b c p q x,
          (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))).intervalIntegrable
        0 1))).mono_set (fun t ht => ht.1)
  have hre_int : (∫ t in GMajorArc p q x,
        (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = ∫ t in GMajorArc p q x,
          ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re := by
    simpa using (Complex.reCLM.integral_comp_comm hInt).symm
  rw [hre_int]
  exact MeasureTheory.setIntegral_congr_fun (gmeasurableSet_MajorArc p q x)
    (fun t _ => gintegrand_re a b c p q x n t)

/-! ## Sweep bricks -/

/-- A nonempty band has `GS1 ≥ x`. -/
lemma gle_S1_of_card_pos {a b c p q x : ℕ} (h : 1 ≤ (GBand a b c p q x).card) :
    x ≤ GS1 a b c p q x := by
  obtain ⟨s, hs⟩ := Finset.card_pos.mp h
  calc x ≤ s := (of_mem_GBand hs).2.1
    _ = id s := rfl
    _ ≤ GS1 a b c p q x := Finset.single_le_sum (fun i _ => Nat.zero_le (id i)) hs

/-- `GS2 ≥ card · x²` (each band element is `≥ x`). -/
lemma gS2_ge_card_sq (a b c p q x : ℕ) :
    (GBand a b c p q x).card * x ^ 2 ≤ GS2 a b c p q x := by
  have hstep : (GBand a b c p q x).card • (x ^ 2)
      ≤ (GBand a b c p q x).sum (fun s => s ^ 2) := by
    apply Finset.card_nsmul_le_sum
    intro s hs
    exact Nat.pow_le_pow_left (of_mem_GBand hs).2.1 2
  simpa [smul_eq_mul, GS2] using hstep

/-- `GS2 ≤ card·(px)²` (each band element is `≤ p·x`). -/
lemma gS2_upper {a b c p q : ℕ} (hq : 0 < q) (x : ℕ) :
    GS2 a b c p q x ≤ (GBand a b c p q x).card * (p * x) ^ 2 := by
  unfold GS2
  calc (GBand a b c p q x).sum (fun s => s ^ 2)
      ≤ (GBand a b c p q x).sum (fun _ => (p * x) ^ 2) := by
        refine Finset.sum_le_sum (fun s hs => ?_)
        exact Nat.pow_le_pow_left (gband_le hq hs) 2
    _ = (GBand a b c p q x).card * (p * x) ^ 2 := by rw [Finset.sum_const, smul_eq_mul]

/-- One unit step moves `GS1` up by at most `p²(x+1)`: at most `p` entering elements,
each at most `p(x+1)`. -/
lemma gS1_step_upper {a b c p q : ℕ} (hq : 0 < q) (x : ℕ) :
    GS1 a b c p q (x + 1) ≤ GS1 a b c p q x + p * p * (x + 1) := by
  classical
  have hsplit :
      ((GBand a b c p q (x + 1)) \ (GBand a b c p q x)).sum id
        + ((GBand a b c p q (x + 1)) ∩ (GBand a b c p q x)).sum id
      = GS1 a b c p q (x + 1) := by
    rw [← Finset.sdiff_inter_self_left (GBand a b c p q (x + 1)) (GBand a b c p q x)]
    exact Finset.sum_sdiff Finset.inter_subset_left
  have h1 : ((GBand a b c p q (x + 1)) ∩ (GBand a b c p q x)).sum id ≤ GS1 a b c p q x :=
    Finset.sum_le_sum_of_subset Finset.inter_subset_right
  set E : Finset ℕ := (GBand a b c p q (x + 1)) \ (GBand a b c p q x) with hE
  have hEprop : ∀ s ∈ E, p * x ≤ q * s ∧ q * s < p * (x + 1) := by
    intro s hs
    obtain ⟨hmem, hnot⟩ := Finset.mem_sdiff.mp hs
    obtain ⟨hS, hge, hlt⟩ := of_mem_GBand hmem
    refine ⟨?_, hlt⟩
    by_contra hcon
    push_neg at hcon
    exact hnot ((mem_GBand hq).mpr ⟨hS, by omega, hcon⟩)
  have hcard : E.card ≤ p := by
    have hmaps : ∀ s ∈ E, q * s ∈ Finset.Ico (p * x) (p * x + p) := by
      intro s hs
      obtain ⟨h2, h3⟩ := hEprop s hs
      rw [Finset.mem_Ico]
      refine ⟨h2, ?_⟩
      have : p * (x + 1) = p * x + p := by ring
      omega
    have hinj : Set.InjOn (fun s => q * s) E := by
      intro s hs t ht hst
      exact Nat.eq_of_mul_eq_mul_left hq hst
    have h4 := Finset.card_le_card_of_injOn (fun s => q * s) hmaps hinj
    rwa [Nat.card_Ico, Nat.add_sub_cancel_left] at h4
  have helem : ∀ s ∈ E, id s ≤ p * (x + 1) := by
    intro s hs
    obtain ⟨-, h3⟩ := hEprop s hs
    have hle : s ≤ q * s := Nat.le_mul_of_pos_left s hq
    exact le_of_lt (lt_of_le_of_lt hle h3)
  have h2 : E.sum id ≤ p * p * (x + 1) := by
    calc E.sum id ≤ E.card • (p * (x + 1)) := Finset.sum_le_card_nsmul E id _ helem
      _ = E.card * (p * (x + 1)) := smul_eq_mul _ _
      _ ≤ p * (p * (x + 1)) := Nat.mul_le_mul_right _ hcard
      _ = p * p * (x + 1) := by ring
  omega

end Erdos123Band
