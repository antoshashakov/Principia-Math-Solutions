import Mathlib

set_option maxHeartbeats 4000000

/-!
# P1: `DataN` — the polynomial-carrying counterexample structure, parametric in `n`

Port of `Sendov9/Data.lean` (verified degree-9 module) over a general degree `n ≥ 2`.
All degree-specific numerals (`9`, `Fin 8`, `coeff 8`) become `n`, `Fin (n-1)`,
`coeff (n-1)`; card goals close by `omega`/`Nat` lemmas.

`SendovN.Extract` is the degree-9 `Sendov9.Extract` inlined verbatim (it was already
fully generic in `n`); the playground package cannot import the sendov9-11 package.
-/

namespace SendovN.Extract

open Finset

/-- Index a multiset of known cardinality by `Fin n`. -/
noncomputable def ofMultiset {n : ℕ} (s : Multiset ℂ) (h : Multiset.card s = n) (i : Fin n) : ℂ :=
  s.toList.get (Fin.cast (((Multiset.length_toList s).trans h).symm) i)

/-- Every indexed element belongs to the multiset. -/
theorem mem_ofMultiset {n : ℕ} (s : Multiset ℂ) (h : Multiset.card s = n) (i : Fin n) :
    ofMultiset s h i ∈ s := by
  have : ofMultiset s h i ∈ s.toList := List.get_mem _ _
  rwa [← Multiset.mem_coe, Multiset.coe_toList] at this

/-- Products transfer. -/
theorem prod_ofMultiset {n : ℕ} (s : Multiset ℂ) (h : Multiset.card s = n) :
    ∏ i, ofMultiset s h i = s.prod := by
  have hlen : n = s.toList.length := ((Multiset.length_toList s).trans h).symm
  have h1 : ∏ i : Fin n, s.toList.get (Fin.cast hlen i)
      = ∏ i : Fin s.toList.length, s.toList.get i := Fin.prod_congr' _ hlen
  calc ∏ i, ofMultiset s h i = ∏ i : Fin n, s.toList.get (Fin.cast hlen i) := rfl
    _ = ∏ i : Fin s.toList.length, s.toList.get i := h1
    _ = ∏ i : Fin s.toList.length, s.toList[i.1] := by
        exact Finset.prod_congr rfl fun i _ => by rw [List.get_eq_getElem]
    _ = s.toList.prod := Fin.prod_univ_getElem _
    _ = s.prod := Multiset.prod_toList s

/-- Sums transfer. -/
theorem sum_ofMultiset {n : ℕ} (s : Multiset ℂ) (h : Multiset.card s = n) :
    ∑ i, ofMultiset s h i = s.sum := by
  have hlen : n = s.toList.length := ((Multiset.length_toList s).trans h).symm
  have h1 : ∑ i : Fin n, s.toList.get (Fin.cast hlen i)
      = ∑ i : Fin s.toList.length, s.toList.get i := Fin.sum_congr' _ hlen
  calc ∑ i, ofMultiset s h i = ∑ i : Fin n, s.toList.get (Fin.cast hlen i) := rfl
    _ = ∑ i : Fin s.toList.length, s.toList.get i := h1
    _ = ∑ i : Fin s.toList.length, s.toList[i.1] := by
        exact Finset.sum_congr rfl fun i _ => by rw [List.get_eq_getElem]
    _ = s.toList.sum := Fin.sum_univ_getElem _
    _ = s.sum := Multiset.sum_toList s

/-- A function of the indexed family has the same product as the mapped multiset. -/
theorem prod_map_ofMultiset {n : ℕ} (s : Multiset ℂ) (h : Multiset.card s = n) (f : ℂ → ℂ) :
    ∏ i, f (ofMultiset s h i) = (s.map f).prod := by
  have hlen : n = s.toList.length := ((Multiset.length_toList s).trans h).symm
  have h1 : ∏ i : Fin n, f (s.toList.get (Fin.cast hlen i))
      = ∏ i : Fin s.toList.length, f (s.toList.get i) :=
    Fin.prod_congr' (fun i => f (s.toList.get i)) hlen
  calc ∏ i, f (ofMultiset s h i)
      = ∏ i : Fin n, f (s.toList.get (Fin.cast hlen i)) := rfl
    _ = ∏ i : Fin s.toList.length, f (s.toList.get i) := h1
    _ = ∏ i : Fin s.toList.length, f s.toList[i.1] := by
        exact Finset.prod_congr rfl fun i _ => by rw [List.get_eq_getElem]
    _ = (s.toList.map f).prod := Fin.prod_univ_fun_getElem _ f
    _ = (s.map f).prod := by
        rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]

/-- The additive sibling of `prod_map_ofMultiset`. -/
theorem sum_map_ofMultiset {n : ℕ} (s : Multiset ℂ) (h : Multiset.card s = n) (f : ℂ → ℂ) :
    ∑ i, f (ofMultiset s h i) = (s.map f).sum := by
  have hlen : n = s.toList.length := ((Multiset.length_toList s).trans h).symm
  have h1 : ∑ i : Fin n, f (s.toList.get (Fin.cast hlen i))
      = ∑ i : Fin s.toList.length, f (s.toList.get i) :=
    Fin.sum_congr' (fun i => f (s.toList.get i)) hlen
  calc ∑ i, f (ofMultiset s h i)
      = ∑ i : Fin n, f (s.toList.get (Fin.cast hlen i)) := rfl
    _ = ∑ i : Fin s.toList.length, f (s.toList.get i) := h1
    _ = ∑ i : Fin s.toList.length, f s.toList[i.1] := by
        exact Finset.sum_congr rfl fun i _ => by rw [List.get_eq_getElem]
    _ = (s.toList.map f).sum := Fin.sum_univ_fun_getElem _ f
    _ = (s.map f).sum := by
        rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList]

end SendovN.Extract


namespace SendovN.Anchor2

open Polynomial Finset

/-!
### The anchors, parametric in `n`

Everything below is `Sendov9.Anchor2` with `9` replaced by a general `n` (with
`1 ≤ n` where the leading coefficient of `p'` must be nonzero as a natural number,
and `(n : ℂ) ≠ 0` obtained from `Nat.cast_ne_zero`).
-/

theorem card_roots_eq (p : ℂ[X]) : Multiset.card p.roots = p.natDegree := by
  have h : (p.map (RingHom.id ℂ)).Splits := IsAlgClosed.splits_codomain p
  rw [Polynomial.map_id] at h
  exact splits_iff_card_roots.mp h

theorem monic_factorization {p : ℂ[X]} (hm : p.Monic) :
    (p.roots.map fun r => X - C r).prod = p :=
  prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (card_roots_eq p)

theorem factor_out {p : ℂ[X]} (hm : p.Monic) {a : ℂ} (ha : a ∈ p.roots) :
    p = (X - C a) * ((p.roots.erase a).map fun r => X - C r).prod := by
  conv_lhs => rw [← monic_factorization hm, ← Multiset.cons_erase ha]
  rw [Multiset.map_cons, Multiset.prod_cons]

/-- `(p')_{n-1} = n` for monic `p` of degree `n ≥ 1`. -/
theorem derivative_coeff_top {p : ℂ[X]} (hm : p.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : p.natDegree = n) : (derivative p).coeff (n - 1) = n := by
  rw [Polynomial.coeff_derivative]
  have hs : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
  have hc : p.coeff (n - 1 + 1) = 1 := by
    rw [hs]
    have := hm.coeff_natDegree
    rwa [hdeg] at this
  rw [hc, one_mul]
  exact_mod_cast congrArg (fun m : ℕ => (m : ℂ)) hs

theorem derivative_natDegree {p : ℂ[X]} {n : ℕ} (hdeg : p.natDegree = n) :
    (derivative p).natDegree = n - 1 := by
  rw [Polynomial.natDegree_derivative, hdeg]

theorem derivative_leadingCoeff {p : ℂ[X]} (hm : p.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : p.natDegree = n) : (derivative p).leadingCoeff = n := by
  rw [Polynomial.leadingCoeff, derivative_natDegree hdeg]
  exact derivative_coeff_top hm hn hdeg

theorem derivative_factorization {p : ℂ[X]} (hm : p.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : p.natDegree = n) :
    C (n : ℂ) * ((derivative p).roots.map fun z => X - C z).prod = derivative p := by
  have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_eq (derivative p))
  rwa [derivative_leadingCoeff hm hn hdeg] at h

theorem derivative_eval_prod {p : ℂ[X]} (hm : p.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : p.natDegree = n) (x : ℂ) :
    (derivative p).eval x = n * ((derivative p).roots.map fun z => x - z).prod := by
  conv_lhs => rw [← derivative_factorization hm hn hdeg]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun r _ => ?_
  simp

theorem derivative_eval_at_root {p : ℂ[X]} (hm : p.Monic) {a : ℂ} (ha : a ∈ p.roots) :
    (derivative p).eval a = ((p.roots.erase a).map fun r => a - r).prod := by
  set g : ℂ[X] := ((p.roots.erase a).map fun r => X - C r).prod with hg
  have hfac : p = (X - C a) * g := factor_out hm ha
  have hd : derivative p = g + (X - C a) * derivative g := by
    rw [hfac, derivative_mul]
    congr 1
    simp
  rw [hd, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, hg,
    eval_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun r _ => ?_
  simp

/-- **First anchor**: `n·∏ⱼ(a − ζⱼ) = ∏ₖ(a − zₖ)` (multiset form). -/
theorem anchor_one {p : ℂ[X]} (hm : p.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : p.natDegree = n) {a : ℂ} (ha : a ∈ p.roots) :
    (n : ℂ) * ((derivative p).roots.map fun z => a - z).prod
      = ((p.roots.erase a).map fun r => a - r).prod := by
  rw [← derivative_eval_prod hm hn hdeg a, derivative_eval_at_root hm ha]

theorem prod_split {s : Multiset ℂ} {a i : ℂ} (hi : i ∈ s) :
    (s.map fun r => a - r).prod = (a - i) * ((s.erase i).map fun r => a - r).prod := by
  conv_lhs => rw [← Multiset.cons_erase hi]
  rw [Multiset.map_cons, Multiset.prod_cons]

/-- The log-derivative identity. -/
theorem logderiv_eval {s : Multiset ℂ} {a : ℂ} (h : ∀ r ∈ s, a - r ≠ 0) :
    (derivative ((s.map fun r => X - C r).prod)).eval a
      = ((s.map fun r => a - r).prod) * ((s.map fun r => (a - r)⁻¹).sum) := by
  have heval : ∀ M : Multiset ℂ[X], eval a M.sum = (M.map fun q => eval a q).sum := by
    intro M
    induction M using Multiset.induction with
    | empty => simp
    | cons q M ih => simp [ih]
  rw [derivative_prod, heval, Multiset.map_map]
  have hterm : ∀ i ∈ s,
      ((fun q => eval a q) ∘ fun i => (Multiset.map (fun r => X - C r) (s.erase i)).prod
        * derivative (X - C i)) i
        = ((s.map fun r => a - r).prod) * (a - i)⁻¹ := by
    intro i hi
    have hne : a - i ≠ 0 := h i hi
    simp only [Function.comp_apply, derivative_sub, derivative_X, derivative_C,
      sub_zero, eval_one, mul_one, eval_multiset_prod, Multiset.map_map,
      eval_sub, eval_X, eval_C]
    rw [prod_split hi]
    field_simp
  rw [Multiset.map_congr rfl hterm, Multiset.sum_map_mul_left]

/-- The factor-of-two. -/
theorem second_derivative_at_root {g : ℂ[X]} {a : ℂ} :
    (derivative (derivative ((X - C a) * g))).eval a = 2 * (derivative g).eval a := by
  have h1 : derivative ((X - C a) * g) = g + (X - C a) * derivative g := by
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  rw [h1]
  simp only [derivative_add, derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
    add_zero]
  ring

/-- **No remaining zero equals `a`.** -/
theorem erase_ne_zero {p : ℂ[X]} (hm : p.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : p.natDegree = n) {a : ℂ} (ha : a ∈ p.roots)
    (hwne : ∀ w ∈ (derivative p).roots, a - w ≠ 0) :
    ∀ r ∈ p.roots.erase a, a - r ≠ 0 := by
  intro r hr hr0
  have hzero : ((p.roots.erase a).map fun r => a - r).prod = 0 := by
    rw [prod_split hr, hr0, zero_mul]
  rw [← anchor_one hm hn hdeg ha] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (Nat.cast_eq_zero.mp h) (by omega)
  · rw [Multiset.prod_eq_zero_iff] at h
    obtain ⟨w, hw, hw0⟩ := Multiset.mem_map.mp h
    exact hwne w hw hw0

/-- **Second anchor**: `∑ⱼ Yⱼ = 2 ∑ₖ Xₖ` (multiset form), derived from `p`. -/
theorem second_anchor {p : ℂ[X]} (hm : p.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : p.natDegree = n) {a : ℂ} (ha : a ∈ p.roots)
    (hwne : ∀ w ∈ (derivative p).roots, a - w ≠ 0) :
    (((derivative p).roots).map fun w => (a - w)⁻¹).sum
      = 2 * ((p.roots.erase a).map fun r => (a - r)⁻¹).sum := by
  have hzne : ∀ r ∈ p.roots.erase a, a - r ≠ 0 := erase_ne_zero hm hn hdeg ha hwne
  set g : ℂ[X] := ((p.roots.erase a).map fun r => X - C r).prod with hg
  have h2 : (derivative (derivative p)).eval a = 2 * (derivative g).eval a := by
    conv_lhs => rw [factor_out hm ha]
    exact second_derivative_at_root
  have h9 : (derivative (derivative p)).eval a
      = (n : ℂ) * ((((derivative p).roots).map fun w => a - w).prod
             * ((((derivative p).roots).map fun w => (a - w)⁻¹).sum)) := by
    conv_lhs => rw [← derivative_factorization hm hn hdeg]
    rw [derivative_C_mul, eval_mul, eval_C, logderiv_eval hwne]
  have hgd : (derivative g).eval a
      = ((p.roots.erase a).map fun r => a - r).prod
        * (((p.roots.erase a).map fun r => (a - r)⁻¹).sum) := by
    rw [hg]
    exact logderiv_eval hzne
  have hanc : (n : ℂ) * (((derivative p).roots).map fun w => a - w).prod
      = ((p.roots.erase a).map fun r => a - r).prod := anchor_one hm hn hdeg ha
  have hne : ((p.roots.erase a).map fun r => a - r).prod ≠ 0 := by
    rw [Ne, Multiset.prod_eq_zero_iff]
    intro hmem
    obtain ⟨r, hr, hr0⟩ := Multiset.mem_map.mp hmem
    exact hzne r hr hr0
  have key : (n : ℂ) * ((((derivative p).roots).map fun w => a - w).prod
      * ((((derivative p).roots).map fun w => (a - w)⁻¹).sum))
      = 2 * (((p.roots.erase a).map fun r => a - r).prod
        * (((p.roots.erase a).map fun r => (a - r)⁻¹).sum)) := by
    rw [← h9, h2, hgd]
  rw [← hanc] at key
  refine mul_left_cancel₀ hne ?_
  rw [← hanc]
  linear_combination key

end SendovN.Anchor2

namespace SendovN

open Polynomial Finset

/-- **The counterexample data at general degree `n ≥ 2`, carrying `p`.**
Only genuinely-assumed facts appear as fields; the zeros, the critical points and
both anchors are derived below. -/
structure DataN (n : ℕ) where
  hn : 2 ≤ n
  p : ℂ[X]
  hmonic : p.Monic
  hdeg : p.natDegree = n
  a : ℝ
  ha0 : 0 ≤ a
  ha1 : a ≤ 1
  haroot : (a : ℂ) ∈ p.roots
  hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1
  /-- the counterexample assumption: no critical point is within distance `1` of `a` -/
  hcrit : ∀ w ∈ (derivative p).roots, 1 < ‖(a : ℂ) - w‖

namespace DataN

variable {n : ℕ} (D : DataN n)

include D in
theorem hn1 : 1 ≤ n := le_trans one_le_two D.hn

theorem zcard : Multiset.card (D.p.roots.erase (D.a : ℂ)) = n - 1 := by
  have hcn : Multiset.card D.p.roots = n := by
    rw [Anchor2.card_roots_eq, D.hdeg]
  rw [Multiset.card_erase_of_mem D.haroot, hcn]
  exact Nat.pred_eq_sub_one

theorem zetacard : Multiset.card (derivative D.p).roots = n - 1 := by
  rw [Anchor2.card_roots_eq, Anchor2.derivative_natDegree D.hdeg]

/-- The `n − 1` remaining zeros. -/
noncomputable def z : Fin (n - 1) → ℂ := Extract.ofMultiset _ D.zcard

/-- The `n − 1` critical points. -/
noncomputable def zeta : Fin (n - 1) → ℂ := Extract.ofMultiset _ D.zetacard

theorem z_mem (k : Fin (n - 1)) : D.z k ∈ D.p.roots.erase (D.a : ℂ) :=
  Extract.mem_ofMultiset _ _ k

theorem zeta_mem (j : Fin (n - 1)) : D.zeta j ∈ (derivative D.p).roots :=
  Extract.mem_ofMultiset _ _ j

/-- Every remaining zero is in the closed unit disk. -/
theorem hz (k : Fin (n - 1)) : ‖D.z k‖ ≤ 1 :=
  D.hroots _ (Multiset.mem_of_mem_erase (D.z_mem k))

/-- Every critical point is strictly farther than `1` from `a`. -/
theorem hzeta (j : Fin (n - 1)) : 1 < ‖(D.a : ℂ) - D.zeta j‖ :=
  D.hcrit _ (D.zeta_mem j)

theorem zeta_ne (j : Fin (n - 1)) : (D.a : ℂ) - D.zeta j ≠ 0 := by
  intro h
  have := D.hzeta j
  rw [h, norm_zero] at this
  linarith

theorem crit_ne : ∀ w ∈ (derivative D.p).roots, (D.a : ℂ) - w ≠ 0 := by
  intro w hw h
  have := D.hcrit w hw
  rw [h, norm_zero] at this
  linarith

/-- **First anchor, derived.**  `n ∏ⱼ(a − ζⱼ) = ∏ₖ(a − zₖ)`. -/
theorem hprod : (n : ℂ) * ∏ j, ((D.a : ℂ) - D.zeta j) = ∏ k, ((D.a : ℂ) - D.z k) := by
  rw [show (∏ j, ((D.a : ℂ) - D.zeta j))
        = (((derivative D.p).roots).map fun w => (D.a : ℂ) - w).prod from
      Extract.prod_map_ofMultiset _ D.zetacard (fun w => (D.a : ℂ) - w),
    show (∏ k, ((D.a : ℂ) - D.z k))
        = ((D.p.roots.erase (D.a : ℂ)).map fun r => (D.a : ℂ) - r).prod from
      Extract.prod_map_ofMultiset _ D.zcard (fun r => (D.a : ℂ) - r)]
  exact Anchor2.anchor_one D.hmonic D.hn1 D.hdeg D.haroot

/-- **Second anchor, derived.**  `∑ⱼ Yⱼ = 2 ∑ₖ Xₖ`. -/
theorem hsum : ∑ j, ((D.a : ℂ) - D.zeta j)⁻¹ = 2 * ∑ k, ((D.a : ℂ) - D.z k)⁻¹ := by
  rw [show (∑ j, ((D.a : ℂ) - D.zeta j)⁻¹)
        = (((derivative D.p).roots).map fun w => ((D.a : ℂ) - w)⁻¹).sum from
      Extract.sum_map_ofMultiset _ D.zetacard (fun w => ((D.a : ℂ) - w)⁻¹),
    show (∑ k, ((D.a : ℂ) - D.z k)⁻¹)
        = ((D.p.roots.erase (D.a : ℂ)).map fun r => ((D.a : ℂ) - r)⁻¹).sum from
      Extract.sum_map_ofMultiset _ D.zcard (fun r => ((D.a : ℂ) - r)⁻¹)]
  exact Anchor2.second_anchor D.hmonic D.hn1 D.hdeg D.haroot D.crit_ne

end DataN

end SendovN

#print axioms SendovN.Extract.sum_map_ofMultiset
#print axioms SendovN.Anchor2.anchor_one
#print axioms SendovN.Anchor2.second_anchor
#print axioms SendovN.DataN.zcard
#print axioms SendovN.DataN.zetacard
#print axioms SendovN.DataN.hz
#print axioms SendovN.DataN.hzeta
#print axioms SendovN.DataN.zeta_ne
#print axioms SendovN.DataN.crit_ne
#print axioms SendovN.DataN.hprod
#print axioms SendovN.DataN.hsum
