import Mathlib

set_option maxHeartbeats 4000000

/-!
# The refactor: a `Counterexample` built from `p`, not assumed

`Bridge5.lean` showed the `Counterexample` structure is under-specified — its two
anchors pin `p'` and `p''` down only at `a`, so `|I| < a/9` is not reachable from it.
The fix is to carry `p` itself and *derive* the anchors.  `Anchor2.second_anchor`
supplied the last missing derivation; this file performs the refactor.

`Data` assumes only what a genuine degree-nine counterexample would give you: a monic
`p` of degree 9, a real root `a ∈ [0,1]`, every root in the closed unit disk, and
every critical point strictly farther than `1` from `a`.  Everything the old
structure took as given — the eight remaining zeros, the eight critical points,
`hprod`, `hsum` — comes out as a theorem.

`sum_map_ofMultiset` is the additive sibling `Extract.lean` never needed until now;
`hsum` is the first statement in the campaign that transfers a *sum* rather than a
product across the `Multiset`/`Fin 8` boundary.
-/



namespace Sendov9.Extract

open Finset

/-!
# Indexing a multiset of known cardinality by `Fin n`

The whole development is stated over families `Fin 8 → ℂ`, but `Polynomial.roots`
delivers a `Multiset ℂ`.  This file is the adapter: given `card s = n`, index `s` by
`Fin n` and transfer products, sums and membership.

It is the reusable core of the polynomial bridge — the roots of `p` (minus the
distinguished one) and the roots of `p'` are both obtained this way.
-/

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
  have hcard : Multiset.card (s.map f) = n := by rw [Multiset.card_map]; exact h
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
        -- the idiom Mathlib itself uses (Multiset/Defs.lean): push through the coe
        rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]

end Sendov9.Extract


namespace Sendov9.Anchor2

open Polynomial Finset

/-!
# The second anchor, derived: `∑ⱼ Yⱼ = 2 ∑ₖ Xₖ`

`Bridge3.lean` banked the log-derivative identity and the factor-of-two, but never
combined them, so `hsum` was still an axiom of the `Counterexample` structure rather
than a consequence of `p`.  This file derives it, which is the last piece needed to
refactor `Counterexample` into a structure carrying `p` (see `Bridge5.lean`'s header
for why that refactor is forced).

The chain evaluates `p''(a)` two ways:

* through the zeros — `p = (X - a)·g` gives `p''(a) = 2g'(a)`, and the log-derivative
  identity gives `g'(a) = ∏ₖ(a - zₖ)·∑ₖXₖ`;
* through the critical points — `p' = 9∏ⱼ(X - ζⱼ)` gives
  `p''(a) = 9·∏ⱼ(a - ζⱼ)·∑ⱼYⱼ`.

Equating and cancelling the common factor `∏ₖ(a - zₖ) = 9∏ⱼ(a - ζⱼ)` (nonzero) leaves
`∑ⱼYⱼ = 2∑ₖXₖ`.

`erase_ne_zero` is the small fact that makes the cancellation legal: no remaining zero
equals `a`.  It is the multiplicity argument — if `a` were a repeated root then
`p'(a) = 0`, but `p'(a) = 9∏ⱼ(a - ζⱼ)` and every critical point is at distance `> 1`.
-/

/-! ### Restated inputs -/

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

theorem derivative_coeff_eight {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9) :
    (derivative p).coeff 8 = 9 := by
  rw [Polynomial.coeff_derivative]
  have hc : p.coeff 9 = 1 := by
    have := hm.coeff_natDegree
    rwa [hdeg] at this
  rw [show (8:ℕ) + 1 = 9 from rfl, hc]
  norm_num

theorem derivative_natDegree {p : ℂ[X]} (hdeg : p.natDegree = 9) :
    (derivative p).natDegree = 8 := by
  rw [Polynomial.natDegree_derivative, hdeg]

theorem derivative_leadingCoeff {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9) :
    (derivative p).leadingCoeff = 9 := by
  rw [Polynomial.leadingCoeff, derivative_natDegree hdeg]
  exact derivative_coeff_eight hm hdeg

theorem derivative_factorization {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9) :
    C (9:ℂ) * ((derivative p).roots.map fun z => X - C z).prod = derivative p := by
  have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_eq (derivative p))
  rwa [derivative_leadingCoeff hm hdeg] at h

theorem derivative_eval_prod {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9) (x : ℂ) :
    (derivative p).eval x = 9 * ((derivative p).roots.map fun z => x - z).prod := by
  conv_lhs => rw [← derivative_factorization hm hdeg]
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

theorem anchor_one {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9)
    {a : ℂ} (ha : a ∈ p.roots) :
    9 * ((derivative p).roots.map fun z => a - z).prod
      = ((p.roots.erase a).map fun r => a - r).prod := by
  rw [← derivative_eval_prod hm hdeg a, derivative_eval_at_root hm ha]

theorem prod_split {s : Multiset ℂ} {a i : ℂ} (hi : i ∈ s) :
    (s.map fun r => a - r).prod = (a - i) * ((s.erase i).map fun r => a - r).prod := by
  conv_lhs => rw [← Multiset.cons_erase hi]
  rw [Multiset.map_cons, Multiset.prod_cons]

/-- The log-derivative identity (from `Bridge3.lean`). -/
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

/-- The factor-of-two (from `Bridge3.lean`). -/
theorem second_derivative_at_root {g : ℂ[X]} {a : ℂ} :
    (derivative (derivative ((X - C a) * g))).eval a = 2 * (derivative g).eval a := by
  have h1 : derivative ((X - C a) * g) = g + (X - C a) * derivative g := by
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  rw [h1]
  simp only [derivative_add, derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
    add_zero]
  ring

/-! ### `a` is a simple root -/

/-- **No remaining zero equals `a`.**  If one did, `p'(a) = ∏ₖ(a - zₖ)` would vanish;
but `p'(a) = 9∏ⱼ(a - ζⱼ)` and every critical point is at distance `> 1` from `a`. -/
theorem erase_ne_zero {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9)
    {a : ℂ} (ha : a ∈ p.roots)
    (hwne : ∀ w ∈ (derivative p).roots, a - w ≠ 0) :
    ∀ r ∈ p.roots.erase a, a - r ≠ 0 := by
  intro r hr hr0
  have hzero : ((p.roots.erase a).map fun r => a - r).prod = 0 := by
    rw [prod_split hr, hr0, zero_mul]
  rw [← anchor_one hm hdeg ha] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · norm_num at h
  · rw [Multiset.prod_eq_zero_iff] at h
    obtain ⟨w, hw, hw0⟩ := Multiset.mem_map.mp h
    exact hwne w hw hw0

/-! ### The second anchor -/

/-- **`∑ⱼ Yⱼ = 2 ∑ₖ Xₖ`**, derived from `p` rather than assumed. -/
theorem second_anchor {p : ℂ[X]} (hm : p.Monic) (hdeg : p.natDegree = 9)
    {a : ℂ} (ha : a ∈ p.roots)
    (hwne : ∀ w ∈ (derivative p).roots, a - w ≠ 0) :
    (((derivative p).roots).map fun w => (a - w)⁻¹).sum
      = 2 * ((p.roots.erase a).map fun r => (a - r)⁻¹).sum := by
  have hzne : ∀ r ∈ p.roots.erase a, a - r ≠ 0 := erase_ne_zero hm hdeg ha hwne
  set g : ℂ[X] := ((p.roots.erase a).map fun r => X - C r).prod with hg
  -- `p''(a) = 2 g'(a)`
  have h2 : (derivative (derivative p)).eval a = 2 * (derivative g).eval a := by
    conv_lhs => rw [factor_out hm ha]
    exact second_derivative_at_root
  -- `p''(a) = 9 ∏ⱼ(a - ζⱼ) ∑ⱼ Yⱼ`
  have h9 : (derivative (derivative p)).eval a
      = 9 * ((((derivative p).roots).map fun w => a - w).prod
             * ((((derivative p).roots).map fun w => (a - w)⁻¹).sum)) := by
    conv_lhs => rw [← derivative_factorization hm hdeg]
    rw [derivative_C_mul, eval_mul, eval_C, logderiv_eval hwne]
  -- `g'(a) = ∏ₖ(a - zₖ) ∑ₖ Xₖ`
  have hgd : (derivative g).eval a
      = ((p.roots.erase a).map fun r => a - r).prod
        * (((p.roots.erase a).map fun r => (a - r)⁻¹).sum) := by
    rw [hg]
    exact logderiv_eval hzne
  have hanc : 9 * (((derivative p).roots).map fun w => a - w).prod
      = ((p.roots.erase a).map fun r => a - r).prod := anchor_one hm hdeg ha
  have hne : ((p.roots.erase a).map fun r => a - r).prod ≠ 0 := by
    rw [Ne, Multiset.prod_eq_zero_iff]
    intro hmem
    obtain ⟨r, hr, hr0⟩ := Multiset.mem_map.mp hmem
    exact hzne r hr hr0
  have key : 9 * ((((derivative p).roots).map fun w => a - w).prod
      * ((((derivative p).roots).map fun w => (a - w)⁻¹).sum))
      = 2 * (((p.roots.erase a).map fun r => a - r).prod
        * (((p.roots.erase a).map fun r => (a - r)⁻¹).sum)) := by
    rw [← h9, h2, hgd]
  rw [← hanc] at key
  refine mul_left_cancel₀ hne ?_
  rw [← hanc]
  linear_combination key

end Sendov9.Anchor2

namespace Sendov9.Extract

open Finset

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

end Sendov9.Extract

namespace Sendov9

open Polynomial Finset

/-- **The counterexample data, carrying `p`.**  Only genuinely-assumed facts appear
as fields; the zeros, the critical points and both anchors are derived below. -/
structure Data where
  p : ℂ[X]
  hmonic : p.Monic
  hdeg : p.natDegree = 9
  a : ℝ
  ha0 : 0 ≤ a
  ha1 : a ≤ 1
  haroot : (a : ℂ) ∈ p.roots
  hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1
  /-- the counterexample assumption: no critical point is within distance `1` of `a` -/
  hcrit : ∀ w ∈ (derivative p).roots, 1 < ‖(a : ℂ) - w‖

namespace Data

variable (D : Data)

theorem zcard : Multiset.card (D.p.roots.erase (D.a : ℂ)) = 8 := by
  have h9 : Multiset.card D.p.roots = 9 := by
    rw [Anchor2.card_roots_eq, D.hdeg]
  rw [Multiset.card_erase_of_mem D.haroot, h9]
  rfl

theorem zetacard : Multiset.card (derivative D.p).roots = 8 := by
  rw [Anchor2.card_roots_eq, Anchor2.derivative_natDegree D.hdeg]

/-- The eight remaining zeros. -/
noncomputable def z : Fin 8 → ℂ := Extract.ofMultiset _ D.zcard

/-- The eight critical points. -/
noncomputable def zeta : Fin 8 → ℂ := Extract.ofMultiset _ D.zetacard

theorem z_mem (k : Fin 8) : D.z k ∈ D.p.roots.erase (D.a : ℂ) :=
  Extract.mem_ofMultiset _ _ k

theorem zeta_mem (j : Fin 8) : D.zeta j ∈ (derivative D.p).roots :=
  Extract.mem_ofMultiset _ _ j

/-- Every remaining zero is in the closed unit disk. -/
theorem hz (k : Fin 8) : ‖D.z k‖ ≤ 1 :=
  D.hroots _ (Multiset.mem_of_mem_erase (D.z_mem k))

/-- Every critical point is strictly farther than `1` from `a`. -/
theorem hzeta (j : Fin 8) : 1 < ‖(D.a : ℂ) - D.zeta j‖ :=
  D.hcrit _ (D.zeta_mem j)

theorem zeta_ne (j : Fin 8) : (D.a : ℂ) - D.zeta j ≠ 0 := by
  intro h
  have := D.hzeta j
  rw [h, norm_zero] at this
  linarith

theorem crit_ne : ∀ w ∈ (derivative D.p).roots, (D.a : ℂ) - w ≠ 0 := by
  intro w hw h
  have := D.hcrit w hw
  rw [h, norm_zero] at this
  linarith

/-- **First anchor, derived.**  `9 ∏ⱼ(a - ζⱼ) = ∏ₖ(a - zₖ)`. -/
theorem hprod : 9 * ∏ j, ((D.a : ℂ) - D.zeta j) = ∏ k, ((D.a : ℂ) - D.z k) := by
  rw [show (∏ j, ((D.a : ℂ) - D.zeta j))
        = (((derivative D.p).roots).map fun w => (D.a : ℂ) - w).prod from
      Extract.prod_map_ofMultiset _ D.zetacard (fun w => (D.a : ℂ) - w),
    show (∏ k, ((D.a : ℂ) - D.z k))
        = ((D.p.roots.erase (D.a : ℂ)).map fun r => (D.a : ℂ) - r).prod from
      Extract.prod_map_ofMultiset _ D.zcard (fun r => (D.a : ℂ) - r)]
  exact Anchor2.anchor_one D.hmonic D.hdeg D.haroot

/-- **Second anchor, derived.**  `∑ⱼ Yⱼ = 2 ∑ₖ Xₖ`. -/
theorem hsum : ∑ j, ((D.a : ℂ) - D.zeta j)⁻¹ = 2 * ∑ k, ((D.a : ℂ) - D.z k)⁻¹ := by
  rw [show (∑ j, ((D.a : ℂ) - D.zeta j)⁻¹)
        = (((derivative D.p).roots).map fun w => ((D.a : ℂ) - w)⁻¹).sum from
      Extract.sum_map_ofMultiset _ D.zetacard (fun w => ((D.a : ℂ) - w)⁻¹),
    show (∑ k, ((D.a : ℂ) - D.z k)⁻¹)
        = ((D.p.roots.erase (D.a : ℂ)).map fun r => ((D.a : ℂ) - r)⁻¹).sum from
      Extract.sum_map_ofMultiset _ D.zcard (fun r => ((D.a : ℂ) - r)⁻¹)]
  exact Anchor2.second_anchor D.hmonic D.hdeg D.haroot D.crit_ne

end Data

/-- Verbatim copy of `Master.Counterexample`. -/
structure Counterexample where
  a : ℝ
  ha0 : 0 ≤ a
  ha1 : a ≤ 1
  z : Fin 8 → ℂ
  zeta : Fin 8 → ℂ
  hz : ∀ k, ‖z k‖ ≤ 1
  hzeta : ∀ j, 1 < ‖(a : ℂ) - zeta j‖
  hprod : 9 * ∏ j, ((a : ℂ) - zeta j) = ∏ k, ((a : ℂ) - z k)
  hsum : ∑ j, ((a : ℂ) - zeta j)⁻¹ = 2 * ∑ k, ((a : ℂ) - z k)⁻¹

/-- **The refactor.**  Every field of the old structure is now a theorem about `p`.
So the whole verified development downstream of `Counterexample` applies to a
genuine polynomial counterexample, with nothing smuggled in. -/
noncomputable def Data.toCounterexample (D : Data) : Counterexample where
  a := D.a
  ha0 := D.ha0
  ha1 := D.ha1
  z := D.z
  zeta := D.zeta
  hz := D.hz
  hzeta := D.hzeta
  hprod := D.hprod
  hsum := D.hsum

end Sendov9

#print axioms Sendov9.Extract.sum_map_ofMultiset
#print axioms Sendov9.Data.zcard
#print axioms Sendov9.Data.zetacard
#print axioms Sendov9.Data.hz
#print axioms Sendov9.Data.hzeta
#print axioms Sendov9.Data.zeta_ne
#print axioms Sendov9.Data.crit_ne
#print axioms Sendov9.Data.hprod
#print axioms Sendov9.Data.hsum
#print axioms Sendov9.Data.toCounterexample
