/-
Copyright (c) 2026 Principia. All rights reserved.
Released under Apache 2.0.
-/
-- `ℝ` is what the first draft forgot: without it the structure's `toFun : Set G → ℝ` field fails
-- to elaborate, the whole `structure` is rejected, and every later error in the file is a cascade
-- from that one.  The reported first error was a stuck `HAdd` instance three lines further down.
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# #371629 — mensural densities and Reiter sequences: the finitely additive layer

**The row.**  For probability masses `μ n ∈ ℓ¹(G)` on an infinite commutative discrete group,
`d̄(A) = limsup_n μ_n(A)` is an upper density in the sense of Révész–Ruzsa **iff**
`∑_x |μ_n(x) − μ_n(x+t)| → 0` for every `t` (the Reiter condition).  Sufficiency is noted in the
source; the substance is necessity, and its five steps are: dominated ultralimits → cyclic block
selectors → a swap argument → weak nullity → the **Schur property of ℓ¹**.

**What this module is.**  Steps one and three consume a *finitely additive probability defined on
every subset* of `G`, and the swap argument is where the proof's weight sits.  Both are stated here
and fully proved.  Nothing here mentions the group, the measures, or the density, so nothing here is
waiting on the parts that are hard.

**Why a bespoke structure rather than `MeasureTheory.AddContent`.**  `AddContent` is indexed by a
`SetSemiring` and its additivity is stated over `Finset`-indexed families drawn from that semiring.
Here the domain is *all* of `Set G` — the selector argument forms complements, differences and
arbitrary unions of selectors freely — so the semiring bookkeeping would be pure overhead on a
lattice where every operation is already available.  Four fields, and the semiring's own additivity
is recovered as `sum_biUnion` below.

**The one fact the whole selector argument runs on** is `eq_of_partition_pair`: two sets that
complete the *same* third set to the *same* total have equal measure.  In the source this is the
step from "both selectors have measure `1/L`" to `q(E+it) = q(E+jt)`, and it is where the
translation invariance actually comes from.  Stated with the group stripped out, it is four lines —
which is the point of stripping the group out.

**Known trap, avoided here.**  `union_diff_cancel` is deprecated in this Mathlib (the live name is
`union_sdiff_cancel`), so `mono` builds `A ∪ (B \ A) = B` by hand rather than quoting either.
-/

namespace Principia.MathDB.P371629

/-- A finitely additive probability measure defined on **every** subset of `G`. -/
structure FinAddProb (G : Type*) where
  /-- The measure of a set. -/
  toFun : Set G → ℝ
  /-- Measures are nonnegative. -/
  nonneg : ∀ A, 0 ≤ toFun A
  /-- The total mass is one. -/
  univ_eq : toFun Set.univ = 1
  /-- Finite additivity on disjoint pairs. -/
  additive : ∀ A B : Set G, Disjoint A B → toFun (A ∪ B) = toFun A + toFun B

namespace FinAddProb

variable {G : Type*} (q : FinAddProb G)

theorem empty : q.toFun ∅ = 0 := by
  have hd : Disjoint (Set.univ : Set G) (∅ : Set G) := by simp
  have h := q.additive Set.univ ∅ hd
  rw [Set.union_empty, q.univ_eq] at h
  linarith

/-- `B` splits as `A` and `B \ A`. -/
theorem eq_add_diff {A B : Set G} (h : A ⊆ B) :
    q.toFun B = q.toFun A + q.toFun (B \ A) := by
  have hset : A ∪ (B \ A) = B := by
    ext x
    constructor
    · rintro (hx | ⟨hx, -⟩)
      · exact h hx
      · exact hx
    · intro hx
      by_cases hA : x ∈ A
      · exact Or.inl hA
      · exact Or.inr ⟨hx, hA⟩
  have hd : Disjoint A (B \ A) := Set.disjoint_left.mpr fun x hx hx' => hx'.2 hx
  have := q.additive A (B \ A) hd
  rw [hset] at this
  exact this

theorem mono {A B : Set G} (h : A ⊆ B) : q.toFun A ≤ q.toFun B := by
  have := q.eq_add_diff h
  linarith [q.nonneg (B \ A)]

theorem le_one (A : Set G) : q.toFun A ≤ 1 := by
  have := q.mono (Set.subset_univ A)
  rw [q.univ_eq] at this
  exact this

/-- Finite additivity over a `Finset`-indexed pairwise disjoint family — the additivity an
`AddContent` on a semiring would give, recovered on the full power set. -/
theorem sum_biUnion {ι : Type*} [DecidableEq ι] (C : ι → Set G)
    (hd : Pairwise fun i j => Disjoint (C i) (C j)) (s : Finset ι) :
    q.toFun (⋃ i ∈ s, C i) = ∑ i ∈ s, q.toFun (C i) := by
  refine Finset.induction_on s ?_ ?_
  · simp [q.empty]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert, q.additive, ih]
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hd (by rintro rfl; exact ha hi)

end FinAddProb

/-! ### The swap argument, with the group stripped out -/

variable {G : Type*}

/-- **Two sets that complete the same third set to the same total have equal measure.**

This is the whole engine of the selector argument.  In the source, `X = E + it`, `Z = E + jt` and
`Y = (C₀ \ E) + jt`: the selector `S = X ∪ Y` has measure `1/L`, and so does `C_j = Z ∪ Y`, whence
`q(E+it) = q(E+jt)` — which is translation invariance in the making. -/
theorem eq_of_partition_pair (q : FinAddProb G) {X Y Z : Set G} {c : ℝ}
    (hXY : Disjoint X Y) (hXYq : q.toFun (X ∪ Y) = c)
    (hZY : Disjoint Z Y) (hZYq : q.toFun (Z ∪ Y) = c) :
    q.toFun X = q.toFun Z := by
  have h1 := q.additive X Y hXY
  have h2 := q.additive Z Y hZY
  rw [hXYq] at h1
  rw [hZYq] at h2
  linarith

/-- **Two disjoint sets, each capped by `c`, whose union has measure `2c`, both attain `c`.**

The source states this as "consequently both inequalities are equalities".  It is the step that
converts the *upper* bound `q(S) ≤ d̄(S) = 1/L` on selectors into the *exact* value needed. -/
theorem eq_of_le_of_union (q : FinAddProb G) {S S' : Set G} {c : ℝ}
    (hS : q.toFun S ≤ c) (hS' : q.toFun S' ≤ c) (hdisj : Disjoint S S')
    (hunion : q.toFun (S ∪ S') = 2 * c) :
    q.toFun S = c ∧ q.toFun S' = c := by
  have h := q.additive S S' hdisj
  rw [hunion] at h
  exact ⟨by linarith, by linarith⟩

/-- **A partition into `L` pieces each capped by `c`, with total `L · c`, has every piece at `c`.**

Applied with `c = 1/L` and the `L` translates `C_0, …, C_{L−1}`: domination gives `q(C_i) ≤ 1/L`,
the total is `q(G) = 1`, and the conclusion `q(C_i) = 1/L` is equation (7) of the source. -/
theorem eq_of_le_of_sum_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℝ)
    (hle : ∀ i ∈ s, f i ≤ c) (hsum : ∑ i ∈ s, f i = (s.card : ℝ) * c) :
    ∀ i ∈ s, f i = c := by
  refine (Finset.sum_eq_sum_iff_of_le hle).1 ?_
  rw [hsum, Finset.sum_const, nsmul_eq_mul]

/-- The partition form, stated directly against `sum_biUnion`: an `L`-piece partition of `G` whose
pieces are each capped by `c = 1/L` has every piece exactly `1/L`. -/
theorem eq_of_le_of_biUnion_univ (q : FinAddProb G) {ι : Type*} [DecidableEq ι]
    (C : ι → Set G) (hd : Pairwise fun i j => Disjoint (C i) (C j)) (s : Finset ι)
    (hcov : (⋃ i ∈ s, C i) = Set.univ) (hs : s.Nonempty)
    (hle : ∀ i ∈ s, q.toFun (C i) ≤ (s.card : ℝ)⁻¹) :
    ∀ i ∈ s, q.toFun (C i) = (s.card : ℝ)⁻¹ := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by
    have : 0 < s.card := Finset.card_pos.mpr hs
    exact_mod_cast this
  refine eq_of_le_of_sum_eq s (fun i => q.toFun (C i)) _ hle ?_
  rw [← q.sum_biUnion C hd s, hcov, q.univ_eq]
  field_simp


/-! ### Step 1: dominated ultralimits

The source's first step.  Every `μ n` takes values in `[0,1]`, which is compact, so the pushforward
ultrafilter converges; `choose` picks a limit for **every** subset at once, and the three
`FinAddProb` fields are three applications of uniqueness of limits.

Nothing here needs the ultrafilter to be free.  Freeness is wanted only for the *domination*
`q(A) ≤ limsup_n μ_n(A)`, which is what ties the ultralimit back to the density and is the next
brick. -/

/-- **An ultrafilter limit of finitely additive probabilities is one.** -/
theorem exists_finAddProb_ultralimit (U : Ultrafilter ℕ) (μ : ℕ → FinAddProb G) :
    ∃ q : FinAddProb G, ∀ A, Filter.Tendsto (fun n => (μ n).toFun A) U (nhds (q.toFun A)) := by
  have hex : ∀ A : Set G, ∃ x ∈ Set.Icc (0 : ℝ) 1,
      Filter.Tendsto (fun n => (μ n).toFun A) U (nhds x) := by
    intro A
    have hmap : ((Ultrafilter.map (fun n => (μ n).toFun A) U) : Filter ℝ)
        ≤ Filter.principal (Set.Icc 0 1) := by
      rw [Filter.le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
      filter_upwards with n
      simp only [Set.mem_preimage, Set.mem_Icc]
      exact ⟨(μ n).nonneg A, (μ n).le_one A⟩
    obtain ⟨x, hx, hle⟩ :=
      isCompact_Icc.ultrafilter_le_nhds (Ultrafilter.map (fun n => (μ n).toFun A) U) hmap
    refine ⟨x, hx, ?_⟩
    rwa [Filter.Tendsto, ← Ultrafilter.coe_map]
  choose f hf hlim using hex
  refine ⟨⟨f, fun A => (hf A).1, ?_, ?_⟩, hlim⟩
  · have he : (fun n => (μ n).toFun Set.univ) = fun _ => (1 : ℝ) :=
      funext fun n => (μ n).univ_eq
    have h1 := hlim Set.univ
    rw [he] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  · intro A B hd
    have he : (fun n => (μ n).toFun (A ∪ B)) = fun n => (μ n).toFun A + (μ n).toFun B :=
      funext fun n => (μ n).additive A B hd
    have h1 := hlim (A ∪ B)
    rw [he] at h1
    exact tendsto_nhds_unique h1 ((hlim A).add (hlim B))


/-! ### The domination, and where freeness is actually used

`q(A) ≤ limsup_n μ_n(A)` is the clause that ties the ultralimit back to the density, and it is the
**only** place the ultrafilter has to be free.  The mechanism is one line of filter algebra: a set
in a free ultrafilter cannot have its complement in `atTop`, or both would lie in the ultrafilter
and it would be `⊥`.  So every `U`-eventual statement is `atTop`-frequent, and frequent-below is
what `Filter.le_limsup_of_frequently_le` consumes.

Stated for a bare sequence rather than for `FinAddProb`, because that is all it is about; the
`FinAddProb` version is one line on top. -/

/-- **A limit along a free ultrafilter is at most the `limsup`.** -/
theorem le_limsup_of_tendsto_ultrafilter (U : Ultrafilter ℕ)
    (hfree : (U : Filter ℕ) ≤ Filter.atTop) (f : ℕ → ℝ) (L : ℝ)
    (hL : Filter.Tendsto f U (nhds L)) (hb : ∀ n, f n ≤ 1) :
    L ≤ Filter.limsup f Filter.atTop := by
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop f :=
    Filter.isBoundedUnder_of ⟨1, hb⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hfreq : ∃ᶠ n in Filter.atTop, L - ε ≤ f n := by
    by_contra hcon
    rw [Filter.not_frequently] at hcon
    -- `hfree` turns an `atTop`-eventual statement into a `U`-eventual one; the ultralimit gives
    -- the opposite one; an ultrafilter cannot hold both.
    have h1 : ∀ᶠ n in (U : Filter ℕ), ¬ (L - ε ≤ f n) := hfree hcon
    have h2 : ∀ᶠ n in (U : Filter ℕ), L - ε < f n :=
      hL.eventually (eventually_gt_nhds (by linarith))
    have h3 : ∀ᶠ _n in (U : Filter ℕ), False := by
      filter_upwards [h1, h2] with n hn1 hn2
      exact hn1 (le_of_lt hn2)
    obtain ⟨_, hfalse⟩ := h3.exists
    exact hfalse
  have hle := Filter.le_limsup_of_frequently_le hfreq hbdd
  linarith

/-- **Step 1 in the form the selector lemma consumes**: a free ultrafilter turns a sequence of
finitely additive probabilities into a single one dominated by the upper density. -/
theorem exists_finAddProb_le_limsup (U : Ultrafilter ℕ)
    (hfree : (U : Filter ℕ) ≤ Filter.atTop) (μ : ℕ → FinAddProb G) :
    ∃ q : FinAddProb G,
      ∀ A, q.toFun A ≤ Filter.limsup (fun n => (μ n).toFun A) Filter.atTop := by
  obtain ⟨q, hq⟩ := exists_finAddProb_ultralimit U μ
  exact ⟨q, fun A =>
    le_limsup_of_tendsto_ultrafilter U hfree _ _ (hq A) fun n => (μ n).le_one A⟩


/-! ### Step 4: weak nullity

The source argues by contradiction — "if (12) failed, then after passing to a subsequence and
choosing one sign there would be an `ε > 0` …, and a free ultrafilter concentrated on that
subsequence would give a non-translation-invariant `q_𝒰`".

None of that is needed.  `Filter.tendsto_iff_ultrafilter` says convergence along `atTop` **is**
convergence along every ultrafilter refining `atTop`, so the subsequence extraction, the sign
choice and the `ε` are all internal to a lemma Mathlib already has.  What remains is to observe
that along any such ultrafilter the two sequences converge to `q A` and `q B`, which agree.

This is the step where the earlier separation pays off: `exists_finAddProb_ultralimit` was proved
for an *arbitrary* ultrafilter, so it applies verbatim to the one `tendsto_iff_ultrafilter` hands
over, and freeness is carried only as a hypothesis to be passed along. -/

/-- **Weak nullity.**  If every free-ultrafilter limit of the measures gives `A` and `B` the same
mass, then `μ_n(A) − μ_n(B) → 0`. -/
theorem tendsto_sub_of_ultralimit_eq (μ : ℕ → FinAddProb G) (A B : Set G)
    (h : ∀ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ Filter.atTop →
      ∀ q : FinAddProb G,
        (∀ C, Filter.Tendsto (fun n => (μ n).toFun C) U (nhds (q.toFun C))) →
        q.toFun A = q.toFun B) :
    Filter.Tendsto (fun n => (μ n).toFun A - (μ n).toFun B) Filter.atTop (nhds 0) := by
  refine (Filter.tendsto_iff_ultrafilter _ _ _).2 fun U hU => ?_
  obtain ⟨q, hq⟩ := exists_finAddProb_ultralimit U μ
  have hAB := h U hU q hq
  have hsub := (hq A).sub (hq B)
  rwa [hAB, sub_self] at hsub

/-- The same statement with the invariance supplied as a property of the *sets* rather than of each
limit: if `A` and `B` are interchangeable under every dominated finitely additive probability, the
difference of the measures is null. -/
theorem tendsto_sub_of_forall_dominated (μ : ℕ → FinAddProb G) (d : Set G → ℝ) (A B : Set G)
    (hdom : ∀ (q : FinAddProb G), (∀ C, q.toFun C ≤ d C) → q.toFun A = q.toFun B)
    (hle : ∀ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ Filter.atTop →
      ∀ q : FinAddProb G,
        (∀ C, Filter.Tendsto (fun n => (μ n).toFun C) U (nhds (q.toFun C))) →
        ∀ C, q.toFun C ≤ d C) :
    Filter.Tendsto (fun n => (μ n).toFun A - (μ n).toFun B) Filter.atTop (nhds 0) :=
  tendsto_sub_of_ultralimit_eq μ A B fun U hU q hq => hdom q (hle U hU q hq)


section Height

variable [AddCommGroup G]

/-! ### Step 2: the cyclic blocks, as residue classes of a height

The source builds the blocks from a transversal `R` for the cosets of `⟨t⟩`, cuts each `t`-orbit
into consecutive `L`-blocks, and sets `C_i` to be the `i`-th points of all blocks.  Every element of
that construction — the transversal, the orbit, the block index — collapses into **one** object: an
integer coordinate along the orbit,

  `k : G → ℤ`  with  `k (x + t) = k x + 1`,

and the classes are then the fibres of `k` modulo `L`.  A transversal is exactly what is needed to
*produce* such a `k`, so nothing is being assumed away; what changes is that the construction is
isolated in one existence statement and every consequence below is choice-free.

**Indexing by `ZMod L`, not by `Finset.range L`.**  This is the whole reason the section is short.
With `ℕ` indices the translation step reads `C_i + t = C_{(i+1) mod L}` and every proof carries a
wrap-around case split at `i = L − 1`.  Over `ZMod L` the same step is `C_i + t = C_{i+1}` with no
case at all, because the wrap is the ring's own arithmetic.  The partition and covering statements
likewise become "the fibres of a map into a fintype", which is what they actually are. -/

/-- **A `t`-height**: an integer coordinate advancing by one along the `t`-orbit. -/
def IsHeight (t : G) (k : G → ℤ) : Prop := ∀ x, k (x + t) = k x + 1

/-- The `i`-th residue class of a height, modulo `L` — the source's `C_i`. -/
def heightClass (k : G → ℤ) (L : ℕ) (i : ZMod L) : Set G := {x | ((k x : ℤ) : ZMod L) = i}

theorem mem_heightClass_self (k : G → ℤ) (L : ℕ) (x : G) :
    x ∈ heightClass k L ((k x : ZMod L)) := rfl

/-- Distinct classes are disjoint: they are fibres of one map. -/
theorem heightClass_disjoint (k : G → ℤ) (L : ℕ) {i j : ZMod L} (h : i ≠ j) :
    Disjoint (heightClass k L i) (heightClass k L j) :=
  Set.disjoint_left.mpr fun _ hx hx' => h (hx.symm.trans hx')

/-- The classes cover `G`. -/
theorem heightClass_cover (k : G → ℤ) (L : ℕ) [NeZero L] :
    (⋃ i ∈ (Finset.univ : Finset (ZMod L)), heightClass k L i) = Set.univ := by
  ext x
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  exact Set.mem_iUnion₂.mpr ⟨(k x : ZMod L), Finset.mem_univ _, mem_heightClass_self k L x⟩

/-- **`C_i + t = C_{i+1}`** — no wrap-around case, because `ZMod L` does the wrapping. -/
theorem heightClass_translate {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (i : ZMod L) :
    (fun x => x + t) '' heightClass k L i = heightClass k L (i + 1) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show ((k (x + t) : ℤ) : ZMod L) = i + 1
    rw [hk x]
    push_cast
    rw [show ((k x : ℤ) : ZMod L) = i from hx]
  · intro hy
    have hxt : y - t + t = y := by abel
    refine ⟨y - t, ?_, hxt⟩
    have h := hk (y - t)
    rw [hxt] at h
    have hy' : ((k y : ℤ) : ZMod L) = i + 1 := hy
    rw [h] at hy'
    push_cast at hy'
    exact add_right_cancel hy'

/-- **Each of the `L` height classes carries exactly `1/L`** for any finitely additive probability
capped by `1/L` on each of them.

This is equation (7) of the source, and the cap is where the upper density enters: domination gives
`q(C_i) ≤ d̄(C_i) = 1/L`, and the total forces equality.  The forcing itself is
`eq_of_le_of_biUnion_univ`, which knows nothing about heights. -/
theorem q_heightClass_eq (q : FinAddProb G) (k : G → ℤ) (L : ℕ) [NeZero L]
    (hle : ∀ i : ZMod L, q.toFun (heightClass k L i) ≤ (L : ℝ)⁻¹) (i : ZMod L) :
    q.toFun (heightClass k L i) = (L : ℝ)⁻¹ := by
  have hcard : (Finset.univ : Finset (ZMod L)).card = L := by
    rw [Finset.card_univ, ZMod.card]
  have hne : (Finset.univ : Finset (ZMod L)).Nonempty := ⟨(0 : ZMod L), Finset.mem_univ _⟩
  have hle' : ∀ j ∈ (Finset.univ : Finset (ZMod L)),
      q.toFun (heightClass k L j) ≤ (((Finset.univ : Finset (ZMod L)).card : ℝ))⁻¹ := by
    intro j _
    rw [hcard]
    exact hle j
  have h := eq_of_le_of_biUnion_univ q (heightClass k L)
    (fun _ _ hab => heightClass_disjoint k L hab) Finset.univ
    (heightClass_cover k L) hne hle' i (Finset.mem_univ i)
  rwa [hcard] at h


/-! ### The one choice-dependent step, isolated

Everything above takes the height `k` as given.  A height exists exactly when `t` has infinite
order, and producing one is where the source's transversal lives: choose a representative of each
`t`-orbit, and let `k x` be `x`'s displacement from its own orbit's representative.

Isolating it here is the point.  `Quotient.out` supplies the transversal in one step, and the
infinite-order hypothesis is used for exactly one thing — that `m • t` determines `m`, so the
displacement is well defined.  Nothing downstream mentions choice again. -/

/-- The `t`-orbit equivalence: `y` sits on `x`'s orbit. -/
def orbitSetoid (t : G) : Setoid G where
  r x y := ∃ m : ℤ, y = x + m • t
  iseqv :=
    { refl := fun x => ⟨0, by simp⟩
      symm := fun {x y} h => by
        obtain ⟨m, hm⟩ := h
        exact ⟨-m, by rw [hm, neg_zsmul]; abel⟩
      trans := fun {x y z} h h' => by
        obtain ⟨m, hm⟩ := h
        obtain ⟨n, hn⟩ := h'
        exact ⟨m + n, by rw [hn, hm, add_zsmul]; abel⟩ }

/-- **A height exists whenever `t` has infinite order.**

`hinf` states infinite order in the form the proof actually consumes: only `m • t = 0 → m = 0` is
used, and only to know that the orbit displacement is unique. -/
theorem exists_isHeight (t : G) (hinf : ∀ m : ℤ, m • t = 0 → m = 0) :
    ∃ k : G → ℤ, IsHeight t k := by
  classical
  have hcancel : ∀ m n : ℤ, m • t = n • t → m = n := by
    intro m n h
    -- `sub_zsmul` produces `m • t + -(n • t)`, not `m • t - n • t`, so `sub_self` finds nothing.
    have hz : (m - n) • t = 0 := by rw [sub_zsmul, h]; abel
    have := hinf _ hz
    omega
  refine ⟨fun x => Classical.choose (Quotient.mk_out (s := orbitSetoid t) x), fun x => ?_⟩
  have hspec : ∀ y : G, y = (Quotient.mk (orbitSetoid t) y).out
      + (Classical.choose (Quotient.mk_out (s := orbitSetoid t) y)) • t :=
    fun y => Classical.choose_spec (Quotient.mk_out (s := orbitSetoid t) y)
  have hrel : (orbitSetoid t).r (x + t) x := ⟨-1, by rw [neg_one_zsmul]; abel⟩
  have hq : Quotient.mk (orbitSetoid t) (x + t) = Quotient.mk (orbitSetoid t) x :=
    Quotient.sound hrel
  -- `rw [hq] at h1` is NOT available: `h1` mentions `Classical.choose (Quotient.mk_out (x+t))`,
  -- whose TYPE contains the class being rewritten, so the motive is ill-typed.  Rewriting the
  -- plain equation `.out = .out` in a GOAL touches no dependent position.
  have hout : (Quotient.mk (orbitSetoid t) (x + t)).out
      = (Quotient.mk (orbitSetoid t) x).out := congrArg Quotient.out hq
  have h1 : x + t = (Quotient.mk (orbitSetoid t) x).out
      + (Classical.choose (Quotient.mk_out (s := orbitSetoid t) (x + t))) • t := by
    rw [← hout]
    exact hspec (x + t)
  have h2 : (Quotient.mk (orbitSetoid t) x).out
        + (Classical.choose (Quotient.mk_out (s := orbitSetoid t) x)) • t + t
      = (Quotient.mk (orbitSetoid t) x).out
        + (Classical.choose (Quotient.mk_out (s := orbitSetoid t) (x + t))) • t := by
    rw [← hspec x]
    exact h1
  rw [add_assoc] at h2
  have h3 := add_left_cancel h2
  have h4 : (Classical.choose (Quotient.mk_out (s := orbitSetoid t) x) + 1) • t
      = (Classical.choose (Quotient.mk_out (s := orbitSetoid t) (x + t))) • t := by
    rw [add_zsmul, one_zsmul]
    exact h3
  exact (hcancel _ _ h4).symm


/-! ### Step 3: the swap, and translation by an arbitrary integer

`heightClass_translate` moves by one `t`.  The swap needs to move by an arbitrary `m : ℤ`, and the
class it lands in is indexed by `(m : ZMod L)` — which is the second place the `ZMod` indexing pays
for itself, since `i • t` is not even *defined* for a residue `i`, while `m • t` for an integer `m`
lands in the class `i + (m : ZMod L)` with no side condition.

The swap itself splits in two.  `q_eq_of_swap` is pure `FinAddProb`: four sets, two of which
partition one class and two the other, with the two *crossed* unions capped by `c`.  It mentions no
group, no height, no shift — and it is the entire content of the source's "consequently both
inequalities are equalities … comparing gives `q(E+it) = q(E+jt)`".  The geometric statement is then
the instantiation, whose only work is checking that the shifted sets sit where they should. -/

/-- The height advances by `m` along `m • t`. -/
theorem isHeight_zsmul {t : G} {k : G → ℤ} (hk : IsHeight t k) (x : G) (m : ℤ) :
    k (x + m • t) = k x + m := by
  refine Int.induction_on m ?_ ?_ ?_
  · simp
  · intro n ih
    have h : x + ((n : ℤ) + 1) • t = (x + (n : ℤ) • t) + t := by
      rw [add_zsmul, one_zsmul]; abel
    rw [h, hk, ih]
    ring
  · intro n ih
    have h : x + (-(n : ℤ) - 1) • t + t = x + (-(n : ℤ)) • t := by
      rw [sub_zsmul, one_zsmul]; abel
    have h2 := hk (x + (-(n : ℤ) - 1) • t)
    rw [h, ih] at h2
    omega

/-- **Translation by `m • t` sends `C_i` to `C_{i+m}`.** -/
theorem heightClass_shift {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (i : ZMod L) (m : ℤ) :
    (fun x => x + m • t) '' heightClass k L i = heightClass k L (i + (m : ZMod L)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show ((k (x + m • t) : ℤ) : ZMod L) = i + (m : ZMod L)
    rw [isHeight_zsmul hk]
    push_cast
    rw [show ((k x : ℤ) : ZMod L) = i from hx]
  · intro hy
    refine ⟨y + (-m) • t, ?_, ?_⟩
    · show ((k (y + (-m) • t) : ℤ) : ZMod L) = i
      rw [isHeight_zsmul hk]
      push_cast
      rw [show ((k y : ℤ) : ZMod L) = i + (m : ZMod L) from hy]
      ring
    -- the goal is a beta-redex `(fun x => x + m • t) (y + -m • t) = y`, in which `rw` cannot see
    -- the `+` structure at all; `show` exposes it first.
    · show y + (-m) • t + m • t = y
      have hz : (-m) • t + m • t = 0 := by rw [← add_zsmul]; simp
      rw [add_assoc, hz, add_zero]

/-- **The swap, with the group stripped out.**

`X, W` partition one class and `Z, Y` the other; the two crossed unions `X ∪ Y` and `W ∪ Z` are the
selectors, each capped by `c`.  Their union is the two classes, whose total is `2c`, so both caps
are attained — and then `X ∪ Y` and `Z ∪ Y` both totalling `c` forces `q X = q Z`. -/
theorem q_eq_of_swap (q : FinAddProb G) {X Y Z W : Set G} {c : ℝ}
    (hXW : Disjoint X W) (hZY : Disjoint Z Y)
    (hcross : Disjoint (X ∪ W) (Z ∪ Y))
    (hCm : q.toFun (X ∪ W) = c) (hCn : q.toFun (Z ∪ Y) = c)
    (hS : q.toFun (X ∪ Y) ≤ c) (hS' : q.toFun (W ∪ Z) ≤ c) :
    q.toFun X = q.toFun Z := by
  have hXZ : Disjoint X Z :=
    Set.disjoint_of_subset Set.subset_union_left Set.subset_union_left hcross
  have hXY : Disjoint X Y :=
    Set.disjoint_of_subset Set.subset_union_left Set.subset_union_right hcross
  have hWZ : Disjoint W Z :=
    Set.disjoint_of_subset Set.subset_union_right Set.subset_union_left hcross
  have hWY : Disjoint W Y :=
    Set.disjoint_of_subset Set.subset_union_right Set.subset_union_right hcross
  have hdisj : Disjoint (X ∪ Y) (W ∪ Z) := by
    rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    exact ⟨⟨hXW, hXZ⟩, ⟨hWY.symm, hZY.symm⟩⟩
  have hset : (X ∪ Y) ∪ (W ∪ Z) = (X ∪ W) ∪ (Z ∪ Y) := by
    ext y
    simp only [Set.mem_union]
    tauto
  have h2c : q.toFun ((X ∪ Y) ∪ (W ∪ Z)) = 2 * c := by
    rw [hset, q.additive _ _ hcross, hCm, hCn]
    ring
  obtain ⟨hSc, -⟩ := eq_of_le_of_union q hS hS' hdisj h2c
  exact eq_of_partition_pair q hXY hSc hZY hCn

/-- **Equation (8)**: `E` and its translates.  For `E` inside the zero class, its `m`-shift and its
`n`-shift carry the same mass, given that the two crossed selectors are capped by `c` and the two
classes attain `c`. -/
theorem q_shift_eq_of_selector_le (q : FinAddProb G) {t : G} {k : G → ℤ} (hk : IsHeight t k)
    (L : ℕ) (E : Set G) (hE : E ⊆ heightClass k L 0) (m n : ℤ)
    (hmn : ((m : ZMod L)) ≠ ((n : ZMod L))) {c : ℝ}
    (hCm : q.toFun (heightClass k L (m : ZMod L)) = c)
    (hCn : q.toFun (heightClass k L (n : ZMod L)) = c)
    (hS : q.toFun ((fun x => x + m • t) '' E
        ∪ (fun x => x + n • t) '' (heightClass k L 0 \ E)) ≤ c)
    (hS' : q.toFun ((fun x => x + m • t) '' (heightClass k L 0 \ E)
        ∪ (fun x => x + n • t) '' E) ≤ c) :
    q.toFun ((fun x => x + m • t) '' E) = q.toFun ((fun x => x + n • t) '' E) := by
  have hdiff : Disjoint E (heightClass k L 0 \ E) :=
    Set.disjoint_left.mpr fun _ hx hx' => hx'.2 hx
  have hEC : E ∪ (heightClass k L 0 \ E) = heightClass k L 0 := by
    ext y
    constructor
    · rintro (hy | ⟨hy, -⟩)
      · exact hE hy
      · exact hy
    · intro hy
      by_cases hE' : y ∈ E
      · exact Or.inl hE'
      · exact Or.inr ⟨hy, hE'⟩
  have hm0 : (fun x : G => x + m • t) '' heightClass k L 0 = heightClass k L (m : ZMod L) := by
    have := heightClass_shift hk L 0 m
    rwa [zero_add] at this
  have hn0 : (fun x : G => x + n • t) '' heightClass k L 0 = heightClass k L (n : ZMod L) := by
    have := heightClass_shift hk L 0 n
    rwa [zero_add] at this
  have hUm : (fun x : G => x + m • t) '' E ∪ (fun x : G => x + m • t) '' (heightClass k L 0 \ E)
      = heightClass k L (m : ZMod L) := by
    rw [← Set.image_union, hEC, hm0]
  have hUn : (fun x : G => x + n • t) '' E ∪ (fun x : G => x + n • t) '' (heightClass k L 0 \ E)
      = heightClass k L (n : ZMod L) := by
    rw [← Set.image_union, hEC, hn0]
  refine q_eq_of_swap q (X := (fun x : G => x + m • t) '' E)
    (W := (fun x : G => x + m • t) '' (heightClass k L 0 \ E))
    (Z := (fun x : G => x + n • t) '' E)
    (Y := (fun x : G => x + n • t) '' (heightClass k L 0 \ E))
    (Set.disjoint_image_of_injective (add_left_injective _) hdiff)
    (Set.disjoint_image_of_injective (add_left_injective _) hdiff)
    ?_ ?_ ?_ hS hS'
  · rw [hUm, hUn]
    exact heightClass_disjoint k L hmn
  · rw [hUm]; exact hCm
  · rw [hUn]; exact hCn


/-! ### The upper-density axiom enters, and `d̄(C_i) = 1/L`

This is the source's equation (5), and the first place anything about *densities* is used rather
than about finitely additive measures.  Mathlib has no notion of a Révész–Ruzsa upper density, so
the axiom enters as a hypothesis on an abstract `d` — which is the honest encoding, and also the
useful one: the theorem below says exactly what property of `d̄` the block argument consumes.

Only **restricted additivity** is needed here.  Perturbation invariance, the other axiom, is what
the *selector* half needs, and is separate.

The source states restricted additivity for arbitrary translations `A + t_1, …, A + t_m`; the block
argument only ever uses multiples of a single `t`, so that is the form declared. -/

/-- **Restricted additivity along `t`**: disjoint translates of one set add. -/
def RestrictedAdditiveAlong (d : Set G → ℝ) (t : G) : Prop :=
  ∀ (s : Finset ℤ) (A : Set G),
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint ((fun x => x + i • t) '' A) ((fun x => x + j • t) '' A)) →
    d (⋃ i ∈ s, (fun x => x + i • t) '' A) = s.card * d A

/-- Distinct integers in `[0, L)` stay distinct in `ZMod L`. -/
theorem intCast_ne_intCast_of_mem_Ico {L : ℕ} {i j : ℤ}
    (hi : i ∈ Finset.Ico (0 : ℤ) (L : ℤ)) (hj : j ∈ Finset.Ico (0 : ℤ) (L : ℤ)) (hij : i ≠ j) :
    ((i : ZMod L)) ≠ ((j : ZMod L)) := by
  simp only [Finset.mem_Ico] at hi hj
  intro h
  have hdvd : ((L : ℤ)) ∣ (i - j) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h]
    ring
  have habs : |i - j| < (L : ℤ) := by
    rw [abs_lt]
    omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  exact hij (by omega)

/-- The `L` translates of `C_0` by `0, t, …, (L−1)t` cover `G`. -/
theorem heightClass_zero_translate_cover {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ)
    (hL : 0 < L) :
    (⋃ i ∈ Finset.Ico (0 : ℤ) (L : ℤ), (fun x => x + i • t) '' heightClass k L 0) = Set.univ := by
  ext x
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  have hLz : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  have hr0 : 0 ≤ k x % (L : ℤ) := Int.emod_nonneg _ (ne_of_gt hLz)
  have hrL : k x % (L : ℤ) < (L : ℤ) := Int.emod_lt_of_pos _ hLz
  have hdm := Int.ediv_add_emod (k x) ((L : ℤ))
  refine Set.mem_iUnion₂.mpr ⟨k x % (L : ℤ), Finset.mem_Ico.mpr ⟨hr0, hrL⟩,
    ⟨x + (-(k x % (L : ℤ))) • t, ?_, ?_⟩⟩
  · show ((k (x + (-(k x % (L : ℤ))) • t) : ℤ) : ZMod L) = 0
    rw [isHeight_zsmul hk, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨k x / (L : ℤ), by linarith⟩
  · show x + (-(k x % (L : ℤ))) • t + (k x % (L : ℤ)) • t = x
    have hz : (-(k x % (L : ℤ))) • t + (k x % (L : ℤ)) • t = 0 := by rw [← add_zsmul]; simp
    rw [add_assoc, hz, add_zero]

/-- **Equation (5): every height class has upper density exactly `1/L`.**

Restricted additivity applied to the `L` translates of `C_0`, whose union is `G`, gives
`1 = L · d̄(C_0)`; the same axiom with a single translation gives `d̄(C_i) = d̄(C_0)`. -/
theorem d_heightClass_eq {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (hL : 0 < L)
    (d : Set G → ℝ) (hadd : RestrictedAdditiveAlong d t) (hone : d Set.univ = 1) (i : ZMod L) :
    d (heightClass k L i) = (L : ℝ)⁻¹ := by
  haveI : NeZero L := ⟨by omega⟩
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hshift : ∀ m : ℤ, (fun x : G => x + m • t) '' heightClass k L 0
      = heightClass k L (m : ZMod L) := by
    intro m
    have := heightClass_shift hk L 0 m
    rwa [zero_add] at this
  -- the `L` translates are pairwise disjoint
  have hdisj : ∀ a ∈ Finset.Ico (0 : ℤ) (L : ℤ), ∀ b ∈ Finset.Ico (0 : ℤ) (L : ℤ), a ≠ b →
      Disjoint ((fun x : G => x + a • t) '' heightClass k L 0)
        ((fun x : G => x + b • t) '' heightClass k L 0) := by
    intro a ha b hb hab
    rw [hshift a, hshift b]
    exact heightClass_disjoint k L (intCast_ne_intCast_of_mem_Ico ha hb hab)
  have hcard : (Finset.Ico (0 : ℤ) (L : ℤ)).card = L := by
    rw [Int.card_Ico]
    simp
  -- `1 = L · d̄(C₀)`
  have hsum := hadd (Finset.Ico (0 : ℤ) (L : ℤ)) (heightClass k L 0) hdisj
  rw [heightClass_zero_translate_cover hk L hL, hone, hcard] at hsum
  -- `d̄(C_i) = d̄(C₀)`, by the same axiom with one translation
  have hone' : d (heightClass k L i) = d (heightClass k L 0) := by
    have h1 := hadd {(i.val : ℤ)} (heightClass k L 0) (by
      intro a ha b hb hab
      simp only [Finset.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab)
    have hval : (((i.val : ℤ)) : ZMod L) = i := by
      push_cast
      exact ZMod.natCast_rightInverse i
    -- `Set.biUnion_singleton` does NOT fire here: the index is a FINSET singleton, and the
    -- matching lemma is `Finset.set_biUnion_singleton`.
    simp only [Finset.set_biUnion_singleton, Finset.card_singleton] at h1
    rw [hshift, hval] at h1
    rw [h1]
    push_cast
    ring
  rw [hone']
  field_simp at hsum ⊢
  linarith


/-! ### The selector half: `d̄(S) = 1/L`

The source says every selector is a perturbation of `C₀` — "move its selected point in a block to
that block's zeroth point" — with displacements among `0, −t, …, −(L−1)t`.  Written out, the map is

  `φ x = x + (−(k x mod L)) • t`,

and the three obligations of `Set.BijOn` split cleanly along the definition of a selector:

* **MapsTo** uses nothing about `S` at all — `k(φ x) = L·(k x / L)` is divisible by `L` for *every*
  `x`, so `φ` lands in `C₀` unconditionally.
* **InjOn** is the *uniqueness* half of "exactly one point per block".
* **SurjOn** is the *existence* half.

So the `∃!` in `IsSelector` is not one hypothesis used twice; its two halves discharge two different
obligations, and neither is needed for the third.  `blockZero_eq` is the one computation both share:
a point `c` of `C₀` is its own block's zero point, so anything `m` steps above it, `0 ≤ m < L`, maps
back to `c`. -/

/-- The zero point of `x`'s block: step back by `k x mod L`. -/
def blockZero (t : G) (k : G → ℤ) (L : ℕ) (x : G) : G := x + (-(k x % (L : ℤ))) • t

/-- Stepping back and forward again returns `x`. -/
theorem blockZero_add (t : G) (k : G → ℤ) (L : ℕ) (x : G) :
    blockZero t k L x + (k x % (L : ℤ)) • t = x := by
  unfold blockZero
  have hz : (-(k x % (L : ℤ))) • t + (k x % (L : ℤ)) • t = 0 := by rw [← add_zsmul]; simp
  rw [add_assoc, hz, add_zero]

/-- `φ` lands in `C₀` for every `x`, selector or not. -/
theorem blockZero_mem {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (hL : 0 < L) (x : G) :
    blockZero t k L x ∈ heightClass k L 0 := by
  have hLz : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  have hdm := Int.ediv_add_emod (k x) ((L : ℤ))
  show ((k (blockZero t k L x) : ℤ) : ZMod L) = 0
  unfold blockZero
  rw [isHeight_zsmul hk, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨k x / (L : ℤ), by linarith⟩

/-- **A point of `C₀` is its own block's zero point**, so anything `m` steps above it with
`0 ≤ m < L` maps back to it.  Both `InjOn` and `SurjOn` run on this. -/
theorem blockZero_eq {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ)
    {c x : G} (hc : c ∈ heightClass k L 0) {m : ℤ}
    (hm0 : 0 ≤ m) (hmL : m < (L : ℤ)) (hx : x = c + m • t) :
    blockZero t k L x = c := by
  obtain ⟨q, hq⟩ : ((L : ℤ)) ∣ k c := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hc
  have hkx : k x = (L : ℤ) * q + m := by
    rw [hx, isHeight_zsmul hk, hq]
  have hmod : k x % (L : ℤ) = m := by
    rw [hkx, add_comm ((L : ℤ) * q) m, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt hm0 hmL
  unfold blockZero
  rw [hmod, hx, add_assoc]
  have hz : m • t + (-m) • t = 0 := by rw [← add_zsmul]; simp
  rw [hz, add_zero]

/-- **A selector**: exactly one point from each `L`-block. -/
def IsSelector (t : G) (k : G → ℤ) (L : ℕ) (S : Set G) : Prop :=
  ∀ c ∈ heightClass k L 0, ∃! x : G, x ∈ S ∧ ∃ m : ℤ, 0 ≤ m ∧ m < (L : ℤ) ∧ x = c + m • t

/-- **Perturbation invariance** — the Révész–Ruzsa axiom (3): a bijection with displacements in one
finite set preserves the upper density. -/
def PerturbationInvariant (d : Set G → ℝ) : Prop :=
  ∀ (A B : Set G) (T : Finset G) (f : G → G),
    Set.BijOn f A B → (∀ x ∈ A, f x - x ∈ T) → d B = d A

/-- **`φ` is a bijection from any selector onto `C₀`.** -/
theorem bijOn_blockZero {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (hL : 0 < L)
    {S : Set G} (hS : IsSelector t k L S) :
    Set.BijOn (blockZero t k L) S (heightClass k L 0) := by
  have hLz : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  refine ⟨fun x _ => blockZero_mem hk L hL x, ?_, ?_⟩
  · intro x hx y hy hxy
    -- `∃! x, p x` is `∃ x, p x ∧ ∀ y, p y → y = x`: THREE components, not two.  Binding two puts
    -- the conjunction in the second and loses the uniqueness clause entirely.
    obtain ⟨z, -, huniq⟩ := hS _ (blockZero_mem hk L hL x)
    have hxw : x ∈ S ∧ ∃ m : ℤ, 0 ≤ m ∧ m < (L : ℤ) ∧ x = blockZero t k L x + m • t :=
      ⟨hx, k x % (L : ℤ), Int.emod_nonneg _ (ne_of_gt hLz), Int.emod_lt_of_pos _ hLz,
        (blockZero_add t k L x).symm⟩
    have hyw : y ∈ S ∧ ∃ m : ℤ, 0 ≤ m ∧ m < (L : ℤ) ∧ y = blockZero t k L x + m • t :=
      ⟨hy, k y % (L : ℤ), Int.emod_nonneg _ (ne_of_gt hLz), Int.emod_lt_of_pos _ hLz, by
        rw [hxy]; exact (blockZero_add t k L y).symm⟩
    rw [huniq x hxw, huniq y hyw]
  · intro c hc
    obtain ⟨x, ⟨hxS, m, hm0, hmL, hxm⟩, -⟩ := hS c hc
    exact ⟨x, hxS, blockZero_eq hk L hc hm0 hmL hxm⟩

/-- **Equation (6): every selector has upper density `1/L`.** -/
theorem d_selector_eq {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (hL : 0 < L)
    (d : Set G → ℝ) (hpert : PerturbationInvariant d) (hadd : RestrictedAdditiveAlong d t)
    (hone : d Set.univ = 1) {S : Set G} (hS : IsSelector t k L S) :
    d S = (L : ℝ)⁻¹ := by
  -- `Finset.image` needs `DecidableEq G`, which a bare `AddCommGroup` does not supply.
  classical
  have hLz : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  -- the displacements lie in one finite set, which is the axiom's hypothesis
  have hdisp : ∀ x ∈ S, blockZero t k L x - x
      ∈ (Finset.Ico (0 : ℤ) (L : ℤ)).image (fun m : ℤ => (-m) • t) := by
    intro x _
    refine Finset.mem_image.mpr ⟨k x % (L : ℤ), Finset.mem_Ico.mpr
      ⟨Int.emod_nonneg _ (ne_of_gt hLz), Int.emod_lt_of_pos _ hLz⟩, ?_⟩
    unfold blockZero
    abel
  have h := hpert S (heightClass k L 0)
    ((Finset.Ico (0 : ℤ) (L : ℤ)).image (fun m : ℤ => (-m) • t)) (blockZero t k L)
    (bijOn_blockZero hk L hL hS) hdisp
  rw [d_heightClass_eq hk L hL d hadd hone 0] at h
  exact h.symm


/-! ### Equation (9): the telescoping, and where the boundary term comes from

`q(B+t) − q(B)` splits over the `L` classes.  Translation permutes the classes cyclically
(`C_j + t = C_{j+1}`), so after reindexing by `j ↦ j − 1` the two sums run over the same index set
and the difference is a single sum of differences.  The swap kills every term whose class is not the
boundary one, and what survives is one term.

**The boundary is real, and the `ZMod` indexing does not hide it.**  `C_{L−1} + t = C₀` holds as
sets — the classes really are permuted cyclically — but the *swap* is only available when both
shifts stay inside one block, `0 ≤ m, n < L`.  For the class whose points sit at offset `L−1`, the
shift by `t` leaves the block, and `q_shift_eq_of_selector_le` has no selector to offer.  That one
class is `j₀` below; the conclusion is stated as an exact identity for it, and the bound `1/L`
follows because both surviving terms lie in `[0, 1/L]`. -/

/-- `q B` splits over the `L` height classes. -/
theorem q_eq_sum_inter_heightClass (q : FinAddProb G) (k : G → ℤ) (L : ℕ) [NeZero L] (B : Set G) :
    q.toFun B = ∑ j : ZMod L, q.toFun (B ∩ heightClass k L j) := by
  classical
  have hd : Pairwise fun i j : ZMod L =>
      Disjoint (B ∩ heightClass k L i) (B ∩ heightClass k L j) := fun i j hij =>
    Disjoint.mono Set.inter_subset_right Set.inter_subset_right (heightClass_disjoint k L hij)
  have hcov : (⋃ j ∈ (Finset.univ : Finset (ZMod L)), B ∩ heightClass k L j) = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.mp hx
      exact hj.1
    · intro hx
      exact Set.mem_iUnion₂.mpr
        ⟨(k x : ZMod L), Finset.mem_univ _, hx, mem_heightClass_self k L x⟩
  have h := q.sum_biUnion (fun j => B ∩ heightClass k L j) hd Finset.univ
  rwa [hcov] at h

/-- Translation permutes the classes: the part of `B + t` in `C_j` is the shift of the part of `B`
in `C_{j−1}`. -/
theorem shift_inter_heightClass {t : G} {k : G → ℤ} (hk : IsHeight t k) (L : ℕ) (B : Set G)
    (j : ZMod L) :
    ((fun x => x + t) '' B) ∩ heightClass k L j
      = (fun x => x + t) '' (B ∩ heightClass k L (j - 1)) := by
  ext y
  constructor
  · rintro ⟨⟨b, hb, rfl⟩, hcls⟩
    refine ⟨b, ⟨hb, ?_⟩, rfl⟩
    show ((k b : ℤ) : ZMod L) = j - 1
    have hj : ((k (b + t) : ℤ) : ZMod L) = j := hcls
    rw [hk b] at hj
    push_cast at hj
    -- `linear_combination` is NOT in this module's import closure (it is in Problem333521's only
    -- because that file pulls half of Analysis); the explicit lemma needs no tactic at all.
    exact eq_sub_of_add_eq hj
  · rintro ⟨b, ⟨hb, hcls⟩, rfl⟩
    refine ⟨⟨b, hb, rfl⟩, ?_⟩
    show ((k (b + t) : ℤ) : ZMod L) = j
    rw [hk b]
    push_cast
    rw [show ((k b : ℤ) : ZMod L) = j - 1 from hcls]
    ring

/-- **Equation (9), as an exact identity**: all but the boundary class cancel. -/
theorem q_shift_sub_eq_boundary (q : FinAddProb G) {t : G} {k : G → ℤ} (hk : IsHeight t k)
    (L : ℕ) [NeZero L] (B : Set G) (j₀ : ZMod L)
    (hinv : ∀ j : ZMod L, j ≠ j₀ →
      q.toFun ((fun x => x + t) '' (B ∩ heightClass k L j)) = q.toFun (B ∩ heightClass k L j)) :
    q.toFun ((fun x => x + t) '' B) - q.toFun B
      = q.toFun ((fun x => x + t) '' (B ∩ heightClass k L j₀))
        - q.toFun (B ∩ heightClass k L j₀) := by
  classical
  have h1 : q.toFun ((fun x => x + t) '' B)
      = ∑ j : ZMod L, q.toFun ((fun x => x + t) '' (B ∩ heightClass k L j)) := by
    rw [q_eq_sum_inter_heightClass q k L ((fun x => x + t) '' B)]
    have hstep : ∀ j : ZMod L,
        q.toFun (((fun x => x + t) '' B) ∩ heightClass k L j)
          = q.toFun ((fun x => x + t) '' (B ∩ heightClass k L (j - 1))) := by
      intro j
      rw [shift_inter_heightClass hk L B j]
    rw [Finset.sum_congr rfl fun j _ => hstep j]
    exact Fintype.sum_equiv (Equiv.subRight (1 : ZMod L)) _ _ fun _ => rfl
  rw [h1, q_eq_sum_inter_heightClass q k L B, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_single j₀ (fun j _ hj => by rw [hinv j hj, sub_self])
    (fun h => absurd (Finset.mem_univ j₀) h)

/-- **The `1/L` bound.**  Both surviving terms lie in `[0, 1/L]`, so their difference is at most
`1/L` in absolute value — and `L` is arbitrary, which is what makes `q` translation invariant. -/
theorem abs_q_shift_sub_le (q : FinAddProb G) {t : G} {k : G → ℤ} (hk : IsHeight t k)
    (L : ℕ) [NeZero L] (B : Set G) (j₀ : ZMod L)
    (hcap : ∀ i : ZMod L, q.toFun (heightClass k L i) ≤ (L : ℝ)⁻¹)
    (hinv : ∀ j : ZMod L, j ≠ j₀ →
      q.toFun ((fun x => x + t) '' (B ∩ heightClass k L j)) = q.toFun (B ∩ heightClass k L j)) :
    |q.toFun ((fun x => x + t) '' B) - q.toFun B| ≤ (L : ℝ)⁻¹ := by
  rw [q_shift_sub_eq_boundary q hk L B j₀ hinv]
  have h1 : q.toFun (B ∩ heightClass k L j₀) ≤ (L : ℝ)⁻¹ :=
    le_trans (q.mono Set.inter_subset_right) (hcap j₀)
  have h2 : q.toFun ((fun x => x + t) '' (B ∩ heightClass k L j₀)) ≤ (L : ℝ)⁻¹ := by
    refine le_trans (q.mono ?_) (hcap (j₀ + 1))
    rintro y ⟨b, ⟨-, hb⟩, rfl⟩
    show ((k (b + t) : ℤ) : ZMod L) = j₀ + 1
    rw [hk b]
    push_cast
    rw [show ((k b : ℤ) : ZMod L) = j₀ from hb]
  rw [abs_le]
  exact ⟨by linarith [q.nonneg ((fun x => x + t) '' (B ∩ heightClass k L j₀))],
    by linarith [q.nonneg (B ∩ heightClass k L j₀)]⟩


end Height
end Principia.MathDB.P371629
