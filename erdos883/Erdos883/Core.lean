/-
DEVELOPMENT — Erdős Problem #883: both sharpness theorems, axiom-free.

Proof routes:
- `erdos883_threshold_sharp`: A₀ = multiples of 2 or 3 in [1,n]. |A₀| = T n by
  inclusion–exclusion. Parity (evenness) is a proper 2-coloring of G(A₀): two evens
  share the factor 2, two odd members of A₀ share the factor 3. A closed walk in a
  properly-2-colored graph has even length, so G(A₀) has no odd cycle.
- `erdos883_ceiling_sharp`: A₁ = evens in [1,n] ∪ {1, 3, …, 2⋅q n + 1}. |A₁| = T n + 1.
  Attainment: 1 – 2 – ⋯ – (2t+1) – 1 is an explicit cycle (consecutive integers are
  coprime; 1 is coprime to everything). Ceiling: the evens form an independent set in
  G(A₁); rotating a cycle to start at an odd vertex and scanning its support list, at
  most ⌊L/2⌋ of the L distinct cycle vertices are even, so a (2t+1)-cycle has ≥ t+1
  distinct odd vertices — but A₁ has only q n + 1 odd members, forcing t ≤ q n.

`#print axioms` for both headline theorems: [propext, Classical.choice, Quot.sound].
-/
import Erdos883.Statement
set_option autoImplicit false

namespace Erdos883

open Finset SimpleGraph
open Erdos883.Statement

/-! ### Generic list lemmas -/

/-- `(a :: b :: t).getLast? = (b :: t).getLast?`. -/
lemma getLast?_cons_cons' {α : Type*} (a b : α) (t : List α) :
    (a :: b :: t).getLast? = (b :: t).getLast? := by
  simp [List.getLast?_cons]

/-- In a list with no two consecutive `P`-elements whose first and last elements are
not `P`, at most `(length − 1)/2` elements are `P`. -/
lemma countP_le_of_isChain (P : ℕ → Bool) :
    ∀ (N : ℕ) (l : List ℕ), l.length ≤ N →
      List.IsChain (fun a b => ¬(P a = true ∧ P b = true)) l →
      (∀ a, l.head? = some a → ¬ P a = true) →
      (∀ a, l.getLast? = some a → ¬ P a = true) →
      l.countP P ≤ (l.length - 1) / 2 := by
  intro N
  induction N with
  | zero =>
    intro l hlen _ _ _
    have hl : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst hl; simp
  | succ N ih =>
    intro l hlen hchain hhead hlast
    match l with
    | [] => simp
    | [a] =>
      have ha : ¬ P a = true := hhead a rfl
      simp [ha]
    | a :: b :: t =>
      have ha : ¬ P a = true := hhead a rfl
      obtain ⟨hab, hchain'⟩ := List.isChain_cons_cons.mp hchain
      have hlast' : ∀ x, (b :: t).getLast? = some x → ¬ P x = true := by
        intro x hx
        apply hlast
        rw [getLast?_cons_cons']
        exact hx
      by_cases hb : P b = true
      · match t with
        | [] => exact absurd hb (hlast' b rfl)
        | c :: t' =>
          obtain ⟨hbc, hchain''⟩ := List.isChain_cons_cons.mp hchain'
          have hc : ¬ P c = true := fun h => hbc ⟨hb, h⟩
          have hrec : (c :: t').countP P ≤ ((c :: t').length - 1) / 2 := by
            apply ih (c :: t')
            · simp only [List.length_cons] at hlen ⊢; omega
            · exact hchain''
            · intro x hx
              rw [List.head?_cons] at hx
              cases hx; exact hc
            · intro x hx
              apply hlast
              rw [getLast?_cons_cons', getLast?_cons_cons']
              exact hx
          rw [List.countP_cons_of_neg ha, List.countP_cons_of_pos hb]
          simp only [List.length_cons] at hrec ⊢
          omega
      · have hrec : (b :: t).countP P ≤ ((b :: t).length - 1) / 2 := by
          apply ih (b :: t)
          · simp only [List.length_cons] at hlen ⊢; omega
          · exact hchain'
          · intro x hx
            rw [List.head?_cons] at hx
            cases hx; exact hb
          · exact hlast'
        rw [List.countP_cons_of_neg ha]
        simp only [List.length_cons] at hrec ⊢
        omega

/-- Splitting a count by a Boolean predicate and its negation. -/
lemma countP_add_countP_bnot (p : ℕ → Bool) :
    ∀ l : List ℕ, l.countP p + l.countP (fun m => !(p m)) = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a = true <;>
      simp [h, List.length_cons, ← ih] <;> omega

/-! ### Generic walk lemmas -/

/-- If `f` is a proper 2-coloring, a walk's length is even iff its endpoints have
equal colors. -/
lemma walk_length_even_iff {V : Type*} {G : SimpleGraph V} (f : V → Bool)
    (hf : ∀ x y, G.Adj x y → f x ≠ f y) {u v : V} (w : G.Walk u v) :
    Even w.length ↔ f u = f v := by
  induction w with
  | nil => simp
  | cons h p ih =>
    rename_i a b c
    have hab : f a ≠ f b := hf a b h
    rw [Walk.length_cons, Nat.even_add_one, ih]
    cases hfa : f a <;> cases hfb : f b <;> cases hfc : f c <;> simp_all

/-- The support of a walk ends at its endpoint. -/
lemma support_getLast? {V : Type*} {G : SimpleGraph V} {u v : V} (w : G.Walk u v) :
    w.support.getLast? = some v := by
  rw [List.getLast?_eq_head?_reverse, ← Walk.support_reverse,
    ← Walk.cons_tail_support, List.head?_cons]

/-- In a cycle, an "independent" predicate `S` (no edge joins two `S`-vertices)
holds on at most `length / 2` of the distinct cycle vertices. -/
lemma cycle_countP_le {G : SimpleGraph ℕ} (S : ℕ → Bool)
    (hS : ∀ x y, G.Adj x y → ¬(S x = true ∧ S y = true))
    {u : ℕ} (w : G.Walk u u) (hc : w.IsCycle) :
    w.support.tail.countP S ≤ w.length / 2 := by
  have hnil : ¬ w.Nil := hc.not_nil
  obtain ⟨v, hv, hSv⟩ : ∃ v, v ∈ w.support ∧ ¬ S v = true := by
    by_cases hSu : S u = true
    · refine ⟨w.snd, List.mem_of_mem_tail (Walk.snd_mem_tail_support hnil), ?_⟩
      intro hSsnd
      exact hS u w.snd (Walk.adj_snd hnil) ⟨hSu, hSsnd⟩
    · exact ⟨u, Walk.start_mem_support w, hSu⟩
  have hlen : (w.rotate v hv).length = w.length := Walk.length_rotate w v hv
  have hrot : (w.rotate v hv).support.tail ~r w.support.tail := Walk.support_rotate w v hv
  have hcount : (w.rotate v hv).support.tail.countP S = w.support.tail.countP S :=
    hrot.perm.countP_eq _
  have hchain : List.IsChain (fun a b => ¬(S a = true ∧ S b = true))
      (w.rotate v hv).support :=
    (Walk.isChain_adj_support _).imp (fun a b hab => hS a b hab)
  have hhead : ∀ a, (w.rotate v hv).support.head? = some a → ¬ S a = true := by
    intro a ha
    rw [← Walk.cons_tail_support, List.head?_cons] at ha
    cases ha
    exact hSv
  have hlast : ∀ a, (w.rotate v hv).support.getLast? = some a → ¬ S a = true := by
    intro a ha
    rw [support_getLast?] at ha
    cases ha
    exact hSv
  have hlist := countP_le_of_isChain S (w.rotate v hv).support.length
    (w.rotate v hv).support le_rfl hchain hhead hlast
  have hsupp : (w.rotate v hv).support = v :: (w.rotate v hv).support.tail :=
    (Walk.cons_tail_support _).symm
  rw [hsupp, List.countP_cons_of_neg hSv, List.length_cons] at hlist
  have hslen : (w.rotate v hv).support.tail.length = w.length := by
    have h1 : (w.rotate v hv).support.length = (w.rotate v hv).length + 1 :=
      Walk.length_support _
    rw [hsupp, List.length_cons] at h1
    omega
  rw [← hcount]
  omega

/-- Build a walk from an `IsChain` of adjacencies. -/
def chainWalk {V : Type*} {G : SimpleGraph V} :
    ∀ (a : V) (l : List V) (b : V), List.IsChain G.Adj (a :: (l ++ [b])) → G.Walk a b
  | _, [], _, h => Walk.cons (List.isChain_cons_cons.mp h).1 Walk.nil
  | _, c :: l, b, h =>
      Walk.cons (List.isChain_cons_cons.mp h).1
        (chainWalk c l b (List.isChain_cons_cons.mp h).2)

lemma chainWalk_support {V : Type*} {G : SimpleGraph V} :
    ∀ (a : V) (l : List V) (b : V) (h : List.IsChain G.Adj (a :: (l ++ [b]))),
      (chainWalk a l b h).support = a :: (l ++ [b])
  | _, [], _, _ => by simp [chainWalk]
  | a, c :: l, b, h => by
      simp [chainWalk, chainWalk_support c l b (List.isChain_cons_cons.mp h).2]

lemma chainWalk_length {V : Type*} {G : SimpleGraph V} :
    ∀ (a : V) (l : List V) (b : V) (h : List.IsChain G.Adj (a :: (l ++ [b]))),
      (chainWalk a l b h).length = l.length + 1
  | _, [], _, _ => by simp [chainWalk]
  | a, c :: l, b, h => by
      simp [chainWalk, chainWalk_length c l b (List.isChain_cons_cons.mp h).2]

/-- Every edge of `chainWalk` joins a consecutive pair of the underlying list. -/
lemma chainWalk_edges_mem {V : Type*} {G : SimpleGraph V} :
    ∀ (a : V) (l : List V) (b : V) (h : List.IsChain G.Adj (a :: (l ++ [b])))
      (e : Sym2 V), e ∈ (chainWalk a l b h).edges →
      ∃ p ∈ (a :: (l ++ [b])).zip (l ++ [b]), e = s(p.1, p.2)
  | a, [], b, h, e, he => by
      simp only [chainWalk, Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at he
      exact ⟨(a, b), by simp, by simp [he]⟩
  | a, c :: l, b, h, e, he => by
      simp only [chainWalk, Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · exact ⟨(a, c), by simp, by simp [he]⟩
      · obtain ⟨p, hp, hpe⟩ :=
          chainWalk_edges_mem c l b (List.isChain_cons_cons.mp h).2 e he
        refine ⟨p, ?_, hpe⟩
        simp only [List.cons_append, List.zip_cons_cons, List.mem_cons] at hp ⊢
        tauto

/-- Pairs in the zip of two staggered `range'`s are consecutive pairs. -/
lemma zip_range'_consec :
    ∀ (m k : ℕ) (p : ℕ × ℕ),
      p ∈ (List.range' m (k + 1)).zip (List.range' (m + 1) k) →
      ∃ j, m ≤ j ∧ j < m + k ∧ p = (j, j + 1) := by
  intro m k
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    intro p hp
    rw [List.range'_succ, show List.range' (m + 1) (k + 1)
        = (m + 1) :: List.range' (m + 2) k from List.range'_succ,
      List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨m, le_rfl, by omega, rfl⟩
    · obtain ⟨j, hj1, hj2, hpj⟩ := ih (m + 1) p (by
        rw [List.range'_succ]
        exact hp)
      exact ⟨j, by omega, by omega, hpj⟩

/-! ### The coprime graph -/

/-- Consecutive integers are coprime. -/
lemma coprime_succ (m : ℕ) : Nat.Coprime m (m + 1) :=
  Nat.coprime_self_add_right.mpr (Nat.coprime_one_right m)

/-- Consecutive-integer chains lie in the coprime graph. -/
lemma chain_consec (A : Finset ℕ) :
    ∀ (m k : ℕ), 1 ≤ m → (∀ j, m ≤ j → j ≤ m + k → j ∈ A) →
    List.IsChain (coprimeGraph A).Adj (m :: List.range' (m + 1) k)
  | m, 0, _, _ => by simp
  | m, k + 1, hm, hmem => by
    rw [List.range'_succ]
    refine List.IsChain.cons_cons ?_ ?_
    · exact ⟨by omega, hmem m le_rfl (by omega), hmem (m + 1) (by omega) (by omega),
        coprime_succ m⟩
    · exact chain_consec A (m + 1) k (by omega)
        (fun j hj hj' => hmem j (by omega) (by omega))

/-- Every support vertex of a non-nil walk has an incident edge. -/
lemma exists_adj_of_mem_support {V : Type*} {G : SimpleGraph V} :
    ∀ {a b : V} (w : G.Walk a b), ¬ w.Nil → ∀ v ∈ w.support, ∃ z, G.Adj v z := by
  intro a b w
  induction w with
  | nil => intro hnil; simp at hnil
  | cons h p ih =>
    rename_i x y z'
    intro _ v hv
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨y, h⟩
    · by_cases hp : p.Nil
      · cases p with
        | nil =>
          simp only [Walk.support_nil, List.mem_singleton] at hv
          subst hv
          exact ⟨x, h.symm⟩
        | cons h' p' => simp at hp
      · exact ih hp v hv

/-- On a cycle, every support vertex lies in `A`. -/
lemma support_subset_of_cycle {A : Finset ℕ} {u : ℕ}
    (w : (coprimeGraph A).Walk u u) (hc : w.IsCycle) :
    ∀ v ∈ w.support, v ∈ A := by
  intro v hv
  obtain ⟨z, hz⟩ := exists_adj_of_mem_support w hc.not_nil v hv
  exact hz.2.1

/-- For `1 ≤ t`, if `{1, …, 2t+1} ⊆ A`, then `G(A)` has a cycle of length `2t+1`:
the cycle `1 – 2 – ⋯ – (2t+1) – 1`. -/
theorem cycle_of_consec (A : Finset ℕ) (t : ℕ) (ht : 1 ≤ t)
    (hmem : ∀ j, 1 ≤ j → j ≤ 2 * t + 1 → j ∈ A) :
    HasCycleLength (coprimeGraph A) (2 * t + 1) := by
  have hchain : List.IsChain (coprimeGraph A).Adj (1 :: List.range' 2 (2 * t)) :=
    chain_consec A 1 (2 * t) le_rfl (fun j hj hj' => hmem j hj (by omega))
  have hsplit : List.range' 2 (2 * t) = List.range' 2 (2 * t - 1) ++ [2 * t + 1] := by
    have h1 : 2 * t = (2 * t - 1) + 1 := by omega
    rw [h1, List.range'_concat]
    have h2 : 2 + 1 * (2 * t - 1) = 2 * t + 1 := by omega
    have h3 : 2 * t - 1 + 1 - 1 = 2 * t - 1 := by omega
    have h4 : 2 * t - 1 + 1 + 1 = 2 * t + 1 := by omega
    rw [h2, h3, h4]
  rw [hsplit] at hchain
  have hasc_supp : (chainWalk 1 (List.range' 2 (2 * t - 1)) (2 * t + 1) hchain).support
      = List.range' 1 (2 * t + 1) := by
    rw [chainWalk_support, ← hsplit,
      show List.range' 1 (2 * t + 1) = 1 :: List.range' 2 (2 * t) from List.range'_succ]
  have hasc_path : (chainWalk 1 (List.range' 2 (2 * t - 1)) (2 * t + 1) hchain).IsPath := by
    rw [Walk.isPath_def, hasc_supp]
    exact List.nodup_range'
  have hadj : (coprimeGraph A).Adj 1 (2 * t + 1) := by
    refine ⟨by omega, hmem 1 le_rfl (by omega), hmem (2 * t + 1) (by omega) le_rfl, ?_⟩
    simp [Nat.Coprime]
  have hnotmem : s(1, 2 * t + 1)
      ∉ (chainWalk 1 (List.range' 2 (2 * t - 1)) (2 * t + 1) hchain).reverse.edges := by
    rw [Walk.edges_reverse, List.mem_reverse]
    intro hmem_e
    obtain ⟨p, hp, hpe⟩ := chainWalk_edges_mem _ _ _ hchain _ hmem_e
    rw [← hsplit] at hp
    have hp' : p ∈ (List.range' 1 (2 * t + 1)).zip (List.range' 2 (2 * t)) := by
      rw [show List.range' 1 (2 * t + 1) = 1 :: List.range' 2 (2 * t) from
        List.range'_succ]
      exact hp
    obtain ⟨j, hj1, hj2, hpj⟩ := zip_range'_consec 1 (2 * t) p hp'
    rw [hpj] at hpe
    rw [Sym2.eq_iff] at hpe
    omega
  refine ⟨1, Walk.cons hadj
      (chainWalk 1 (List.range' 2 (2 * t - 1)) (2 * t + 1) hchain).reverse,
    SimpleGraph.Path.cons_isCycle
      ⟨(chainWalk 1 (List.range' 2 (2 * t - 1)) (2 * t + 1) hchain).reverse,
        hasc_path.reverse⟩ hadj hnotmem, ?_⟩
  rw [Walk.length_cons, Walk.length_reverse, chainWalk_length]
  have hlr : (List.range' 2 (2 * t - 1)).length = 2 * t - 1 := List.length_range'
  omega

/-! ### The extremal sets -/

/-- The threshold example: the multiples of 2 or 3 in `[1, n]`. -/
def A₀ (n : ℕ) : Finset ℕ := (Icc 1 n).filter (fun m => 2 ∣ m ∨ 3 ∣ m)

/-- The ceiling example: the evens in `[1, n]` plus the `q n + 1` smallest odds. -/
def A₁ (n : ℕ) : Finset ℕ :=
  (Icc 1 n).filter (fun m => 2 ∣ m) ∪ (range (q n + 1)).image (fun k => 2 * k + 1)

lemma Icc_one_eq_Ioc (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext m
  simp [Nat.lt_iff_add_one_le]

lemma card_dvd_filter (n d : ℕ) : ((Icc 1 n).filter (fun m => d ∣ m)).card = n / d := by
  rw [Icc_one_eq_Ioc]
  exact Nat.Ioc_filter_dvd_card_eq_div n d

lemma card_A₀ (n : ℕ) : (A₀ n).card = T n := by
  have h2 := card_dvd_filter n 2
  have h3 := card_dvd_filter n 3
  have h6 := card_dvd_filter n 6
  have hunion : A₀ n =
      (Icc 1 n).filter (fun m => 2 ∣ m) ∪ (Icc 1 n).filter (fun m => 3 ∣ m) := by
    rw [A₀, filter_or]
  have hinter : ((Icc 1 n).filter (fun m => 2 ∣ m)) ∩ ((Icc 1 n).filter (fun m => 3 ∣ m))
      = (Icc 1 n).filter (fun m => 6 ∣ m) := by
    rw [← filter_and]
    apply filter_congr
    intro m _
    constructor
    · rintro ⟨h2m, h3m⟩
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 2 3 by decide) h2m h3m
    · intro h6m
      exact ⟨dvd_trans (show (2 : ℕ) ∣ 6 by decide) h6m,
        dvd_trans (show (3 : ℕ) ∣ 6 by decide) h6m⟩
  have hcard := Finset.card_union_add_card_inter
    ((Icc 1 n).filter (fun m => 2 ∣ m)) ((Icc 1 n).filter (fun m => 3 ∣ m))
  rw [hinter, h2, h3, h6, ← hunion] at hcard
  rw [T]
  omega

lemma odds_inj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
  intro a b h
  simpa using h

lemma card_A₁ (n : ℕ) : (A₁ n).card = T n + 1 := by
  have hdisj : Disjoint ((Icc 1 n).filter (fun m => 2 ∣ m))
      ((range (q n + 1)).image (fun k => 2 * k + 1)) := by
    rw [Finset.disjoint_left]
    intro m hm hodd
    simp only [mem_filter] at hm
    simp only [mem_image] at hodd
    obtain ⟨k, -, hk⟩ := hodd
    obtain ⟨j, hj⟩ := hm.2
    omega
  rw [A₁, Finset.card_union_of_disjoint hdisj, card_dvd_filter n 2,
    Finset.card_image_of_injective _ odds_inj, card_range, T, q]
  omega

lemma two_q_add_one_le (n : ℕ) (hn : 3 ≤ n) : 2 * q n + 1 ≤ n := by
  rw [q]
  omega

lemma A₁_subset (n : ℕ) (hn : 1 ≤ n) : A₁ n ⊆ Icc 1 n := by
  intro m hm
  rw [A₁, mem_union] at hm
  rcases hm with hm | hm
  · exact mem_of_mem_filter m hm
  · simp only [mem_image, mem_range] at hm
    obtain ⟨k, hk, hkm⟩ := hm
    rw [mem_Icc]
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · have hq : q n = 0 := by rw [q]; omega
      omega
    · have := two_q_add_one_le n h3
      omega

/-! ### Threshold sharpness -/

lemma A₀_proper (n : ℕ) :
    ∀ x y, (coprimeGraph (A₀ n)).Adj x y →
      (decide (2 ∣ x) : Bool) ≠ (decide (2 ∣ y) : Bool) := by
  rintro x y ⟨hne, hx, hy, hco⟩
  simp only [A₀, mem_filter] at hx hy
  intro heq
  have hg : Nat.gcd x y = 1 := hco
  by_cases h2x : 2 ∣ x
  · have h2y : 2 ∣ y := by
      by_contra h2y
      simp [h2x, h2y] at heq
    have hdvd : (2 : ℕ) ∣ Nat.gcd x y := Nat.dvd_gcd h2x h2y
    rw [hg] at hdvd
    have := Nat.le_of_dvd one_pos hdvd
    omega
  · have h2y : ¬ 2 ∣ y := by
      by_contra h2y
      simp [h2x, h2y] at heq
    have h3x : 3 ∣ x := (hx.2).resolve_left h2x
    have h3y : 3 ∣ y := (hy.2).resolve_left h2y
    have hdvd : (3 : ℕ) ∣ Nat.gcd x y := Nat.dvd_gcd h3x h3y
    rw [hg] at hdvd
    have := Nat.le_of_dvd one_pos hdvd
    omega

/-- `G(A₀ n)` contains no odd cycle. -/
theorem A₀_no_odd_cycle (n L : ℕ) (hL : Odd L) :
    ¬ HasCycleLength (coprimeGraph (A₀ n)) L := by
  rintro ⟨v, w, -, hlen⟩
  have heven := (walk_length_even_iff (fun m => decide (2 ∣ m)) (A₀_proper n) w).mpr rfl
  rw [hlen] at heven
  exact (Nat.not_even_iff_odd.mpr hL) heven

/-- **Erdős #883, threshold sharpness** (development form). -/
theorem erdos883_threshold_sharp (n : ℕ) :
    ∃ A ⊆ Icc 1 n, A.card = T n ∧
      ∀ L : ℕ, Odd L → ¬ HasCycleLength (coprimeGraph A) L :=
  ⟨A₀ n, filter_subset _ _, card_A₀ n, fun L hL => A₀_no_odd_cycle n L hL⟩

/-! ### Ceiling sharpness -/

/-- In `G(A₁ n)`, a cycle of length `2t+1` (t ≥ 1) forces `t ≤ q n`. -/
theorem A₁_ceiling (n t : ℕ) (ht : 1 ≤ t)
    (h : HasCycleLength (coprimeGraph (A₁ n)) (2 * t + 1)) : t ≤ q n := by
  obtain ⟨u, w, hc, hlen⟩ := h
  have hS : ∀ x y, (coprimeGraph (A₁ n)).Adj x y →
      ¬((decide (2 ∣ x) : Bool) = true ∧ (decide (2 ∣ y) : Bool) = true) := by
    rintro x y ⟨hne, hx, hy, hco⟩ ⟨h2x, h2y⟩
    simp only [decide_eq_true_eq] at h2x h2y
    have hg : Nat.gcd x y = 1 := hco
    have hdvd : (2 : ℕ) ∣ Nat.gcd x y := Nat.dvd_gcd h2x h2y
    rw [hg] at hdvd
    have := Nat.le_of_dvd one_pos hdvd
    omega
  have hcount := cycle_countP_le _ hS w hc
  rw [hlen] at hcount
  have htail_nodup : w.support.tail.Nodup := hc.support_nodup
  have htail_len : w.support.tail.length = 2 * t + 1 := by
    have h1 : w.support.length = w.length + 1 := Walk.length_support w
    rw [List.length_tail, h1, hlen]
    omega
  have hodd_count : t + 1 ≤ w.support.tail.countP (fun m => !(decide (2 ∣ m))) := by
    have hsplit := countP_add_countP_bnot (fun m => decide (2 ∣ m)) w.support.tail
    omega
  have hodd_sub : (w.support.tail.filter (fun m => !(decide (2 ∣ m)))).toFinset
      ⊆ (range (q n + 1)).image (fun k => 2 * k + 1) := by
    intro v hv
    rw [List.mem_toFinset, List.mem_filter] at hv
    obtain ⟨hvmem, hvodd⟩ := hv
    have hvA : v ∈ A₁ n :=
      support_subset_of_cycle w hc v (List.mem_of_mem_tail hvmem)
    rw [A₁, mem_union] at hvA
    rcases hvA with hvA | hvA
    · rw [mem_filter] at hvA
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hvodd
      exact absurd hvA.2 hvodd
    · exact hvA
  have hodd_card : (w.support.tail.filter (fun m => !(decide (2 ∣ m)))).toFinset.card
      = w.support.tail.countP (fun m => !(decide (2 ∣ m))) := by
    rw [List.toFinset_card_of_nodup (htail_nodup.filter _), List.countP_eq_length_filter]
  have hle := Finset.card_le_card hodd_sub
  rw [hodd_card, Finset.card_image_of_injective _ odds_inj, card_range] at hle
  omega

/-- The attained lengths in `G(A₁ n)`. -/
theorem A₁_attains (n t : ℕ) (ht : 1 ≤ t) (htq : t ≤ q n) :
    HasCycleLength (coprimeGraph (A₁ n)) (2 * t + 1) := by
  apply cycle_of_consec _ t ht
  intro j hj1 hj2
  have hq1 : 1 ≤ q n := le_trans ht htq
  have hn3 : 3 ≤ n := by
    by_contra h3
    have hq0 : q n = 0 := by rw [q]; omega
    omega
  have h2q := two_q_add_one_le n hn3
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [A₁, mem_union]
    left
    rw [mem_filter, mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨k, by omega⟩⟩
  · rw [A₁, mem_union]
    right
    rw [mem_image]
    exact ⟨k, by rw [mem_range]; omega, by omega⟩

/-- **Erdős #883, ceiling sharpness and attainment** (development form). -/
theorem erdos883_ceiling_sharp (n : ℕ) (hn : 1 ≤ n) :
    ∃ A ⊆ Icc 1 n, A.card = T n + 1 ∧
      (∀ t : ℕ, 1 ≤ t → t ≤ q n → HasCycleLength (coprimeGraph A) (2 * t + 1)) ∧
      (∀ t : ℕ, q n < t → ¬ HasCycleLength (coprimeGraph A) (2 * t + 1)) :=
  ⟨A₁ n, A₁_subset n hn, card_A₁ n,
    fun t ht htq => A₁_attains n t ht htq,
    fun t htq h => absurd (A₁_ceiling n t (by omega) h) (by omega)⟩

end Erdos883
