import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Sendov9.Mac

open Finset

/-!
# `MaclaurinIneq` at `n = 8`, assembled

`Maclaurin.lean` banked the smoothing engine (`esymm_insert`, `esymm_pair`, `avg_ge`)
and `MaclaurinNet.lean` banked the butterfly network (`network_const`).  Neither file
ever put the two together, so the master still carried `MaclaurinIneq` as a hypothesis.
This file closes that: `avg_mono` upgrades `avg_ge` from "a pair sitting outside an
explicit `t`" to "any pair of `univ`", and then twelve applications of it, followed by
`network_const` + `E_const`, give Maclaurin at `n = 8` outright.

The only genuinely fiddly step is `avg_mono`'s bookkeeping: `avg_ge` wants
`univ = insert i (insert j t)` with `i, j ∉ t`, which is `Finset.insert_erase` twice.
Orders `m = 0, 1` fall outside `avg_ge`'s `m + 2` shape and are handled directly --
at `m = 1` the step is an *equality*, which is exactly `avg_sum`.
-/




open Finset

/-!
# Maclaurin for `n = 8`, by smoothing — no Newton inequalities

Discharges the `MaclaurinIneq` hypothesis.  The route (owner-supplied blueprint,
refereed 2026-07-27) avoids real-rootedness, differentiation, compactness and limits
entirely:

1. **`esymm_insert`** — adjoining one coordinate: `eₘ₊₁(insert i t) = eₘ₊₁(t) + xᵢ·eₘ(t)`.
2. **`esymm_pair`** — hence, for two fresh coordinates,
   `eₘ(a,b,z) = eₘ(z) + (a+b)eₘ₋₁(z) + ab·eₘ₋₂(z)`.
3. **`avg_ge`** — averaging a pair keeps `a+b` fixed and raises `ab`, so
   `eₘ(c,c,z) - eₘ(a,b,z) = ((a-b)²/4)·eₘ₋₂(z) ≥ 0`.
4. **The network** — since `8 = 2³`, *twelve* pair-averagings in butterfly order land
   **exactly** on `(T/8,…,T/8)`; no limiting argument is needed.  Then
   `eₘ = C(8,m)(T/8)^m`.

For `m = 5,…,8` the resulting constants `C(8,m) = 56, 28, 8, 1` are exactly the paper's
`c₅,…,c₈`, which is the only range where `MaclaurinIneq` is used.  (At `m = 3,4` the
paper needs the sharper `264/35` and `24`, which come from the centring `∑Dⱼ = 0` and
still require `NewtonCentred`.)
-/

variable {ι : Type*} [DecidableEq ι]

/-- `eₘ` for a family over a finite index set. -/
noncomputable def E (x : ι → ℝ) (s : Finset ι) (m : ℕ) : ℝ :=
  ∑ A ∈ s.powersetCard m, ∏ k ∈ A, x k

@[simp] theorem E_zero (x : ι → ℝ) (s : Finset ι) : E x s 0 = 1 := by
  simp [E, Finset.powersetCard_zero]

/-- `eₘ ≥ 0` for nonnegative families. -/
theorem E_nonneg {x : ι → ℝ} (hx : ∀ k, 0 ≤ x k) (s : Finset ι) (m : ℕ) : 0 ≤ E x s m := by
  refine Finset.sum_nonneg fun A _ => Finset.prod_nonneg fun k _ => hx k

/-- **Step 1.** Adjoining one coordinate. -/
theorem esymm_insert {t : Finset ι} {i : ι} (hi : i ∉ t) (x : ι → ℝ) (m : ℕ) :
    E x (insert i t) (m + 1) = E x t (m + 1) + x i * E x t m := by
  unfold E
  rw [Finset.powersetCard_succ_insert hi]
  have hdisj : Disjoint (t.powersetCard (m + 1)) ((t.powersetCard m).image (insert i)) := by
    rw [Finset.disjoint_right]
    rintro A hA hA'
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    have hsub : insert i B ⊆ t := (Finset.mem_powersetCard.mp hA').1
    exact hi (hsub (Finset.mem_insert_self i B))
  rw [Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun B hB => ?_
    have hiB : i ∉ B := fun h => hi ((Finset.mem_powersetCard.mp hB).1 h)
    rw [Finset.prod_insert hiB]
  · intro B hB C hC hBC
    have hiB : i ∉ B := fun h => hi ((Finset.mem_powersetCard.mp hB).1 h)
    have hiC : i ∉ C := fun h => hi ((Finset.mem_powersetCard.mp hC).1 h)
    have := congrArg (fun s => Finset.erase s i) hBC
    simpa [Finset.erase_insert hiB, Finset.erase_insert hiC] using this

/-- **Step 2.** Two fresh coordinates. -/
theorem esymm_pair {t : Finset ι} {i j : ι} (hi : i ∉ t) (hj : j ∉ t) (hij : i ≠ j)
    (x : ι → ℝ) (m : ℕ) :
    E x (insert i (insert j t)) (m + 2)
      = E x t (m + 2) + (x i + x j) * E x t (m + 1) + (x i * x j) * E x t m := by
  have hij' : i ∉ insert j t := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hij, hi⟩
  rw [esymm_insert hij' x (m + 1), esymm_insert hj x (m + 1), esymm_insert hj x m]
  ring

/-- **Step 3.** Averaging a pair does not decrease `eₘ`. -/
theorem avg_ge {t : Finset ι} {i j : ι} (hi : i ∉ t) (hj : j ∉ t) (hij : i ≠ j)
    (x y : ι → ℝ) (hx : ∀ k, 0 ≤ x k) (m : ℕ)
    (hy : ∀ k ∈ t, y k = x k)
    (hyi : y i = (x i + x j) / 2) (hyj : y j = (x i + x j) / 2) :
    E x (insert i (insert j t)) (m + 2) ≤ E y (insert i (insert j t)) (m + 2) := by
  have hEt : ∀ r, E y t r = E x t r := by
    intro r
    unfold E
    refine Finset.sum_congr rfl fun A hA => ?_
    refine Finset.prod_congr rfl fun k hk => ?_
    exact hy k ((Finset.mem_powersetCard.mp hA).1 hk)
  rw [esymm_pair hi hj hij x m, esymm_pair hi hj hij y m, hEt, hEt, hEt, hyi, hyj]
  have hsum : (x i + x j) / 2 + (x i + x j) / 2 = x i + x j := by ring
  rw [hsum]
  have hprod : x i * x j ≤ (x i + x j) / 2 * ((x i + x j) / 2) := by nlinarith [sq_nonneg (x i - x j)]
  have hE : 0 ≤ E x t m := E_nonneg hx t m
  nlinarith [hprod, hE]






open Finset

/-!
# Maclaurin for `n = 8`: the averaging network

`Maclaurin.lean` banked the engine (`esymm_insert`, `esymm_pair`, `avg_ge`).  This file
runs the network and evaluates at the constant vector, completing the discharge of
`MaclaurinIneq` for `n = 8`.

The network is a butterfly: pairs `(0,1)(2,3)(4,5)(6,7)`, then `(0,2)(1,3)(4,6)(5,7)`,
then `(0,4)(1,5)(2,6)(3,7)`.  Because `8 = 2³`, after those twelve averagings every
coordinate equals `T/8` **exactly** — this is why no limiting argument is needed, and
it is the observation that makes the whole route formalizable.
-/

variable {ι : Type*} [DecidableEq ι]

/-- **Evaluation at a constant vector.**  `eₘ(w,…,w) = C(|s|,m)·wᵐ`. -/
theorem E_const (w : ℝ) (s : Finset ι) (m : ℕ) :
    E (fun _ => w) s m = (s.card.choose m : ℝ) * w ^ m := by
  unfold E
  have h : ∀ A ∈ s.powersetCard m, ∏ _k ∈ A, w = w ^ m := by
    intro A hA
    rw [Finset.prod_const, (Finset.mem_powersetCard.mp hA).2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

/-- The averaging operation on a `Fin 8` family. -/
noncomputable def avg (x : Fin 8 → ℝ) (i j : Fin 8) : Fin 8 → ℝ :=
  fun k => if k = i ∨ k = j then (x i + x j) / 2 else x k

theorem avg_nonneg {x : Fin 8 → ℝ} (hx : ∀ k, 0 ≤ x k) (i j : Fin 8) :
    ∀ k, 0 ≤ avg x i j k := by
  intro k
  unfold avg
  split
  · have := hx i; have := hx j; linarith
  · exact hx k

/-- Averaging preserves the total. -/
theorem avg_sum (x : Fin 8 → ℝ) {i j : Fin 8} (hij : i ≠ j) :
    ∑ k, avg x i j k = ∑ k, x k := by
  have hsplit : ∀ (f : Fin 8 → ℝ),
      ∑ k, f k = f i + f j + ∑ k ∈ (univ.erase i).erase j, f k := by
    intro f
    rw [← Finset.add_sum_erase _ f (Finset.mem_univ i),
      ← Finset.add_sum_erase _ f (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
    ring
  rw [hsplit (avg x i j), hsplit x]
  have hi : avg x i j i = (x i + x j) / 2 := by unfold avg; simp
  have hj : avg x i j j = (x i + x j) / 2 := by unfold avg; simp [hij]
  have hrest : ∀ k ∈ (univ.erase i).erase j, avg x i j k = x k := by
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    unfold avg
    simp [hki, hkj]
  rw [hi, hj, Finset.sum_congr rfl hrest]
  ring

/-! ### The network, one round at a time

A single 12-deep composition of `avg` overflows `whnf`: each layer is an
`if k = i ∨ k = j` whose `Decidable` instance must be evaluated, and `fin_cases` then
faces 2^12 branches.  Splitting into the three butterfly rounds keeps every proof to
one layer over an explicit vector. -/

/-- Round 1: pairs `(0,1) (2,3) (4,5) (6,7)`. -/
theorem round1 (x : Fin 8 → ℝ) :
    avg (avg (avg (avg x 0 1) 2 3) 4 5) 6 7
      = ![(x 0 + x 1) / 2, (x 0 + x 1) / 2, (x 2 + x 3) / 2, (x 2 + x 3) / 2,
          (x 4 + x 5) / 2, (x 4 + x 5) / 2, (x 6 + x 7) / 2, (x 6 + x 7) / 2] := by
  funext k
  fin_cases k <;> simp [avg] <;> ring

/-- Round 2: pairs `(0,2) (1,3) (4,6) (5,7)`. -/
theorem round2 (a b c d : ℝ) :
    avg (avg (avg (avg ![a, a, b, b, c, c, d, d] 0 2) 1 3) 4 6) 5 7
      = ![(a + b) / 2, (a + b) / 2, (a + b) / 2, (a + b) / 2,
          (c + d) / 2, (c + d) / 2, (c + d) / 2, (c + d) / 2] := by
  funext k
  fin_cases k <;> simp [avg] <;> ring

/-- Round 3: pairs `(0,4) (1,5) (2,6) (3,7)`. -/
theorem round3 (u v : ℝ) :
    avg (avg (avg (avg ![u, u, u, u, v, v, v, v] 0 4) 1 5) 2 6) 3 7
      = fun _ => (u + v) / 2 := by
  funext k
  fin_cases k <;> simp [avg] <;> ring

/-- **The network reaches the constant vector.**  Twelve butterfly averagings send any
`x : Fin 8 → ℝ` to the constant family `T/8`.  Note this identity is unconditional --
nonnegativity is needed only for the MONOTONICITY step `avg_ge`, not here. -/
theorem network_const (x : Fin 8 → ℝ) :
    avg (avg (avg (avg (avg (avg (avg (avg (avg (avg (avg (avg x 0 1) 2 3) 4 5) 6 7)
      0 2) 1 3) 4 6) 5 7) 0 4) 1 5) 2 6) 3 7
      = fun _ => (∑ k, x k) / 8 := by
  rw [round1, round2, round3]
  funext k
  rw [Fin.sum_univ_eight]
  ring



/-- `e₁ = ∑ xᵢ`. -/
theorem E_one (x : ι → ℝ) (s : Finset ι) : E x s 1 = ∑ i ∈ s, x i := by
  simp [E, Finset.powersetCard_one]

/-- **Averaging any pair of `univ` does not decrease `eₘ`.**  This is `avg_ge` with the
`insert`/`erase` bookkeeping discharged, so it applies to the twelve butterfly pairs. -/
theorem avg_mono (x : Fin 8 → ℝ) (hx : ∀ k, 0 ≤ x k) {i j : Fin 8} (hij : i ≠ j) (m : ℕ) :
    E x univ m ≤ E (avg x i j) univ m := by
  match m with
  | 0 => simp [E_zero]
  | 1 =>
      rw [E_one, E_one, avg_sum x hij]
  | (m + 2) =>
      have h1 : insert j ((univ.erase i).erase j) = univ.erase i :=
        Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
      have h2 : insert i ((univ : Finset (Fin 8)).erase i) = univ :=
        Finset.insert_erase (Finset.mem_univ i)
      have huniv : (univ : Finset (Fin 8)) = insert i (insert j ((univ.erase i).erase j)) := by
        rw [h1, h2]
      have hi : i ∉ (univ.erase i).erase j := fun h =>
        (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl
      have hjt : j ∉ (univ.erase i).erase j := fun h => (Finset.mem_erase.mp h).1 rfl
      rw [huniv]
      refine avg_ge hi hjt hij x (avg x i j) hx m ?_ ?_ ?_
      · intro k hk
        have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
        have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
        unfold avg
        simp [hki, hkj]
      · unfold avg; simp
      · unfold avg; simp

/-- **Maclaurin's inequality at `n = 8`.**  Twelve monotone averagings carry `eₘ(x)` up
to `eₘ` of the constant vector, which `E_const` evaluates.  Note no `m ≤ 8` hypothesis is
needed: above `m = 8` both sides are zero. -/
theorem maclaurin_eight (x : Fin 8 → ℝ) (hx : ∀ k, 0 ≤ x k) (m : ℕ) :
    E x univ m ≤ (Nat.choose 8 m : ℝ) * ((∑ k, x k) / 8) ^ m := by
  have h1 := avg_mono x hx (i := 0) (j := 1) (by decide) m
  have n1 := avg_nonneg hx (0 : Fin 8) 1
  have h2 := avg_mono _ n1 (i := 2) (j := 3) (by decide) m
  have n2 := avg_nonneg n1 (2 : Fin 8) 3
  have h3 := avg_mono _ n2 (i := 4) (j := 5) (by decide) m
  have n3 := avg_nonneg n2 (4 : Fin 8) 5
  have h4 := avg_mono _ n3 (i := 6) (j := 7) (by decide) m
  have n4 := avg_nonneg n3 (6 : Fin 8) 7
  have h5 := avg_mono _ n4 (i := 0) (j := 2) (by decide) m
  have n5 := avg_nonneg n4 (0 : Fin 8) 2
  have h6 := avg_mono _ n5 (i := 1) (j := 3) (by decide) m
  have n6 := avg_nonneg n5 (1 : Fin 8) 3
  have h7 := avg_mono _ n6 (i := 4) (j := 6) (by decide) m
  have n7 := avg_nonneg n6 (4 : Fin 8) 6
  have h8 := avg_mono _ n7 (i := 5) (j := 7) (by decide) m
  have n8 := avg_nonneg n7 (5 : Fin 8) 7
  have h9 := avg_mono _ n8 (i := 0) (j := 4) (by decide) m
  have n9 := avg_nonneg n8 (0 : Fin 8) 4
  have h10 := avg_mono _ n9 (i := 1) (j := 5) (by decide) m
  have n10 := avg_nonneg n9 (1 : Fin 8) 5
  have h11 := avg_mono _ n10 (i := 2) (j := 6) (by decide) m
  have n11 := avg_nonneg n10 (2 : Fin 8) 6
  have h12 := avg_mono _ n11 (i := 3) (j := 7) (by decide) m
  have hfin : E (avg (avg (avg (avg (avg (avg (avg (avg (avg (avg (avg (avg x 0 1) 2 3) 4 5)
      6 7) 0 2) 1 3) 4 6) 5 7) 0 4) 1 5) 2 6) 3 7) univ m
      = (Nat.choose 8 m : ℝ) * ((∑ k, x k) / 8) ^ m := by
    rw [network_const, E_const]
    simp
  rw [← hfin]
  linarith

end Sendov9.Mac

/-! ## Discharge of the carried hypothesis

`Master.MaclaurinIneq` is stated for a general `n`; the paper only ever uses `n = 8`
(the eight roots `Dⱼ`).  `MaclaurinIneq8` below is `Master.MaclaurinIneq` with `n := 8`
substituted, verbatim -- and it is a theorem. -/

namespace Sendov9

open Finset

/-- `Master.MaclaurinIneq` at `n = 8`. -/
def MaclaurinIneq8 : Prop :=
  ∀ (m : ℕ) (x : Fin 8 → ℝ), (∀ i, 0 ≤ x i) → m ≤ 8 →
    ∑ s ∈ (univ : Finset (Fin 8)).powersetCard m, ∏ i ∈ s, x i
      ≤ ((8:ℕ).choose m : ℝ) * ((∑ i, x i) / 8) ^ m

/-- **`MaclaurinIneq8` is a theorem.** -/
theorem maclaurinIneq8 : MaclaurinIneq8 := fun m x hx _ => Mac.maclaurin_eight x hx m

end Sendov9

#print axioms Sendov9.Mac.E_one
#print axioms Sendov9.Mac.avg_mono
#print axioms Sendov9.Mac.maclaurin_eight
#print axioms Sendov9.maclaurinIneq8
