/-
# The tensor-product Bernstein representation theorem

Companion engine for `Sendov9to11.lean`.  That file proves the *bound* direction
(`bernstein_lower_bound`): a table dominating `c` forces the Bernstein sum to
dominate `c`.  What it lacks — and what blocks every one of the paper's 598
certificates from being checked in the kernel — is the *representation*
direction: that a given table really is the Bernstein table of a given
polynomial.

This file supplies it.  The pivot is the division-free identity

  `∑_{i≤n} C(i,k) · bern n i U = C(n,k) · U^k`,

which follows from the subset-of-a-subset relation `C(n,i)·C(i,k) =
C(n,k)·C(n-k,i-k)` (`Nat.choose_mul`) plus the binomial theorem.  Dividing by
`C(n,k)` gives the change of basis, and tensoring gives the bivariate form.

Everything here is general: no Sendov-specific data appears.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Sendov911Bern

open Finset

/-! ## The Bernstein basis -/

/-- The univariate Bernstein basis polynomial `C(r,i) · Uⁱ · (1-U)^{r-i}`. -/
noncomputable def bern (r i : ℕ) (U : ℝ) : ℝ :=
  (r.choose i : ℝ) * U ^ i * (1 - U) ^ (r - i)

theorem bern_nonneg (r i : ℕ) {U : ℝ} (h0 : 0 ≤ U) (h1 : U ≤ 1) :
    0 ≤ bern r i U := by
  have h : (0 : ℝ) ≤ 1 - U := by linarith
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0 i)) (pow_nonneg h _)

/-- The Bernstein basis of degree `r` is a partition of unity. -/
theorem sum_bern (r : ℕ) (U : ℝ) :
    ∑ i ∈ range (r + 1), bern r i U = 1 := by
  calc ∑ i ∈ range (r + 1), bern r i U
      = ∑ i ∈ range (r + 1), U ^ i * (1 - U) ^ (r - i) * (r.choose i : ℝ) := by
        refine sum_congr rfl fun i _ => ?_
        simp only [bern]; ring
    _ = ((U + (1 - U)) : ℝ) ^ r := (add_pow U (1 - U) r).symm
    _ = 1 := by norm_num

/-! ## The division-free change of basis

`∑_{i≤n} C(i,k) · bern n i U = C(n,k) · U^k`.  Both sides vanish when `k > n`.
-/

theorem sum_choose_mul_bern (n k : ℕ) (U : ℝ) :
    ∑ i ∈ range (n + 1), (i.choose k : ℝ) * bern n i U = (n.choose k : ℝ) * U ^ k := by
  by_cases hkn : k ≤ n
  · -- Terms with `i < k` vanish, so the sum is over `i = k + j`, `j ≤ n - k`.
    have hsplit : ∑ i ∈ range (n + 1), (i.choose k : ℝ) * bern n i U
        = ∑ j ∈ range (n - k + 1), ((k + j).choose k : ℝ) * bern n (k + j) U := by
      rw [← sum_range_add_sum_Ico _ (by omega : k ≤ n + 1)]
      have hlow : ∑ i ∈ range k, (i.choose k : ℝ) * bern n i U = 0 := by
        refine sum_eq_zero fun i hi => ?_
        rw [mem_range] at hi
        rw [Nat.choose_eq_zero_of_lt hi]
        simp
      rw [hlow, zero_add, Finset.sum_Ico_eq_sum_range]
      have hlen : n + 1 - k = n - k + 1 := by omega
      rw [hlen]
    rw [hsplit]
    -- `C(k+j, k) * C(n, k+j) = C(n,k) * C(n-k, j)`
    have hkey : ∀ j ∈ range (n - k + 1),
        ((k + j).choose k : ℝ) * bern n (k + j) U
          = (n.choose k : ℝ) * ((n - k).choose j : ℝ) * U ^ (k + j) * (1 - U) ^ (n - k - j) := by
      intro j hj
      rw [mem_range] at hj
      have hid : n.choose (k + j) * (k + j).choose k = n.choose k * (n - k).choose (k + j - k) :=
        Nat.choose_mul (Nat.le_add_right k j)
      have hkj : k + j - k = j := by omega
      rw [hkj] at hid
      have hsub : n - (k + j) = n - k - j := by omega
      simp only [bern, hsub]
      have : ((k + j).choose k : ℝ) * ((n.choose (k + j) : ℝ) * U ^ (k + j) * (1 - U) ^ (n - k - j))
          = ((n.choose (k + j) * (k + j).choose k : ℕ) : ℝ) * U ^ (k + j) * (1 - U) ^ (n - k - j) := by
        push_cast; ring
      rw [this, hid]
      push_cast; ring
    rw [sum_congr rfl hkey]
    -- factor `U^k` and apply the binomial theorem to the remaining sum
    have : ∑ j ∈ range (n - k + 1),
        (n.choose k : ℝ) * ((n - k).choose j : ℝ) * U ^ (k + j) * (1 - U) ^ (n - k - j)
        = (n.choose k : ℝ) * U ^ k *
            ∑ j ∈ range (n - k + 1), ((n - k).choose j : ℝ) * U ^ j * (1 - U) ^ (n - k - j) := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [pow_add]; ring
    rw [this]
    have hbin : ∑ j ∈ range (n - k + 1), ((n - k).choose j : ℝ) * U ^ j * (1 - U) ^ (n - k - j)
        = 1 := by
      have := sum_bern (n - k) U
      simpa [bern] using this
    rw [hbin, mul_one]
  · -- `k > n`: every `C(i,k)` with `i ≤ n` vanishes, and `C(n,k) = 0`.
    push_neg at hkn
    have hz : ∑ i ∈ range (n + 1), (i.choose k : ℝ) * bern n i U = 0 := by
      refine sum_eq_zero fun i hi => ?_
      rw [mem_range] at hi
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [hz, Nat.choose_eq_zero_of_lt hkn]
    simp

/-- The change of basis in the form used below: for `k ≤ n`,
`U^k = ∑_{i≤n} (C(i,k)/C(n,k)) · bern n i U`. -/
theorem pow_eq_sum_weight_bern {n k : ℕ} (hk : k ≤ n) (U : ℝ) :
    U ^ k = ∑ i ∈ range (n + 1), ((i.choose k : ℝ) / (n.choose k : ℝ)) * bern n i U := by
  have hne : ((n.choose k : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  have h : ∑ i ∈ range (n + 1), ((i.choose k : ℝ) / (n.choose k : ℝ)) * bern n i U
      = (∑ i ∈ range (n + 1), (i.choose k : ℝ) * bern n i U) / (n.choose k : ℝ) := by
    rw [sum_div]
    exact sum_congr rfl fun i _ => by ring
  rw [h, sum_choose_mul_bern]
  field_simp

/-- **Univariate representation.**  A polynomial written in the monomial basis
equals its Bernstein expansion of degree `n`.  This is the workhorse: the
bivariate case is two applications of it. -/
theorem univ_repr (n : ℕ) (c : ℕ → ℝ) (U : ℝ) :
    ∑ k ∈ range (n + 1), c k * U ^ k
      = ∑ i ∈ range (n + 1),
          (∑ k ∈ range (n + 1), c k * ((i.choose k : ℝ) / (n.choose k : ℝ))) * bern n i U := by
  have hexp : ∑ i ∈ range (n + 1),
      (∑ k ∈ range (n + 1), c k * ((i.choose k : ℝ) / (n.choose k : ℝ))) * bern n i U
      = ∑ i ∈ range (n + 1), ∑ k ∈ range (n + 1),
          c k * (((i.choose k : ℝ) / (n.choose k : ℝ)) * bern n i U) := by
    refine sum_congr rfl fun i _ => ?_
    rw [sum_mul]
    exact sum_congr rfl fun k _ => by ring
  rw [hexp, sum_comm]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  rw [← mul_sum, ← pow_eq_sum_weight_bern (by omega : k ≤ n) U]

/-! ## The bivariate representation theorem

For a polynomial given in the monomial basis by a coefficient table `m`
supported in `k ≤ nx`, `l ≤ ny`, the tensor-product Bernstein coefficients are

  `b i j = ∑_{k≤nx, l≤ny} m k l · (C(i,k)/C(nx,k)) · (C(j,l)/C(ny,l))`,

and the two representations agree pointwise.  This is the theorem the paper's
verifiers compute numerically (`bernstein_coefficients`), stated and proved once
so that no per-certificate polynomial identity is ever needed. -/

/-- The `V`-direction Bernstein transform of row `k` of the monomial table. -/
noncomputable def bernRow (ny : ℕ) (m : ℕ → ℕ → ℝ) (k j : ℕ) : ℝ :=
  ∑ l ∈ range (ny + 1), m k l * ((j.choose l : ℝ) / (ny.choose l : ℝ))

/-- The tensor-product Bernstein coefficient table of a monomial table:
transform in `V`, then in `U`. -/
noncomputable def bernTable (nx ny : ℕ) (m : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ k ∈ range (nx + 1), bernRow ny m k j * ((i.choose k : ℝ) / (nx.choose k : ℝ))

/-- The table in the flat form the paper's verifiers compute:
`b i j = ∑_{k,l} m k l · C(i,k)/C(nx,k) · C(j,l)/C(ny,l)`. -/
theorem bernTable_eq_flat (nx ny : ℕ) (m : ℕ → ℕ → ℝ) (i j : ℕ) :
    bernTable nx ny m i j
      = ∑ k ∈ range (nx + 1), ∑ l ∈ range (ny + 1),
          m k l * ((i.choose k : ℝ) / (nx.choose k : ℝ)) * ((j.choose l : ℝ) / (ny.choose l : ℝ)) := by
  simp only [bernTable, bernRow, sum_mul]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring

/-- **Representation theorem.**  A bivariate polynomial written in the monomial
basis equals its tensor-product Bernstein expansion. -/
theorem monomial_eq_bern (nx ny : ℕ) (m : ℕ → ℕ → ℝ) (U V : ℝ) :
    ∑ k ∈ range (nx + 1), ∑ l ∈ range (ny + 1), m k l * U ^ k * V ^ l
      = ∑ i ∈ range (nx + 1), ∑ j ∈ range (ny + 1),
          bernTable nx ny m i j * (bern nx i U * bern ny j V) := by
  -- Collapse the `V`-sum, leaving a univariate polynomial in `U`.
  have hA : ∑ k ∈ range (nx + 1), ∑ l ∈ range (ny + 1), m k l * U ^ k * V ^ l
      = ∑ k ∈ range (nx + 1), (∑ l ∈ range (ny + 1), m k l * V ^ l) * U ^ k := by
    refine sum_congr rfl fun k _ => ?_
    rw [sum_mul]
    exact sum_congr rfl fun l _ => by ring
  -- Each row is its own Bernstein expansion in `V`.
  have hC : ∀ k, (∑ l ∈ range (ny + 1), m k l * V ^ l)
      = ∑ j ∈ range (ny + 1), bernRow ny m k j * bern ny j V := fun k => univ_repr ny (m k) V
  rw [hA, univ_repr nx (fun k => ∑ l ∈ range (ny + 1), m k l * V ^ l) U]
  refine sum_congr rfl fun i _ => ?_
  -- Expand the row transforms and swap the `k`/`j` sums.
  have hstep : ∑ k ∈ range (nx + 1),
      (∑ l ∈ range (ny + 1), m k l * V ^ l) * ((i.choose k : ℝ) / (nx.choose k : ℝ))
      = ∑ j ∈ range (ny + 1), bernTable nx ny m i j * bern ny j V := by
    have h1 : ∑ k ∈ range (nx + 1),
        (∑ l ∈ range (ny + 1), m k l * V ^ l) * ((i.choose k : ℝ) / (nx.choose k : ℝ))
        = ∑ k ∈ range (nx + 1), ∑ j ∈ range (ny + 1),
            bernRow ny m k j * ((i.choose k : ℝ) / (nx.choose k : ℝ)) * bern ny j V := by
      refine sum_congr rfl fun k _ => ?_
      rw [hC k, sum_mul]
      exact sum_congr rfl fun j _ => by ring
    rw [h1, sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [bernTable, sum_mul]
  rw [hstep, sum_mul]
  exact sum_congr rfl fun j _ => by ring

/-! ## The box certificate

Combining the representation theorem with the bound direction: if every
tensor-product Bernstein coefficient of `m` is at least `c`, then the polynomial
is at least `c` on the whole unit square.  This is the single lemma each of the
paper's 598 certificates instantiates. -/

theorem bernstein_lower_bound {r s : ℕ} {c : ℝ} (b : ℕ → ℕ → ℝ)
    (hb : ∀ i ∈ range (r + 1), ∀ j ∈ range (s + 1), c ≤ b i j)
    {U V : ℝ} (hU0 : 0 ≤ U) (hU1 : U ≤ 1) (hV0 : 0 ≤ V) (hV1 : V ≤ 1) :
    c ≤ ∑ i ∈ range (r + 1), ∑ j ∈ range (s + 1), b i j * (bern r i U * bern s j V) := by
  have hbase : ∑ i ∈ range (r + 1), ∑ j ∈ range (s + 1), c * (bern r i U * bern s j V) = c := by
    calc ∑ i ∈ range (r + 1), ∑ j ∈ range (s + 1), c * (bern r i U * bern s j V)
        = c * ∑ i ∈ range (r + 1), ∑ j ∈ range (s + 1), bern r i U * bern s j V := by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by rw [mul_sum]
      _ = c * ((∑ i ∈ range (r + 1), bern r i U) * (∑ j ∈ range (s + 1), bern s j V)) := by
          rw [sum_mul_sum]
      _ = c := by rw [sum_bern, sum_bern]; ring
  calc c = ∑ i ∈ range (r + 1), ∑ j ∈ range (s + 1), c * (bern r i U * bern s j V) := hbase.symm
    _ ≤ _ := by
        refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
        exact mul_le_mul_of_nonneg_right (hb i hi j hj)
          (mul_nonneg (bern_nonneg _ _ hU0 hU1) (bern_nonneg _ _ hV0 hV1))

/-- **Box certificate (unit square).**  If every tensor-product Bernstein
coefficient of the monomial table `m` is at least `c`, then the polynomial
`∑ m k l U^k V^l` is at least `c` on `[0,1]²`. -/
theorem cert_unit_square {nx ny : ℕ} {c : ℝ} (m : ℕ → ℕ → ℝ)
    (hb : ∀ i ∈ range (nx + 1), ∀ j ∈ range (ny + 1), c ≤ bernTable nx ny m i j)
    {U V : ℝ} (hU0 : 0 ≤ U) (hU1 : U ≤ 1) (hV0 : 0 ≤ V) (hV1 : V ≤ 1) :
    c ≤ ∑ k ∈ range (nx + 1), ∑ l ∈ range (ny + 1), m k l * U ^ k * V ^ l := by
  rw [monomial_eq_bern nx ny m U V]
  exact bernstein_lower_bound _ hb hU0 hU1 hV0 hV1

/-! ## The integer bridge

The tables the paper's verifiers produce are rationals with 200-digit
numerators; comparing them in the kernel as rationals is hopeless.  But if the
monomial coefficients are written `m k l = A k l / D` with `A` integral, and `L`
is any common multiple of the binomial denominators `C(nx,k)·C(ny,l)`, then

  `bernTable i j = (∑_{k,l} A k l · C(i,k) · C(j,l) · (L / (C(nx,k)·C(ny,l)))) / (D·L)`

and the numerator is an **integer**.  Positivity then reduces to integer
comparisons, which the kernel does on GMP-backed arithmetic. -/

/-- The integer numerator of the Bernstein table entry, scaled by `D·L`.  `Q k l`
is the cofactor `L / (C(nx,k)·C(ny,l))`, supplied as data so that no division
occurs anywhere. -/
def intTable (nx ny : ℕ) (A Q : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ :=
  ∑ k ∈ range (nx + 1), ∑ l ∈ range (ny + 1),
    A k l * (i.choose k : ℤ) * (j.choose l : ℤ) * Q k l

/-- **The bridge.**  The rational Bernstein table is the integer table over `D·L`. -/
theorem bernTable_eq_intTable {nx ny : ℕ} (A Q : ℕ → ℕ → ℤ) {D L : ℝ} {Lz : ℤ}
    (hD : D ≠ 0) (hLz : (Lz : ℝ) = L) (hL : L ≠ 0)
    (hQ : ∀ k ∈ range (nx + 1), ∀ l ∈ range (ny + 1),
      ((nx.choose k : ℤ) * (ny.choose l : ℤ)) * Q k l = Lz)
    (i j : ℕ) :
    bernTable nx ny (fun k l => (A k l : ℝ) / D) i j
      = (intTable nx ny A Q i j : ℝ) / (D * L) := by
  rw [bernTable_eq_flat, intTable]
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun k hk => ?_
  rw [sum_div]
  refine sum_congr rfl fun l hl => ?_
  have hkn : k ≤ nx := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hln : l ≤ ny := Nat.lt_succ_iff.mp (mem_range.mp hl)
  have hnx : ((nx.choose k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hkn).ne'
  have hny : ((ny.choose l : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hln).ne'
  have hLreal : ((nx.choose k : ℕ) : ℝ) * ((ny.choose l : ℕ) : ℝ) * ((Q k l : ℤ) : ℝ) = L := by
    have := congrArg (fun z : ℤ => (z : ℝ)) (hQ k hk l hl)
    push_cast at this
    rw [this, hLz]
  have hQne : ((Q k l : ℤ) : ℝ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hLreal
    exact hL hLreal.symm
  rw [← hLreal]
  field_simp

/-- **Integer box certificate.**  Everything the kernel must check for one box is
the integer inequality `cnum ≤ intTable i j`. -/
theorem cert_of_intTable {nx ny : ℕ} (A Q : ℕ → ℕ → ℤ) {D L : ℝ} {Lz cnum : ℤ}
    (hD : 0 < D) (hLz : (Lz : ℝ) = L) (hL : 0 < L)
    (hQ : ∀ k ∈ range (nx + 1), ∀ l ∈ range (ny + 1),
      ((nx.choose k : ℤ) * (ny.choose l : ℤ)) * Q k l = Lz)
    (hpos : 0 < cnum)
    (hint : ∀ i ∈ range (nx + 1), ∀ j ∈ range (ny + 1), cnum ≤ intTable nx ny A Q i j)
    {U V : ℝ} (hU0 : 0 ≤ U) (hU1 : U ≤ 1) (hV0 : 0 ≤ V) (hV1 : V ≤ 1) :
    0 < ∑ k ∈ range (nx + 1), ∑ l ∈ range (ny + 1), ((A k l : ℝ) / D) * U ^ k * V ^ l := by
  have hDL : (0 : ℝ) < D * L := mul_pos hD hL
  refine lt_of_lt_of_le (by positivity : (0:ℝ) < (cnum : ℝ) / (D * L)) ?_
  refine cert_unit_square (c := (cnum : ℝ) / (D * L)) _ ?_ hU0 hU1 hV0 hV1
  intro i hi j hj
  rw [bernTable_eq_intTable A Q hD.ne' hLz hL.ne' hQ i j]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hint i hi j hj) hDL.le

/-- **Box certificate (rational rectangle).**  The paper's actual shape: the
polynomial is positive on `[a₀,a₁] × [0,Y]` once the Bernstein table of its
affine pullback dominates a positive constant. -/
theorem cert_rectangle {nx ny : ℕ} {c : ℝ} (m : ℕ → ℕ → ℝ)
    (hc : 0 < c)
    (hb : ∀ i ∈ range (nx + 1), ∀ j ∈ range (ny + 1), c ≤ bernTable nx ny m i j)
    {a₀ a₁ Y a y : ℝ} (ha : a₀ < a₁) (hY : 0 < Y)
    (hain : a ∈ Set.Icc a₀ a₁) (hyin : y ∈ Set.Icc (0 : ℝ) Y) :
    0 < ∑ k ∈ range (nx + 1), ∑ l ∈ range (ny + 1),
          m k l * ((a - a₀) / (a₁ - a₀)) ^ k * (y / Y) ^ l := by
  obtain ⟨ha1, ha2⟩ := hain
  obtain ⟨hy1, hy2⟩ := hyin
  have hd : (0 : ℝ) < a₁ - a₀ := by linarith
  refine lt_of_lt_of_le hc (cert_unit_square m hb ?_ ?_ ?_ ?_)
  · exact div_nonneg (by linarith) hd.le
  · exact (div_le_one hd).mpr (by linarith)
  · exact div_nonneg hy1 hY.le
  · exact (div_le_one hY).mpr hy2

end Sendov911Bern
