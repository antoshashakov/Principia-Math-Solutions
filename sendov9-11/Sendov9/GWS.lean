import Mathlib
-- `Grace2Lib` is `Grace2` with its verbatim `Extract`/`Anchor2` copies replaced by an
-- `import Sendov9.Data`, so the GWS route and the counterexample data compose.
import Sendov9.Grace2Lib
import Sendov9.Apolarity2
import Sendov9.Walsh
import Sendov9.GWSCoeffs
import Sendov9.VietaProd
import Sendov9.VietaGen
import Sendov9.GWSFix

set_option maxHeartbeats 4000000

namespace Sendov9.GWS

open Polynomial Finset

/-!
# The Grace–Walsh–Szegő coincidence theorem, assembled

This closes the campaign's last carried hypothesis.  Every input is already gated:
Grace's apolarity theorem (`Grace2.grace_apolarity`, built on Laguerre), the two Vieta
translations (`VietaProd`, `VietaGen`), the coefficient/root identification
(`Apolarity2`), the integral expansion (`Walsh.integral_prod_eq`) and the apolar
construction (`GWSCoeffs.apolar_zero`).  What is added here is the bookkeeping that
joins them.

**The route.**  Write `F(u) = ∫₀¹ ∏ⱼ(1 - t uⱼ) dt` and `G(z) = ∫₀¹ (1 - t z)ⁿ dt`.  By
`Walsh.integral_prod_eq`, `F(u) = ∑ₘ cₘ eₘ(u)` and `G(z) = ∑ₘ cₘ C(n,m) zᵐ`, with
`cₘ = (-1)ᵐ/(m+1)`.  Let `b` be `c` with `b₀ := 1 - F(u)`, so that

    polyOf n b = G(·) - F(u).

`GWSCoeffs.apolar_zero` says `∑ₘ bₘ eₘ(u) = 0` **unconditionally** — the polynomial is
built to be apolar to `∏ⱼ(z - uⱼ)`.  Feed that through `Apolarity2.apolar_symm` and
`apolar_eq_pair` in both directions and the apolarity form against the *roots of*
`polyOf n b` is forced to vanish, after cancelling the nonzero leading coefficient.
Grace says a vanishing form is impossible when the roots stay strictly outside the disk
holding the `uⱼ`.  So some root `w` of `polyOf n b` satisfies `‖w‖ ≤ ρ < R`, and
`polyOf n b` vanishing at `w` is exactly `G(w) = F(u)`.

**The statement proved is `GWSFix.GraceWalshSzegoPos`, with the `0 < n` guard.**  The
unguarded `Master.GraceWalshSzego` is *false* (`GWSFix.not_graceWalshSzego`): at `n = 0`
its hypothesis is vacuous for negative `R`.  Nothing here targets that version.

Sendov's conjecture in degree nine is not proven by this file alone; it removes the last
classical input the campaign was carrying.
-/

/-- **Grace–Walsh–Szegő**, in the concrete integral form Lemma 2.1 consumes. -/
theorem graceWalshSzegoPos : GWSFix.GraceWalshSzegoPos := by
  intro n u R hn hu
  haveI hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- ρ = max‖uⱼ‖, the closed disk Grace needs the `uⱼ` to sit in
  set rho : ℝ := (univ : Finset (Fin n)).sup' Finset.univ_nonempty (fun j => ‖u j‖) with hrho
  have hrho_le : ∀ j, ‖u j‖ ≤ rho := fun j => Finset.le_sup' (fun j => ‖u j‖) (mem_univ j)
  have hrho_lt : rho < R := by
    rw [hrho, Finset.sup'_lt_iff]
    exact fun j _ => hu j
  have hrho0 : 0 ≤ rho := le_trans (norm_nonneg (u ⟨0, hn⟩)) (hrho_le ⟨0, hn⟩)
  -- the two `E`s that appear are the same function under different names
  have hEW : ∀ m : ℕ, Walsh.E u univ m = GWSCoeffs.E u univ m := fun _ => rfl
  -- `F(u)`, evaluated
  have hFint : (∫ t in (0:ℝ)..1, ∏ j, (1 - (t : ℂ) * u j)) = GWSCoeffs.Fval u univ n := by
    rw [Walsh.integral_prod_eq u n univ (by simp)]
    unfold GWSCoeffs.Fval GWSCoeffs.c
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hEW m]
    ring
  -- the top coefficient of `b` is `cₙ ≠ 0`
  have hbcn : GWSCoeffs.bcoeff u univ n n ≠ 0 := by
    unfold GWSCoeffs.bcoeff
    rw [if_neg (by omega : ¬ (n = 0))]
    unfold GWSCoeffs.c
    refine div_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    exact_mod_cast Nat.cast_add_one_ne_zero (R := ℂ) n
  set g : ℂ[X] := PolyOf.polyOf n (GWSCoeffs.bcoeff u univ n) with hg
  have hgdeg : g.natDegree = n := by rw [hg]; exact PolyOf.natDegree_eq hbcn
  have hgcard : Multiset.card g.roots = g.natDegree := LagGen.card_roots_eq g
  have hglc0 : g.leadingCoeff ≠ 0 := by
    rw [hg, Grace.leadingCoeff_polyOf hbcn]; exact hbcn
  have hgcoeff : ∀ j, j ≤ n → g.coeff j = ((n.choose j : ℂ)) * GWSCoeffs.bcoeff u univ n j := by
    intro j hj
    rw [hg, PolyOf.coeff_polyOf, if_pos (by simpa using Nat.lt_succ_of_le hj)]
  -- the `u`-side polynomial and its normalized coefficients
  have hchoose : ∀ k, k ≤ n → ((n.choose k : ℂ)) ≠ 0 := by
    intro k hk
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  set ac : ℕ → ℂ := fun k => (∏ j, (X - C (u j)) : ℂ[X]).coeff k / (n.choose k : ℂ) with hac
  have hacoeff : ∀ j, j ≤ n → (∏ i, (X - C (u i)) : ℂ[X]).coeff j = ((n.choose j : ℂ)) * ac j := by
    intro j hj
    -- `field_simp` must be *handed* the nonvanishing; without it the binomial
    -- coefficient is treated as possibly zero and `x = x * c / c` survives.
    have hc : ((n.choose j : ℂ)) ≠ 0 := hchoose j hj
    rw [hac]
    field_simp [hc]
  have hPdeg : (∏ j, (X - C (u j)) : ℂ[X]).natDegree = n := by
    rw [Polynomial.natDegree_prod _ _ (fun j _ => (Polynomial.monic_X_sub_C (u j)).ne_zero)]
    simp
  have hacn : ac n = 1 := by
    have h0 : (∏ j, (X - C (u j)) : ℂ[X]).coeff n = 1 := by
      have h := VietaProd.coeff_prod_X_sub u (Nat.zero_le n)
      rw [Nat.sub_zero] at h
      rw [h]
      have hE0 : VietaProd.E u univ 0 = 1 := by
        unfold VietaProd.E
        simp
      rw [hE0]
      norm_num
    rw [hac]
    simp only
    rw [h0, Nat.choose_self]
    norm_num
  have hPeq : PolyOf.polyOf n ac = ∏ j, (X - C (u j)) := by
    ext k
    rw [PolyOf.coeff_polyOf]
    by_cases hk : k ∈ range (n + 1)
    · rw [if_pos hk]
      exact (hacoeff k (Nat.lt_succ_iff.mp (mem_range.mp hk))).symm
    · rw [if_neg hk]
      symm
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      rw [hPdeg]
      simpa using hk
  have hProots : (∏ j, (X - C (u j)) : ℂ[X]).roots = (univ : Finset (Fin n)).val.map u := by
    rw [VietaProd.prod_as_multiset u]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  have hroots_le : ∀ r ∈ (PolyOf.polyOf n ac).roots, ‖r - (0:ℂ)‖ ≤ rho := by
    intro r hr
    rw [hPeq, hProots] at hr
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hr
    simpa using hrho_le j
  /- ### Grace forces a root into the disk -/
  have hexists : ∃ r ∈ g.roots, ‖r‖ ≤ rho := by
    by_contra hcon
    push_neg at hcon
    -- index the roots by `ℕ`, parking a far-away dummy outside `range n`
    set dmy : ℂ := ((rho + 1 : ℝ) : ℂ) with hdmy
    set w' : ℕ → ℂ := fun i => g.roots.toList.getD i dmy with hw'
    have hlen : g.roots.toList.length = n := by
      rw [Multiset.length_toList, hgcard, hgdeg]
    have hw'lt : ∀ i, ∀ h : i < n, w' i = g.roots.toList[i] := by
      intro i h
      rw [hw']
      exact List.getD_eq_getElem _ _ (by omega)
    have hw'mem : ∀ i, i < n → w' i ∈ g.roots := by
      intro i h
      rw [hw'lt i h]
      have : g.roots.toList[i] ∈ g.roots.toList := List.getElem_mem _
      rwa [← Multiset.mem_coe, Multiset.coe_toList] at this
    have hw'out : ∀ i, rho < ‖w' i - (0:ℂ)‖ := by
      intro i
      rw [sub_zero]
      by_cases h : i < n
      · exact hcon _ (hw'mem i h)
      · have : w' i = dmy := by
          rw [hw']
          exact List.getD_eq_default _ _ (by omega)
        rw [this, hdmy, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        linarith
    -- the roots, as a family over `range n`
    have hmap : (Finset.range n).val.map w' = g.roots := by
      have hlist : List.map w' (List.range n) = g.roots.toList := by
        refine List.ext_getElem (by simp [hlen]) ?_
        intro i h1' h2'
        simp only [List.getElem_map, List.getElem_range]
        exact hw'lt i (by simpa using h1')
      calc (Finset.range n).val.map w'
          = ((List.range n : List ℕ) : Multiset ℕ).map w' := rfl
        _ = ((List.map w' (List.range n) : List ℂ) : Multiset ℂ) := by rw [Multiset.map_coe]
        _ = ((g.roots.toList : List ℂ) : Multiset ℂ) := by rw [hlist]
        _ = g.roots := Multiset.coe_toList g.roots
    have hesymm : ∀ k, g.roots.esymm k = Apolarity.E w' (range n) k := by
      intro k
      rw [← hmap, VietaGen.esymm_eq_E_range w' n k]
      rfl
    -- Grace: the apolarity form cannot vanish
    have hgrace : Apolarity.pair n ac w' (range n) ≠ 0 :=
      Grace2.grace_apolarity w' hw'out n ac (by rw [hacn]; norm_num) hroots_le
    -- but it does, because the construction is apolar by design
    have hS1 : ∑ k ∈ range (n + 1),
          (-1 : ℂ) ^ k * (n.choose k : ℂ) * ac k * GWSCoeffs.bcoeff u univ n (n - k)
        = ∑ k ∈ range (n + 1), ac k * (g.leadingCoeff * g.roots.esymm k) := by
      refine Apolarity2.apolar_eq_pair ac (GWSCoeffs.bcoeff u univ n)
        (fun k => g.leadingCoeff * g.roots.esymm k) ?_
      intro k hk
      exact VietaGen.apolar_hypothesis_general hgdeg hgcard (GWSCoeffs.bcoeff u univ n)
        hgcoeff (Nat.lt_succ_iff.mp (mem_range.mp hk))
    have hS2 : ∑ k ∈ range (n + 1),
          (-1 : ℂ) ^ k * (n.choose k : ℂ) * GWSCoeffs.bcoeff u univ n k * ac (n - k)
        = ∑ k ∈ range (n + 1), GWSCoeffs.bcoeff u univ n k * GWSCoeffs.E u univ k := by
      refine Apolarity2.apolar_eq_pair (GWSCoeffs.bcoeff u univ n) ac
        (fun k => GWSCoeffs.E u univ k) ?_
      intro k hk
      exact VietaProd.apolar_hypothesis u ac hacoeff (Nat.lt_succ_iff.mp (mem_range.mp hk))
    have hSzero : ∑ k ∈ range (n + 1),
        (-1 : ℂ) ^ k * (n.choose k : ℂ) * ac k * GWSCoeffs.bcoeff u univ n (n - k) = 0 := by
      rw [Apolarity2.apolar_symm ac (GWSCoeffs.bcoeff u univ n), hS2,
        GWSCoeffs.apolar_zero u univ n, mul_zero]
    have hpair : g.leadingCoeff * Apolarity.pair n ac w' (range n) = 0 := by
      rw [← hSzero, hS1]
      unfold Apolarity.pair
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hesymm k]
      ring
    exact hgrace ((mul_eq_zero.mp hpair).resolve_left hglc0)
  /- ### The root is the coincidence point -/
  obtain ⟨r, hr, hrle⟩ := hexists
  refine ⟨r, lt_of_le_of_lt hrle hrho_lt, ?_⟩
  -- `G(r)`, evaluated
  have hEconst : ∀ m : ℕ, Walsh.E (fun _ : Fin n => r) univ m = (n.choose m : ℂ) * r ^ m := by
    intro m
    unfold Walsh.E
    have h1 : ∀ A ∈ (univ : Finset (Fin n)).powersetCard m, (∏ _k ∈ A, r) = r ^ m := by
      intro A hA
      rw [Finset.prod_const, (Finset.mem_powersetCard.mp hA).2]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hGint : (∫ t in (0:ℝ)..1, (1 - (t : ℂ) * r) ^ n)
      = ∑ m ∈ range (n + 1), (n.choose m : ℂ) * GWSCoeffs.c m * r ^ m := by
    have hprod : ∀ t : ℝ, (∏ _j : Fin n, (1 - (t : ℂ) * r)) = (1 - (t : ℂ) * r) ^ n := by
      intro t
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc (∫ t in (0:ℝ)..1, (1 - (t : ℂ) * r) ^ n)
        = ∫ t in (0:ℝ)..1, ∏ j : Fin n, (1 - (t : ℂ) * (fun _ : Fin n => r) j) := by
          simp only [hprod]
      _ = ∑ m ∈ range (n + 1), (-1 : ℂ) ^ m * Walsh.E (fun _ : Fin n => r) univ m
            / ((m : ℂ) + 1) := Walsh.integral_prod_eq _ n univ (by simp)
      _ = ∑ m ∈ range (n + 1), (n.choose m : ℂ) * GWSCoeffs.c m * r ^ m := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hEconst m]
          unfold GWSCoeffs.c
          ring
  -- `polyOf n b` vanishes at `r`, i.e. `G(r) - F(u) = 0`
  have hgeval : g.eval r = 0 := Polynomial.isRoot_of_mem_roots hr
  rw [hg, PolyOf.eval_polyOf] at hgeval
  have hsplit : ∑ k ∈ range (n + 1),
        (n.choose k : ℂ) * GWSCoeffs.bcoeff u univ n k * r ^ k
      = (∑ k ∈ range (n + 1), (n.choose k : ℂ) * GWSCoeffs.c k * r ^ k)
        - GWSCoeffs.Fval u univ n := by
    rw [Finset.sum_range_succ' (fun k => (n.choose k : ℂ) * GWSCoeffs.bcoeff u univ n k * r ^ k) n,
      Finset.sum_range_succ' (fun k => (n.choose k : ℂ) * GWSCoeffs.c k * r ^ k) n]
    have htail : ∀ m ∈ range n,
        (n.choose (m + 1) : ℂ) * GWSCoeffs.bcoeff u univ n (m + 1) * r ^ (m + 1)
          = (n.choose (m + 1) : ℂ) * GWSCoeffs.c (m + 1) * r ^ (m + 1) := by
      intro m _
      unfold GWSCoeffs.bcoeff
      simp
    rw [Finset.sum_congr rfl htail]
    have hb0 : (n.choose 0 : ℂ) * GWSCoeffs.bcoeff u univ n 0 * r ^ 0
        = 1 - GWSCoeffs.Fval u univ n := by
      unfold GWSCoeffs.bcoeff
      simp
    have hc0 : (n.choose 0 : ℂ) * GWSCoeffs.c 0 * r ^ 0 = 1 := by
      simp [GWSCoeffs.c]
    rw [hb0, hc0]
    ring
  rw [hsplit] at hgeval
  rw [hFint, hGint]
  linear_combination -hgeval

end Sendov9.GWS

#print axioms Sendov9.GWS.graceWalshSzegoPos
