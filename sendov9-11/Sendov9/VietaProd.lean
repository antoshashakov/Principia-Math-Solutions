import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.VietaProd

open Polynomial Finset

/-!
# Stage fourteen: Vieta for `∏ⱼ(X - uⱼ)`, in the shape `apolar_eq_pair` wants

The GWS assembly feeds two polynomials to `Apolarity2.apolar_eq_pair`, and each needs
its coefficients expressed through the elementary symmetric functions of its roots.
For the polynomial whose roots are the `uⱼ` — the one Grace requires to have its roots
in the disk — that is Vieta for a monic product, and this file puts it in exactly the
form the hypothesis `C(n,n-k)·b₍ₙ₋ₖ₎ = (-1)ᵏ eₖ` asks for.

Mathlib has the multiset version (`Multiset.prod_X_sub_C_coeff`); what is missing is
the translation between `Multiset.esymm` on `univ.val.map u` and the `E u univ k` the
rest of the campaign is written against.  `esymm_eq_E` is that translation, and it is
`Finset.esymm_map_val` — which already says exactly this, once the two `powersetCard`
sums are seen to be the same object.

Sendov's conjecture in degree nine remains unproven.
-/

variable {n : ℕ}

/-- `eₘ`, as everywhere else in the campaign. -/
noncomputable def E (x : Fin n → ℂ) (s : Finset (Fin n)) (m : ℕ) : ℂ :=
  ∑ A ∈ s.powersetCard m, ∏ k ∈ A, x k

/-- `Multiset.esymm` of the mapped underlying multiset is the campaign's `E`. -/
theorem esymm_eq_E (u : Fin n → ℂ) (k : ℕ) :
    ((univ : Finset (Fin n)).val.map u).esymm k = E u univ k := by
  rw [Finset.esymm_map_val]
  rfl

theorem card_map_univ (u : Fin n → ℂ) :
    Multiset.card ((univ : Finset (Fin n)).val.map u) = n := by
  rw [Multiset.card_map]
  simp

/-- The monic product, as a multiset product. -/
theorem prod_as_multiset (u : Fin n → ℂ) :
    ∏ j, (X - C (u j)) = (((univ : Finset (Fin n)).val.map u).map fun t => X - C t).prod := by
  rw [Multiset.map_map]
  rw [Finset.prod_eq_multiset_prod]
  rfl

/-- **Vieta for `∏ⱼ(X - uⱼ)`.**  `coeff (n-k) = (-1)ᵏ eₖ(u)`. -/
theorem coeff_prod_X_sub (u : Fin n → ℂ) {k : ℕ} (hk : k ≤ n) :
    (∏ j, (X - C (u j))).coeff (n - k) = (-1) ^ k * E u univ k := by
  have hcard := card_map_univ u
  have hle : n - k ≤ Multiset.card ((univ : Finset (Fin n)).val.map u) := by
    rw [hcard]; omega
  have hv := Multiset.prod_X_sub_C_coeff ((univ : Finset (Fin n)).val.map u) hle
  rw [hcard] at hv
  have hsub : n - (n - k) = k := by omega
  rw [hsub] at hv
  rw [prod_as_multiset u, hv, esymm_eq_E]

/-- **The shape `Apolarity2.apolar_eq_pair` consumes.**

If `f = ∏ⱼ(X - uⱼ)` is written in the normalized basis as `∑ₖ C(n,k)·aₖ·Xᵏ`, then
`C(n,n-k)·a₍ₙ₋ₖ₎ = (-1)ᵏ eₖ(u)` — which is precisely `apolar_eq_pair`'s hypothesis,
with the monic leading coefficient making the scalar factor `1`. -/
theorem apolar_hypothesis (u : Fin n → ℂ) (a : ℕ → ℂ)
    (hcoeff : ∀ j ≤ n, (∏ i, (X - C (u i))).coeff j = ((n.choose j : ℂ)) * a j)
    {k : ℕ} (hk : k ≤ n) :
    ((n.choose (n - k) : ℂ)) * a (n - k) = (-1) ^ k * E u univ k := by
  rw [← hcoeff (n - k) (by omega)]
  exact coeff_prod_X_sub u hk

end Sendov9.VietaProd

#print axioms Sendov9.VietaProd.esymm_eq_E
#print axioms Sendov9.VietaProd.card_map_univ
#print axioms Sendov9.VietaProd.prod_as_multiset
#print axioms Sendov9.VietaProd.coeff_prod_X_sub
#print axioms Sendov9.VietaProd.apolar_hypothesis
