import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.VietaGen

open Polynomial Finset

/-!
# Stage fifteen: Vieta for the *second* polynomial

`VietaProd` handled the monic product `∏ⱼ(X - uⱼ)`, where the leading coefficient is
`1` and drops out.  The other polynomial the GWS assembly feeds to
`Apolarity2.apolar_eq_pair` is `G(z) - F(u)`, whose leading coefficient is
`bₙ = (-1)ⁿ/(n+1)` — nonzero, but not `1`, so the scalar survives and has to be carried
through and cancelled at the end.

`coeff_eq_esymm` is that statement: `g.coeff (n-k) = leadingCoeff · (-1)ᵏ · eₖ(roots)`.
It is `Polynomial.coeff_eq_esymm_roots_of_card` with the index reflected, and the
reflection is where `k ≤ n` is needed — `n - (n - k) = k` fails without it.

`esymm_eq_E_range` is the companion translation for a family indexed by `ℕ` over
`range n`, which is the shape `Apolarity.pair` uses (`VietaProd.esymm_eq_E` did the
`Fin n`/`univ` case).  Both are `Finset.esymm_map_val`, and both close by `rfl` once
the `powersetCard` sums are recognised as the same object.

With these two the assembly has both Vieta inputs; what is left is the `F(u)`
computation and the contradiction.  Sendov's conjecture in degree nine remains
unproven.
-/

/-- `eₘ`, as in `Apolarity.lean`, for an `ℕ`-indexed family. -/
noncomputable def E (x : ℕ → ℂ) (s : Finset ℕ) (m : ℕ) : ℂ :=
  ∑ A ∈ s.powersetCard m, ∏ k ∈ A, x k

/-- **Vieta with a general leading coefficient.**  The index reflection needs `k ≤ n`. -/
theorem coeff_eq_esymm {g : ℂ[X]} {n : ℕ} (hdeg : g.natDegree = n)
    (hcard : Multiset.card g.roots = g.natDegree) {k : ℕ} (hk : k ≤ n) :
    g.coeff (n - k) = g.leadingCoeff * (-1) ^ k * g.roots.esymm k := by
  have hle : n - k ≤ g.natDegree := by omega
  have hv := Polynomial.coeff_eq_esymm_roots_of_card hcard hle
  have hsub : g.natDegree - (n - k) = k := by omega
  rw [hsub] at hv
  exact hv

/-- The `ℕ`-indexed companion of `VietaProd.esymm_eq_E`. -/
theorem esymm_eq_E_range (w : ℕ → ℂ) (n k : ℕ) :
    (((range n) : Finset ℕ).val.map w).esymm k = E w (range n) k := by
  rw [Finset.esymm_map_val]
  rfl

/-- **The shape `Apolarity2.apolar_eq_pair` consumes, with the scalar carried.**

For `g` of degree `n` written in the normalized basis as `∑ₖ C(n,k)·bₖ·Xᵏ`,

    C(n,n-k)·b₍ₙ₋ₖ₎ = (-1)ᵏ · (leadingCoeff · eₖ(roots))

so `apolar_eq_pair` applies with `e k := leadingCoeff · eₖ(roots)`, and the resulting
pairing is `leadingCoeff` times the one Grace speaks about.  Since the leading
coefficient is nonzero the two vanish together, which is all the assembly needs. -/
theorem apolar_hypothesis_general {g : ℂ[X]} {n : ℕ} (hdeg : g.natDegree = n)
    (hcard : Multiset.card g.roots = g.natDegree) (b : ℕ → ℂ)
    (hcoeff : ∀ j, j ≤ n → g.coeff j = ((n.choose j : ℂ)) * b j)
    {k : ℕ} (hk : k ≤ n) :
    ((n.choose (n - k) : ℂ)) * b (n - k)
      = (-1) ^ k * (g.leadingCoeff * g.roots.esymm k) := by
  rw [← hcoeff (n - k) (by omega), coeff_eq_esymm hdeg hcard hk]
  ring

end Sendov9.VietaGen

#print axioms Sendov9.VietaGen.coeff_eq_esymm
#print axioms Sendov9.VietaGen.esymm_eq_E_range
#print axioms Sendov9.VietaGen.apolar_hypothesis_general
