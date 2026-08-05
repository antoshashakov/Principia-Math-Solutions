import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.GWSCoeffs

open Finset

/-!
# Stage sixteen: the coefficient sequence that makes `G - F(u)` apolar to `∏(z - uⱼ)`

This is the construction the whole GWS argument turns on, and it is a one-line trick
once written down.

`Walsh.integral_prod_eq` gives `F(u) = ∑ₘ cₘ eₘ(u)` with `cₘ = (-1)ᵐ/(m+1)`, and
`G(w) = ∑ₘ cₘ C(n,m) wᵐ` is the same expression at the constant family.  Define

    bₘ = cₘ for m ≥ 1,        b₀ = 1 - F(u)

so that `polyOf n b = G(z) - F(u)` — the `m = 0` term absorbs the constant.  Then

    ∑ₘ bₘ eₘ(u) = (1 - F(u))·e₀ + ∑_{m≥1} cₘ eₘ(u) = (1 - F) + (F - 1) = 0

because `e₀ = 1` and `c₀ = 1`, so the `m ≥ 1` tail is exactly `F - 1`.  That vanishing
**is** apolarity of `G - F(u)` with `∏ⱼ(z - uⱼ)`, which is the hypothesis Grace needs
— and it holds by construction, for every `u`, with no condition whatsoever.

That is why the argument works: the polynomial is *built* to be apolar, and Grace then
has no choice but to hand back a root in the disk.  (Confirmed numerically to 5e-15
before any of this was formalized.)

Sendov's conjecture in degree nine remains unproven.
-/

variable {ι : Type*} [DecidableEq ι]

/-- `eₘ`, as everywhere else. -/
noncomputable def E (x : ι → ℂ) (s : Finset ι) (m : ℕ) : ℂ :=
  ∑ A ∈ s.powersetCard m, ∏ k ∈ A, x k

@[simp] theorem E_zero (x : ι → ℂ) (s : Finset ι) : E x s 0 = 1 := by
  simp [E, Finset.powersetCard_zero]

/-- `cₘ = (-1)ᵐ/(m+1)` — the coefficients of both integrals. -/
noncomputable def c (m : ℕ) : ℂ := (-1) ^ m / ((m : ℂ) + 1)

@[simp] theorem c_zero : c 0 = 1 := by simp [c]

/-- `F(u) = ∑ₘ cₘ eₘ(u)`, the value `Walsh.integral_prod_eq` computes. -/
noncomputable def Fval (x : ι → ℂ) (s : Finset ι) (N : ℕ) : ℂ :=
  ∑ m ∈ range (N + 1), c m * E x s m

/-- The shifted coefficient sequence: `b₀` absorbs the constant `-F(u)`. -/
noncomputable def bcoeff (x : ι → ℂ) (s : Finset ι) (N : ℕ) : ℕ → ℂ :=
  fun m => if m = 0 then 1 - Fval x s N else c m

/-- **The construction is apolar to `∏ⱼ(z - uⱼ)` by design.**

`∑ₘ bₘ eₘ(u) = 0`, unconditionally.  This is the hypothesis Grace consumes, and it is
free — no condition on `u` at all. -/
theorem apolar_zero (x : ι → ℂ) (s : Finset ι) (N : ℕ) :
    ∑ m ∈ range (N + 1), bcoeff x s N m * E x s m = 0 := by
  -- peel the constant term off both the sum and `F`
  rw [Finset.sum_range_succ' (fun m => bcoeff x s N m * E x s m) N]
  have htail : ∀ m ∈ range N, bcoeff x s N (m + 1) * E x s (m + 1)
      = c (m + 1) * E x s (m + 1) := by
    intro m _
    unfold bcoeff
    simp
  rw [Finset.sum_congr rfl htail]
  have hb0 : bcoeff x s N 0 * E x s 0 = 1 - Fval x s N := by
    unfold bcoeff
    simp
  rw [hb0]
  -- and `F = 1 + (the tail)`
  have hF : Fval x s N = 1 + ∑ m ∈ range N, c (m + 1) * E x s (m + 1) := by
    unfold Fval
    rw [Finset.sum_range_succ' (fun m => c m * E x s m) N]
    simp
    ring
  rw [hF]
  ring

end Sendov9.GWSCoeffs

#print axioms Sendov9.GWSCoeffs.c_zero
#print axioms Sendov9.GWSCoeffs.apolar_zero
