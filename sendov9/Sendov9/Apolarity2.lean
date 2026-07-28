import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.Apolarity2

open Finset

/-!
# Stage five: the apolarity form in coefficients equals the apolarity form in roots

Two descriptions of apolarity are in play, and Grace needs them identified.

*Coefficients.*  For `f = ∑ₖ C(n,k) aₖ zᵏ` and `g = ∑ₖ C(n,k) bₖ zᵏ`, apolarity is

    ∑ₖ (-1)ᵏ C(n,k) aₖ b_{n-k} = 0.

*Roots.*  `Apolarity.pair` computes `∑ₖ aₖ eₖ(w)`, and `pair_insert` shows that is
exactly what the iterated polar derivative leaves behind.

`apolar_eq_pair` identifies the two.  It is a **termwise** identity, not a
rearrangement: if `g` is monic with roots `w`, then its normalized coefficients satisfy
`C(n,n-k)·b_{n-k} = (-1)ᵏ eₖ(w)`, so each summand collapses

    (-1)ᵏ C(n,k) aₖ b_{n-k} = (-1)ᵏ aₖ · (C(n,n-k) b_{n-k}) = (-1)ᵏ aₖ (-1)ᵏ eₖ(w) = aₖ eₖ(w)

using `C(n,k) = C(n,n-k)` and `(-1)ᵏ(-1)ᵏ = 1`.  The binomial coefficients cancel
without ever being divided by, which is what keeps this clean.

`apolar_symm` records that apolarity is a symmetric relation up to `(-1)ⁿ` — the fact
that lets Grace be applied in either direction, which is how the coincidence theorem
uses it (there one wants a root of `P` given that the *other* polynomial's roots are in
the disk).

**Scope.**  With this, Grace's algebraic side is complete: coefficient apolarity ⇒ root
apolarity ⇒ (by `pair_insert`, iterated) the constant the polar derivatives leave.
What remains is the analytic iteration on top of `Laguerre3`, then Walsh.  Sendov's
conjecture in degree nine remains unproven.
-/

/-- **Coefficient apolarity equals root apolarity.**  Termwise; the binomial
coefficients cancel by `C(n,k) = C(n,n-k)` without any division. -/
theorem apolar_eq_pair {n : ℕ} (a b e : ℕ → ℂ)
    (hb : ∀ k ∈ range (n + 1), (Nat.choose n (n - k) : ℂ) * b (n - k) = (-1) ^ k * e k) :
    ∑ k ∈ range (n + 1), (-1) ^ k * (Nat.choose n k : ℂ) * a k * b (n - k)
      = ∑ k ∈ range (n + 1), a k * e k := by
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsym : (Nat.choose n k : ℂ) = (Nat.choose n (n - k) : ℂ) := by
    rw [Nat.choose_symm hkn]
  have hsq : ((-1 : ℂ)) ^ k * (-1) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  calc (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * a k * b (n - k)
      = (-1) ^ k * a k * ((Nat.choose n (n - k) : ℂ) * b (n - k)) := by
        rw [hsym]; ring
    _ = (-1) ^ k * a k * ((-1) ^ k * e k) := by rw [hb k hk]
    _ = ((-1 : ℂ) ^ k * (-1) ^ k) * (a k * e k) := by ring
    _ = a k * e k := by rw [hsq]; ring

/-- **Apolarity is symmetric up to `(-1)ⁿ`.**  Reindex `k ↦ n - k`. -/
theorem apolar_symm {n : ℕ} (a b : ℕ → ℂ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * (Nat.choose n k : ℂ) * a k * b (n - k)
      = (-1) ^ n * ∑ k ∈ range (n + 1), (-1) ^ k * (Nat.choose n k : ℂ) * b k * a (n - k) := by
  rw [Finset.mul_sum]
  rw [← Finset.sum_range_reflect
    (fun k => (-1 : ℂ) ^ n * ((-1) ^ k * (Nat.choose n k : ℂ) * b k * a (n - k))) (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hidx : n + 1 - 1 - k = n - k := by omega
  have hback : n - (n - k) = k := by omega
  rw [hidx, hback]
  have hsym : (Nat.choose n (n - k) : ℂ) = (Nat.choose n k : ℂ) := by
    rw [Nat.choose_symm hkn]
  rw [hsym]
  -- `(-1)ⁿ (-1)^{n-k} = (-1)^k`, since `(n - k) + k = n`
  have hpow : ((-1 : ℂ)) ^ n * (-1) ^ (n - k) = (-1) ^ k := by
    have hnk : n - k + k = n := by omega
    calc ((-1 : ℂ)) ^ n * (-1) ^ (n - k)
        = (-1) ^ (n - k + k) * (-1) ^ (n - k) := by rw [hnk]
      _ = ((-1 : ℂ) ^ (n - k) * (-1) ^ (n - k)) * (-1) ^ k := by rw [pow_add]; ring
      _ = (-1) ^ k := by
          rw [← mul_pow]
          norm_num
  calc (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * a k * b (n - k)
      = ((-1 : ℂ) ^ n * (-1) ^ (n - k)) * (Nat.choose n k : ℂ) * a k * b (n - k) := by
        rw [hpow]
    _ = (-1 : ℂ) ^ n * ((-1) ^ (n - k) * (Nat.choose n k : ℂ) * b (n - k) * a k) := by ring

end Sendov9.Apolarity2

#print axioms Sendov9.Apolarity2.apolar_eq_pair
#print axioms Sendov9.Apolarity2.apolar_symm
