import Mathlib

namespace Erdos123Band

open Finset

/-- Two-sided quartic comparison of `cos` with the Gaussian: both have Taylor
    polynomial `1 - u²/2`, and Mathlib bounds the quartic error of each. -/
theorem cos_sub_exp_le {u : ℝ} (hu : |u| ≤ 1) :
    |Real.cos u - Real.exp (-(u ^ 2 / 2))| ≤ u ^ 4 := by
  have hu2 : u ^ 2 ≤ 1 := by
    have := abs_nonneg u
    nlinarith [sq_abs u]
  have hx : |(-(u ^ 2 / 2) : ℝ)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ u ^ 2 / 2)]
    linarith
  have h1 : |Real.cos u - (1 - u ^ 2 / 2)| ≤ |u| ^ 4 * (5 / 96) := Real.cos_bound hu
  have h2 : |Real.exp (-(u ^ 2 / 2)) - 1 - (-(u ^ 2 / 2))| ≤ (-(u ^ 2 / 2)) ^ 2 :=
    Real.abs_exp_sub_one_sub_id_le hx
  have h2' : |(1 - u ^ 2 / 2) - Real.exp (-(u ^ 2 / 2))| ≤ u ^ 4 / 4 := by
    have hrw : (1 - u ^ 2 / 2) - Real.exp (-(u ^ 2 / 2))
        = -(Real.exp (-(u ^ 2 / 2)) - 1 - (-(u ^ 2 / 2))) := by ring
    rw [hrw, abs_neg]
    calc |Real.exp (-(u ^ 2 / 2)) - 1 - (-(u ^ 2 / 2))| ≤ (-(u ^ 2 / 2)) ^ 2 := h2
      _ = u ^ 4 / 4 := by ring
  have habs : |u| ^ 4 = u ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ u ^ 4)]
  have htri : |Real.cos u - Real.exp (-(u ^ 2 / 2))|
      ≤ |Real.cos u - (1 - u ^ 2 / 2)| + |(1 - u ^ 2 / 2) - Real.exp (-(u ^ 2 / 2))| := by
    have : Real.cos u - Real.exp (-(u ^ 2 / 2))
        = (Real.cos u - (1 - u ^ 2 / 2)) + ((1 - u ^ 2 / 2) - Real.exp (-(u ^ 2 / 2))) := by ring
    rw [this]
    exact abs_add_le _ _
  have h4 : (0:ℝ) ≤ u ^ 4 := by positivity
  rw [habs] at h1
  linarith

/-- Telescoping product perturbation for factors bounded by 1. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      have hf' : ∀ i ∈ t, |f i| ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hg' : ∀ i ∈ t, |g i| ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hfa : |f a| ≤ 1 := hf a (Finset.mem_insert_self a t)
      have hIH := ih hf' hg'
      have hQ : |∏ i ∈ t, g i| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun i _ => abs_nonneg _) hg'
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      set P := ∏ i ∈ t, f i with hP
      set Q := ∏ i ∈ t, g i with hQdef
      have key : f a * P - g a * Q = f a * (P - Q) + (f a - g a) * Q := by ring
      calc |f a * P - g a * Q| = |f a * (P - Q) + (f a - g a) * Q| := by rw [key]
        _ ≤ |f a * (P - Q)| + |(f a - g a) * Q| := abs_add_le _ _
        _ = |f a| * |P - Q| + |f a - g a| * |Q| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * |P - Q| + |f a - g a| * 1 := by
              have h1 : |f a| * |P - Q| ≤ 1 * |P - Q| :=
                mul_le_mul_of_nonneg_right hfa (abs_nonneg _)
              have h2 : |f a - g a| * |Q| ≤ |f a - g a| * 1 :=
                mul_le_mul_of_nonneg_left hQ (abs_nonneg _)
              linarith
        _ = |P - Q| + |f a - g a| := by ring
        _ ≤ (∑ i ∈ t, |f i - g i|) + |f a - g a| := by linarith
        _ = |f a - g a| + ∑ i ∈ t, |f i - g i| := by ring

/-- **The principal-range kernel estimate.**  If every `|c i| ≤ 1` then the product of
    cosines is the Gaussian of the summed squares, up to the sum of fourth powers. -/
theorem abs_prod_cos_sub_exp_le {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, |c i| ≤ 1) :
    |(∏ i ∈ s, Real.cos (c i)) - Real.exp (-((∑ i ∈ s, c i ^ 2) / 2))|
      ≤ ∑ i ∈ s, c i ^ 4 := by
  have hexp : Real.exp (-((∑ i ∈ s, c i ^ 2) / 2)) = ∏ i ∈ s, Real.exp (-(c i ^ 2 / 2)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  rw [hexp]
  have hf : ∀ i ∈ s, |Real.cos (c i)| ≤ 1 := fun i _ => Real.abs_cos_le_one _
  have hg : ∀ i ∈ s, |Real.exp (-(c i ^ 2 / 2))| ≤ 1 := by
    intro i _
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (c i)])
  calc |(∏ i ∈ s, Real.cos (c i)) - ∏ i ∈ s, Real.exp (-(c i ^ 2 / 2))|
      ≤ ∑ i ∈ s, |Real.cos (c i) - Real.exp (-(c i ^ 2 / 2))| :=
        abs_prod_sub_prod_le s _ _ hf hg
    _ ≤ ∑ i ∈ s, c i ^ 4 :=
        Finset.sum_le_sum (fun i hi => cos_sub_exp_le (hc i hi))

end Erdos123Band
