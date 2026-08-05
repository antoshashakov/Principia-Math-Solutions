import Mathlib

set_option maxHeartbeats 400000

namespace Sendov9.Cover

/-!
# The middle range is actually covered

`Assembly.middle_increasing` checks that Table 1's nineteen endpoints are strictly
increasing, and `Assembly.middle_tiling` checks the first and last and the count.
Neither says the thing that actually matters: **every real `a ∈ [9/20, 9/10]` lies in
one of the eighteen intervals.**  Ordered endpoints plus the right count do not imply
coverage of the reals between them — that is the step where a transcription slip in
Table 1 would produce a gap which every individual certificate still passes, because
each certificate only ever speaks about its own interval.

`mid_cover` is that statement, and `mid_excluded_of_rows` is the reduction the master
wants: eighteen per-row exclusions give the whole middle range.

Neither ancillary Python verifier checks either one.
-/

/-- **The eighteen intervals cover `[9/20, 9/10]`.** -/
theorem mid_cover (a : ℝ) (h0 : (9/20 : ℝ) ≤ a) (h1 : a ≤ (9/10 : ℝ)) :
    ((9/20 : ℝ) ≤ a ∧ a ≤ 19/40) ∨
    ((19/40 : ℝ) ≤ a ∧ a ≤ 1/2) ∨
    ((1/2 : ℝ) ≤ a ∧ a ≤ 21/40) ∨
    ((21/40 : ℝ) ≤ a ∧ a ≤ 11/20) ∨
    ((11/20 : ℝ) ≤ a ∧ a ≤ 23/40) ∨
    ((23/40 : ℝ) ≤ a ∧ a ≤ 3/5) ∨
    ((3/5 : ℝ) ≤ a ∧ a ≤ 5/8) ∨
    ((5/8 : ℝ) ≤ a ∧ a ≤ 13/20) ∨
    ((13/20 : ℝ) ≤ a ∧ a ≤ 27/40) ∨
    ((27/40 : ℝ) ≤ a ∧ a ≤ 7/10) ∨
    ((7/10 : ℝ) ≤ a ∧ a ≤ 29/40) ∨
    ((29/40 : ℝ) ≤ a ∧ a ≤ 3/4) ∨
    ((3/4 : ℝ) ≤ a ∧ a ≤ 31/40) ∨
    ((31/40 : ℝ) ≤ a ∧ a ≤ 4/5) ∨
    ((4/5 : ℝ) ≤ a ∧ a ≤ 33/40) ∨
    ((33/40 : ℝ) ≤ a ∧ a ≤ 17/20) ∨
    ((17/20 : ℝ) ≤ a ∧ a ≤ 7/8) ∨
    ((7/8 : ℝ) ≤ a ∧ a ≤ 9/10) := by
  rcases le_total a ((19/40 : ℝ)) with k0 | k0
  · exact Or.inl (⟨h0, k0⟩)
  rcases le_total a ((1/2 : ℝ)) with k1 | k1
  · exact Or.inr (Or.inl (⟨k0, k1⟩))
  rcases le_total a ((21/40 : ℝ)) with k2 | k2
  · exact Or.inr (Or.inr (Or.inl (⟨k1, k2⟩)))
  rcases le_total a ((11/20 : ℝ)) with k3 | k3
  · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨k2, k3⟩))))
  rcases le_total a ((23/40 : ℝ)) with k4 | k4
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨k3, k4⟩)))))
  rcases le_total a ((3/5 : ℝ)) with k5 | k5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨k4, k5⟩))))))
  rcases le_total a ((5/8 : ℝ)) with k6 | k6
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨k5, k6⟩)))))))
  rcases le_total a ((13/20 : ℝ)) with k7 | k7
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨k6, k7⟩))))))))
  rcases le_total a ((27/40 : ℝ)) with k8 | k8
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨k7, k8⟩)))))))))
  rcases le_total a ((7/10 : ℝ)) with k9 | k9
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨k8, k9⟩))))))))))
  rcases le_total a ((29/40 : ℝ)) with k10 | k10
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨k9, k10⟩)))))))))))
  rcases le_total a ((3/4 : ℝ)) with k11 | k11
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨k10, k11⟩))))))))))))
  rcases le_total a ((31/40 : ℝ)) with k12 | k12
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨k11, k12⟩)))))))))))))
  rcases le_total a ((4/5 : ℝ)) with k13 | k13
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨k12, k13⟩))))))))))))))
  rcases le_total a ((33/40 : ℝ)) with k14 | k14
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨k13, k14⟩)))))))))))))))
  rcases le_total a ((17/20 : ℝ)) with k15 | k15
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨k14, k15⟩))))))))))))))))
  rcases le_total a ((7/8 : ℝ)) with k16 | k16
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨k15, k16⟩)))))))))))))))))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨k16, h1⟩)))))))))))))))))

/-- **Reduction to the rows.**  If each of the eighteen intervals is excluded, the
whole middle range is. -/
theorem mid_excluded_of_rows
    (r1 : ∀ a : ℝ, (9/20 : ℝ) ≤ a → a ≤ 19/40 → False)
    (r2 : ∀ a : ℝ, (19/40 : ℝ) ≤ a → a ≤ 1/2 → False)
    (r3 : ∀ a : ℝ, (1/2 : ℝ) ≤ a → a ≤ 21/40 → False)
    (r4 : ∀ a : ℝ, (21/40 : ℝ) ≤ a → a ≤ 11/20 → False)
    (r5 : ∀ a : ℝ, (11/20 : ℝ) ≤ a → a ≤ 23/40 → False)
    (r6 : ∀ a : ℝ, (23/40 : ℝ) ≤ a → a ≤ 3/5 → False)
    (r7 : ∀ a : ℝ, (3/5 : ℝ) ≤ a → a ≤ 5/8 → False)
    (r8 : ∀ a : ℝ, (5/8 : ℝ) ≤ a → a ≤ 13/20 → False)
    (r9 : ∀ a : ℝ, (13/20 : ℝ) ≤ a → a ≤ 27/40 → False)
    (r10 : ∀ a : ℝ, (27/40 : ℝ) ≤ a → a ≤ 7/10 → False)
    (r11 : ∀ a : ℝ, (7/10 : ℝ) ≤ a → a ≤ 29/40 → False)
    (r12 : ∀ a : ℝ, (29/40 : ℝ) ≤ a → a ≤ 3/4 → False)
    (r13 : ∀ a : ℝ, (3/4 : ℝ) ≤ a → a ≤ 31/40 → False)
    (r14 : ∀ a : ℝ, (31/40 : ℝ) ≤ a → a ≤ 4/5 → False)
    (r15 : ∀ a : ℝ, (4/5 : ℝ) ≤ a → a ≤ 33/40 → False)
    (r16 : ∀ a : ℝ, (33/40 : ℝ) ≤ a → a ≤ 17/20 → False)
    (r17 : ∀ a : ℝ, (17/20 : ℝ) ≤ a → a ≤ 7/8 → False)
    (r18 : ∀ a : ℝ, (7/8 : ℝ) ≤ a → a ≤ 9/10 → False)
    (a : ℝ) (h0 : (9/20 : ℝ) ≤ a) (h1 : a ≤ (9/10 : ℝ)) : False := by
  rcases mid_cover a h0 h1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact r1 a h.1 h.2
  · exact r2 a h.1 h.2
  · exact r3 a h.1 h.2
  · exact r4 a h.1 h.2
  · exact r5 a h.1 h.2
  · exact r6 a h.1 h.2
  · exact r7 a h.1 h.2
  · exact r8 a h.1 h.2
  · exact r9 a h.1 h.2
  · exact r10 a h.1 h.2
  · exact r11 a h.1 h.2
  · exact r12 a h.1 h.2
  · exact r13 a h.1 h.2
  · exact r14 a h.1 h.2
  · exact r15 a h.1 h.2
  · exact r16 a h.1 h.2
  · exact r17 a h.1 h.2
  · exact r18 a h.1 h.2

end Sendov9.Cover

#print axioms Sendov9.Cover.mid_cover
#print axioms Sendov9.Cover.mid_excluded_of_rows
