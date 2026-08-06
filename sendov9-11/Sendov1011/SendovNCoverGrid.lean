import Mathlib
import Sendov911Capstone

set_option maxHeartbeats 1000000

/-!
# Assembly glue: the grid cover and `CoveringPositive` append

* `cover_grid` — a point of `[lo, lo + K·w]` lies in one of the `K` cells
  `[lo + i·w, lo + (i+1)·w]`.  Serves the 50-interval (deg 10) and 53-interval
  (deg 11) `a`-covers and the 10-way η-strip cover, all by instantiation.
* `coveringPositive_append` — the chunked-assembly glue the plan asked for
  (`Sendov911Capstone` ships only `nil`/`cons`; that file is left untouched).
-/

namespace SendovN.Cover

theorem cover_grid {w : ℝ} (hw : 0 < w) (lo : ℝ) :
    ∀ K : ℕ, 0 < K → ∀ a : ℝ, lo ≤ a → a ≤ lo + K * w →
      ∃ i : ℕ, i < K ∧ lo + i * w ≤ a ∧ a ≤ lo + (i + 1) * w := by
  intro K
  induction K with
  | zero => intro h; exact absurd h (by norm_num)
  | succ k ih =>
    intro _ a h0 h1
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      refine ⟨0, Nat.zero_lt_one, by simpa using h0, ?_⟩
      push_cast at h1 ⊢
      linarith
    · rcases le_or_gt a (lo + k * w) with hle | hgt
      · obtain ⟨i, hi, hia, hib⟩ := ih hk a h0 hle
        exact ⟨i, Nat.lt_succ_of_lt hi, hia, hib⟩
      · refine ⟨k, Nat.lt_succ_self k, hgt.le, ?_⟩
        push_cast at h1 ⊢
        linarith

theorem coveringPositive_append {l₁ l₂ : List Sendov911Capstone.Box}
    (h₁ : Sendov911Capstone.CoveringPositive l₁)
    (h₂ : Sendov911Capstone.CoveringPositive l₂) :
    Sendov911Capstone.CoveringPositive (l₁ ++ l₂) := by
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · exact h₁ b h
  · exact h₂ b h

end SendovN.Cover

#print axioms SendovN.Cover.cover_grid
#print axioms SendovN.Cover.coveringPositive_append
