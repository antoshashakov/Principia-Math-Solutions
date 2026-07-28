import Mathlib

set_option maxHeartbeats 4000000

namespace Sendov9.Mid

/-!
# Table 1's side conditions, machine-checked (all 18 rows)

Proposition 4.1 requires, on each interval `[α,β]` with constants `S, λ, Y`:

    σ ≤ S,   L_S(a) ≥ λ,   Y² ≥ 1-λ²,   2λ ≥ β,   0 ≤ (S/4-1)(1-α²) ≤ 1.

`L_S(a) ≥ λ` is `g(a) = S a² - 8λ a + 8 - S ≥ 0`.  `g` is convex, so in general its
minimum sits at the vertex `4λ/S` — but **the vertex lies outside every one of the 18
intervals** (checked exactly), so `g` is monotone on each and the two endpoint values
settle it.  Rows 1–5 have the vertex above `β`; rows 6–18 below `α`.

Margins are thin: row 1 clears at `β` by `2.9·10⁻⁴`, row 12 at `α` by `8.8·10⁻⁵`.
-/

/-- Row 1: `a ∈ [9/20, 19/40]`, `S = 11043/2000`, `λ = 49/50`, `Y = 199/1000`.  Vertex `0.7100` is above β, so `g` is decreasing here. -/
theorem row1_L {a : ℝ} (h0 : (9/20 : ℝ) ≤ a) (h1 : a ≤ (19/40 : ℝ)) :
    0 ≤ (11043/2000 : ℝ) * a ^ 2 - 8 * (49/50 : ℝ) * a + 8 - (11043/2000 : ℝ) := by
    have hfac : 0 ≤ ((19/40 : ℝ) - a) * (8 * (49/50 : ℝ) - (11043/2000 : ℝ) * (a + (19/40 : ℝ))) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 1: the remaining side conditions. -/
theorem row1_side :
    (199/1000 : ℝ) ^ 2 ≥ 1 - (49/50 : ℝ) ^ 2 ∧ 2 * (49/50 : ℝ) ≥ (19/40 : ℝ) ∧
    0 ≤ (11043/2000 : ℝ) / 4 - 1 ∧ ((11043/2000 : ℝ) / 4 - 1) * (1 - (9/20 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 2: `a ∈ [19/40, 1/2]`, `S = 2783/500`, `λ = 239/250`, `Y = 587/2000`.  Vertex `0.6870` is above β, so `g` is decreasing here. -/
theorem row2_L {a : ℝ} (h0 : (19/40 : ℝ) ≤ a) (h1 : a ≤ (1/2 : ℝ)) :
    0 ≤ (2783/500 : ℝ) * a ^ 2 - 8 * (239/250 : ℝ) * a + 8 - (2783/500 : ℝ) := by
    have hfac : 0 ≤ ((1/2 : ℝ) - a) * (8 * (239/250 : ℝ) - (2783/500 : ℝ) * (a + (1/2 : ℝ))) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 2: the remaining side conditions. -/
theorem row2_side :
    (587/2000 : ℝ) ^ 2 ≥ 1 - (239/250 : ℝ) ^ 2 ∧ 2 * (239/250 : ℝ) ≥ (1/2 : ℝ) ∧
    0 ≤ (2783/500 : ℝ) / 4 - 1 ∧ ((2783/500 : ℝ) / 4 - 1) * (1 - (19/40 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 3: `a ∈ [1/2, 21/40]`, `S = 2257/400`, `λ = 1863/2000`, `Y = 91/250`.  Vertex `0.6603` is above β, so `g` is decreasing here. -/
theorem row3_L {a : ℝ} (h0 : (1/2 : ℝ) ≤ a) (h1 : a ≤ (21/40 : ℝ)) :
    0 ≤ (2257/400 : ℝ) * a ^ 2 - 8 * (1863/2000 : ℝ) * a + 8 - (2257/400 : ℝ) := by
    have hfac : 0 ≤ ((21/40 : ℝ) - a) * (8 * (1863/2000 : ℝ) - (2257/400 : ℝ) * (a + (21/40 : ℝ))) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 3: the remaining side conditions. -/
theorem row3_side :
    (91/250 : ℝ) ^ 2 ≥ 1 - (1863/2000 : ℝ) ^ 2 ∧ 2 * (1863/2000 : ℝ) ≥ (21/40 : ℝ) ∧
    0 ≤ (2257/400 : ℝ) / 4 - 1 ∧ ((2257/400 : ℝ) / 4 - 1) * (1 - (1/2 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 4: `a ∈ [21/40, 11/20]`, `S = 1151/200`, `λ = 1811/2000`, `Y = 849/2000`.  Vertex `0.6294` is above β, so `g` is decreasing here. -/
theorem row4_L {a : ℝ} (h0 : (21/40 : ℝ) ≤ a) (h1 : a ≤ (11/20 : ℝ)) :
    0 ≤ (1151/200 : ℝ) * a ^ 2 - 8 * (1811/2000 : ℝ) * a + 8 - (1151/200 : ℝ) := by
    have hfac : 0 ≤ ((11/20 : ℝ) - a) * (8 * (1811/2000 : ℝ) - (1151/200 : ℝ) * (a + (11/20 : ℝ))) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 4: the remaining side conditions. -/
theorem row4_side :
    (849/2000 : ℝ) ^ 2 ≥ 1 - (1811/2000 : ℝ) ^ 2 ∧ 2 * (1811/2000 : ℝ) ≥ (11/20 : ℝ) ∧
    0 ≤ (1151/200 : ℝ) / 4 - 1 ∧ ((1151/200 : ℝ) / 4 - 1) * (1 - (21/40 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 5: `a ∈ [11/20, 23/40]`, `S = 11819/2000`, `λ = 879/1000`, `Y = 477/1000`.  Vertex `0.5950` is above β, so `g` is decreasing here. -/
theorem row5_L {a : ℝ} (h0 : (11/20 : ℝ) ≤ a) (h1 : a ≤ (23/40 : ℝ)) :
    0 ≤ (11819/2000 : ℝ) * a ^ 2 - 8 * (879/1000 : ℝ) * a + 8 - (11819/2000 : ℝ) := by
    have hfac : 0 ≤ ((23/40 : ℝ) - a) * (8 * (879/1000 : ℝ) - (11819/2000 : ℝ) * (a + (23/40 : ℝ))) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 5: the remaining side conditions. -/
theorem row5_side :
    (477/1000 : ℝ) ^ 2 ≥ 1 - (879/1000 : ℝ) ^ 2 ∧ 2 * (879/1000 : ℝ) ≥ (23/40 : ℝ) ∧
    0 ≤ (11819/2000 : ℝ) / 4 - 1 ∧ ((11819/2000 : ℝ) / 4 - 1) * (1 - (11/20 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 6: `a ∈ [23/40, 3/5]`, `S = 764/125`, `λ = 1699/2000`, `Y = 66/125`.  Vertex `0.5560` is below α, so `g` is increasing here. -/
theorem row6_L {a : ℝ} (h0 : (23/40 : ℝ) ≤ a) (h1 : a ≤ (3/5 : ℝ)) :
    0 ≤ (764/125 : ℝ) * a ^ 2 - 8 * (1699/2000 : ℝ) * a + 8 - (764/125 : ℝ) := by
    have hfac : 0 ≤ (a - (23/40 : ℝ)) * ((764/125 : ℝ) * (a + (23/40 : ℝ)) - 8 * (1699/2000 : ℝ)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 6: the remaining side conditions. -/
theorem row6_side :
    (66/125 : ℝ) ^ 2 ≥ 1 - (1699/2000 : ℝ) ^ 2 ∧ 2 * (1699/2000 : ℝ) ≥ (3/5 : ℝ) ∧
    0 ≤ (764/125 : ℝ) / 4 - 1 ∧ ((764/125 : ℝ) / 4 - 1) * (1 - (23/40 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 7: `a ∈ [3/5, 5/8]`, `S = 637/100`, `λ = 817/1000`, `Y = 577/1000`.  Vertex `0.5130` is below α, so `g` is increasing here. -/
theorem row7_L {a : ℝ} (h0 : (3/5 : ℝ) ≤ a) (h1 : a ≤ (5/8 : ℝ)) :
    0 ≤ (637/100 : ℝ) * a ^ 2 - 8 * (817/1000 : ℝ) * a + 8 - (637/100 : ℝ) := by
    have hfac : 0 ≤ (a - (3/5 : ℝ)) * ((637/100 : ℝ) * (a + (3/5 : ℝ)) - 8 * (817/1000 : ℝ)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 7: the remaining side conditions. -/
theorem row7_side :
    (577/1000 : ℝ) ^ 2 ≥ 1 - (817/1000 : ℝ) ^ 2 ∧ 2 * (817/1000 : ℝ) ≥ (5/8 : ℝ) ∧
    0 ≤ (637/100 : ℝ) / 4 - 1 ∧ ((637/100 : ℝ) / 4 - 1) * (1 - (3/5 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 8: `a ∈ [5/8, 13/20]`, `S = 13093/2000`, `λ = 401/500`, `Y = 239/400`.  Vertex `0.4900` is below α, so `g` is increasing here. -/
theorem row8_L {a : ℝ} (h0 : (5/8 : ℝ) ≤ a) (h1 : a ≤ (13/20 : ℝ)) :
    0 ≤ (13093/2000 : ℝ) * a ^ 2 - 8 * (401/500 : ℝ) * a + 8 - (13093/2000 : ℝ) := by
    have hfac : 0 ≤ (a - (5/8 : ℝ)) * ((13093/2000 : ℝ) * (a + (5/8 : ℝ)) - 8 * (401/500 : ℝ)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 8: the remaining side conditions. -/
theorem row8_side :
    (239/400 : ℝ) ^ 2 ≥ 1 - (401/500 : ℝ) ^ 2 ∧ 2 * (401/500 : ℝ) ≥ (13/20 : ℝ) ∧
    0 ≤ (13093/2000 : ℝ) / 4 - 1 ∧ ((13093/2000 : ℝ) / 4 - 1) * (1 - (5/8 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 9: `a ∈ [13/20, 27/40]`, `S = 13113/2000`, `λ = 81/100`, `Y = 1173/2000`.  Vertex `0.4942` is below α, so `g` is increasing here. -/
theorem row9_L {a : ℝ} (h0 : (13/20 : ℝ) ≤ a) (h1 : a ≤ (27/40 : ℝ)) :
    0 ≤ (13113/2000 : ℝ) * a ^ 2 - 8 * (81/100 : ℝ) * a + 8 - (13113/2000 : ℝ) := by
    have hfac : 0 ≤ (a - (13/20 : ℝ)) * ((13113/2000 : ℝ) * (a + (13/20 : ℝ)) - 8 * (81/100 : ℝ)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 9: the remaining side conditions. -/
theorem row9_side :
    (1173/2000 : ℝ) ^ 2 ≥ 1 - (81/100 : ℝ) ^ 2 ∧ 2 * (81/100 : ℝ) ≥ (27/40 : ℝ) ∧
    0 ≤ (13113/2000 : ℝ) / 4 - 1 ∧ ((13113/2000 : ℝ) / 4 - 1) * (1 - (13/20 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 10: `a ∈ [27/40, 7/10]`, `S = 3289/500`, `λ = 409/500`, `Y = 1151/2000`.  Vertex `0.4974` is below α, so `g` is increasing here. -/
theorem row10_L {a : ℝ} (h0 : (27/40 : ℝ) ≤ a) (h1 : a ≤ (7/10 : ℝ)) :
    0 ≤ (3289/500 : ℝ) * a ^ 2 - 8 * (409/500 : ℝ) * a + 8 - (3289/500 : ℝ) := by
    have hfac : 0 ≤ (a - (27/40 : ℝ)) * ((3289/500 : ℝ) * (a + (27/40 : ℝ)) - 8 * (409/500 : ℝ)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 10: the remaining side conditions. -/
theorem row10_side :
    (1151/2000 : ℝ) ^ 2 ≥ 1 - (409/500 : ℝ) ^ 2 ∧ 2 * (409/500 : ℝ) ≥ (7/10 : ℝ) ∧
    0 ≤ (3289/500 : ℝ) / 4 - 1 ∧ ((3289/500 : ℝ) / 4 - 1) * (1 - (27/40 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 11: `a ∈ [7/10, 29/40]`, `S = 529/80`, `λ = 413/500`, `Y = 141/250`.  Vertex `0.4997` is below α, so `g` is increasing here. -/
theorem row11_L {a : ℝ} (h0 : (7/10 : ℝ) ≤ a) (h1 : a ≤ (29/40 : ℝ)) :
    0 ≤ (529/80 : ℝ) * a ^ 2 - 8 * (413/500 : ℝ) * a + 8 - (529/80 : ℝ) := by
    have hfac : 0 ≤ (a - (7/10 : ℝ)) * ((529/80 : ℝ) * (a + (7/10 : ℝ)) - 8 * (413/500 : ℝ)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 11: the remaining side conditions. -/
theorem row11_side :
    (141/250 : ℝ) ^ 2 ≥ 1 - (413/500 : ℝ) ^ 2 ∧ 2 * (413/500 : ℝ) ≥ (29/40 : ℝ) ∧
    0 ≤ (529/80 : ℝ) / 4 - 1 ∧ ((529/80 : ℝ) / 4 - 1) * (1 - (7/10 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 12: `a ∈ [29/40, 3/4]`, `S = 6661/1000`, `λ = 1669/2000`, `Y = 1103/2000`.  Vertex `0.5011` is below α, so `g` is increasing here. -/
theorem row12_L {a : ℝ} (h0 : (29/40 : ℝ) ≤ a) (h1 : a ≤ (3/4 : ℝ)) :
    0 ≤ (6661/1000 : ℝ) * a ^ 2 - 8 * (1669/2000 : ℝ) * a + 8 - (6661/1000 : ℝ) := by
    have hfac : 0 ≤ (a - (29/40 : ℝ)) * ((6661/1000 : ℝ) * (a + (29/40 : ℝ)) - 8 * (1669/2000 : ℝ)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 12: the remaining side conditions. -/
theorem row12_side :
    (1103/2000 : ℝ) ^ 2 ≥ 1 - (1669/2000 : ℝ) ^ 2 ∧ 2 * (1669/2000 : ℝ) ≥ (3/4 : ℝ) ∧
    0 ≤ (6661/1000 : ℝ) / 4 - 1 ∧ ((6661/1000 : ℝ) / 4 - 1) * (1 - (29/40 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 13: `a ∈ [3/4, 31/40]`, `S = 1681/250`, `λ = 843/1000`, `Y = 269/500`.  Vertex `0.5015` is below α, so `g` is increasing here. -/
theorem row13_L {a : ℝ} (h0 : (3/4 : ℝ) ≤ a) (h1 : a ≤ (31/40 : ℝ)) :
    0 ≤ (1681/250 : ℝ) * a ^ 2 - 8 * (843/1000 : ℝ) * a + 8 - (1681/250 : ℝ) := by
    have hfac : 0 ≤ (a - (3/4 : ℝ)) * ((1681/250 : ℝ) * (a + (3/4 : ℝ)) - 8 * (843/1000 : ℝ)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 13: the remaining side conditions. -/
theorem row13_side :
    (269/500 : ℝ) ^ 2 ≥ 1 - (843/1000 : ℝ) ^ 2 ∧ 2 * (843/1000 : ℝ) ≥ (31/40 : ℝ) ∧
    0 ≤ (1681/250 : ℝ) / 4 - 1 ∧ ((1681/250 : ℝ) / 4 - 1) * (1 - (3/4 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 14: `a ∈ [31/40, 4/5]`, `S = 1701/250`, `λ = 213/250`, `Y = 131/250`.  Vertex `0.5009` is below α, so `g` is increasing here. -/
theorem row14_L {a : ℝ} (h0 : (31/40 : ℝ) ≤ a) (h1 : a ≤ (4/5 : ℝ)) :
    0 ≤ (1701/250 : ℝ) * a ^ 2 - 8 * (213/250 : ℝ) * a + 8 - (1701/250 : ℝ) := by
    have hfac : 0 ≤ (a - (31/40 : ℝ)) * ((1701/250 : ℝ) * (a + (31/40 : ℝ)) - 8 * (213/250 : ℝ)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 14: the remaining side conditions. -/
theorem row14_side :
    (131/250 : ℝ) ^ 2 ≥ 1 - (213/250 : ℝ) ^ 2 ∧ 2 * (213/250 : ℝ) ≥ (4/5 : ℝ) ∧
    0 ≤ (1701/250 : ℝ) / 4 - 1 ∧ ((1701/250 : ℝ) / 4 - 1) * (1 - (31/40 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 15: `a ∈ [4/5, 33/40]`, `S = 2761/400`, `λ = 1723/2000`, `Y = 127/250`.  Vertex `0.4992` is below α, so `g` is increasing here. -/
theorem row15_L {a : ℝ} (h0 : (4/5 : ℝ) ≤ a) (h1 : a ≤ (33/40 : ℝ)) :
    0 ≤ (2761/400 : ℝ) * a ^ 2 - 8 * (1723/2000 : ℝ) * a + 8 - (2761/400 : ℝ) := by
    have hfac : 0 ≤ (a - (4/5 : ℝ)) * ((2761/400 : ℝ) * (a + (4/5 : ℝ)) - 8 * (1723/2000 : ℝ)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 15: the remaining side conditions. -/
theorem row15_side :
    (127/250 : ℝ) ^ 2 ≥ 1 - (1723/2000 : ℝ) ^ 2 ∧ 2 * (1723/2000 : ℝ) ≥ (33/40 : ℝ) ∧
    0 ≤ (2761/400 : ℝ) / 4 - 1 ∧ ((2761/400 : ℝ) / 4 - 1) * (1 - (4/5 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 16: `a ∈ [33/40, 17/20]`, `S = 14041/2000`, `λ = 109/125`, `Y = 49/100`.  Vertex `0.4968` is below α, so `g` is increasing here. -/
theorem row16_L {a : ℝ} (h0 : (33/40 : ℝ) ≤ a) (h1 : a ≤ (17/20 : ℝ)) :
    0 ≤ (14041/2000 : ℝ) * a ^ 2 - 8 * (109/125 : ℝ) * a + 8 - (14041/2000 : ℝ) := by
    have hfac : 0 ≤ (a - (33/40 : ℝ)) * ((14041/2000 : ℝ) * (a + (33/40 : ℝ)) - 8 * (109/125 : ℝ)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 16: the remaining side conditions. -/
theorem row16_side :
    (49/100 : ℝ) ^ 2 ≥ 1 - (109/125 : ℝ) ^ 2 ∧ 2 * (109/125 : ℝ) ≥ (17/20 : ℝ) ∧
    0 ≤ (14041/2000 : ℝ) / 4 - 1 ∧ ((14041/2000 : ℝ) / 4 - 1) * (1 - (33/40 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 17: `a ∈ [17/20, 7/8]`, `S = 7161/1000`, `λ = 221/250`, `Y = 187/400`.  Vertex `0.4938` is below α, so `g` is increasing here. -/
theorem row17_L {a : ℝ} (h0 : (17/20 : ℝ) ≤ a) (h1 : a ≤ (7/8 : ℝ)) :
    0 ≤ (7161/1000 : ℝ) * a ^ 2 - 8 * (221/250 : ℝ) * a + 8 - (7161/1000 : ℝ) := by
    have hfac : 0 ≤ (a - (17/20 : ℝ)) * ((7161/1000 : ℝ) * (a + (17/20 : ℝ)) - 8 * (221/250 : ℝ)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 17: the remaining side conditions. -/
theorem row17_side :
    (187/400 : ℝ) ^ 2 ≥ 1 - (221/250 : ℝ) ^ 2 ∧ 2 * (221/250 : ℝ) ≥ (7/8 : ℝ) ∧
    0 ≤ (7161/1000 : ℝ) / 4 - 1 ∧ ((7161/1000 : ℝ) / 4 - 1) * (1 - (17/20 : ℝ) ^ 2) ≤ 1 := by
  norm_num

/-- Row 18: `a ∈ [7/8, 9/10]`, `S = 3663/500`, `λ = 359/400`, `Y = 883/2000`.  Vertex `0.4900` is below α, so `g` is increasing here. -/
theorem row18_L {a : ℝ} (h0 : (7/8 : ℝ) ≤ a) (h1 : a ≤ (9/10 : ℝ)) :
    0 ≤ (3663/500 : ℝ) * a ^ 2 - 8 * (359/400 : ℝ) * a + 8 - (3663/500 : ℝ) := by
    have hfac : 0 ≤ (a - (7/8 : ℝ)) * ((3663/500 : ℝ) * (a + (7/8 : ℝ)) - 8 * (359/400 : ℝ)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith [hfac]

/-- Row 18: the remaining side conditions. -/
theorem row18_side :
    (883/2000 : ℝ) ^ 2 ≥ 1 - (359/400 : ℝ) ^ 2 ∧ 2 * (359/400 : ℝ) ≥ (9/10 : ℝ) ∧
    0 ≤ (3663/500 : ℝ) / 4 - 1 ∧ ((3663/500 : ℝ) / 4 - 1) * (1 - (7/8 : ℝ) ^ 2) ≤ 1 := by
  norm_num

end Sendov9.Mid

#print axioms Sendov9.Mid.row1_L
#print axioms Sendov9.Mid.row2_L
#print axioms Sendov9.Mid.row3_L
#print axioms Sendov9.Mid.row4_L
#print axioms Sendov9.Mid.row5_L
#print axioms Sendov9.Mid.row6_L
#print axioms Sendov9.Mid.row7_L
#print axioms Sendov9.Mid.row8_L
#print axioms Sendov9.Mid.row9_L
#print axioms Sendov9.Mid.row10_L
#print axioms Sendov9.Mid.row11_L
#print axioms Sendov9.Mid.row12_L
#print axioms Sendov9.Mid.row13_L
#print axioms Sendov9.Mid.row14_L
#print axioms Sendov9.Mid.row15_L
#print axioms Sendov9.Mid.row16_L
#print axioms Sendov9.Mid.row17_L
#print axioms Sendov9.Mid.row18_L
#print axioms Sendov9.Mid.row1_side
#print axioms Sendov9.Mid.row2_side
#print axioms Sendov9.Mid.row3_side
#print axioms Sendov9.Mid.row4_side
#print axioms Sendov9.Mid.row5_side
#print axioms Sendov9.Mid.row6_side
#print axioms Sendov9.Mid.row7_side
#print axioms Sendov9.Mid.row8_side
#print axioms Sendov9.Mid.row9_side
#print axioms Sendov9.Mid.row10_side
#print axioms Sendov9.Mid.row11_side
#print axioms Sendov9.Mid.row12_side
#print axioms Sendov9.Mid.row13_side
#print axioms Sendov9.Mid.row14_side
#print axioms Sendov9.Mid.row15_side
#print axioms Sendov9.Mid.row16_side
#print axioms Sendov9.Mid.row17_side
#print axioms Sendov9.Mid.row18_side
