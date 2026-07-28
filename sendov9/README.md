# Sendov's conjecture in degree nine — Lean 4

**Statement proved, unconditionally and axiom-free:**

```lean
theorem Sendov9.Statement.sendov_degree_nine_general {p : ℂ[X]} (hdeg : p.natDegree = 9)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1
```

*Every complex polynomial of degree nine with all zeros in the closed unit disk has, for
each zero `a`, a critical point within distance one of `a`.*

`#print axioms` shows exactly `[propext, Classical.choice, Quot.sound]`. There are **no
carried hypotheses, no literature axioms, and no `sorry`** anywhere in the 46 modules of
the `Sendov9` library — the only `sorry`s in this directory are the two deliberate
placeholders in `Challenge.lean`, which is the audit surface.

The mathematics is **Anton Shakov's** (`paper/sendov9.tex`). The contribution of this
directory is the machine-checked verification.

## Why degree nine

Brown–Xiang settled `n ≤ 8` (1999). Tao settled all sufficiently large `n` (2020), with no
effective bound, so degree nine was not covered. The only prior claim reaching degree nine
is Meng, arXiv:1705.07235 — unpublished since 2018 and publicly doubted. No assessment of
that claim is made here.

## What to read

The trusted surface is **`Challenge.lean` and Mathlib. That is all.** Unlike the other
solutions in this repository there is no `Statement.lean` holding definitions, because the
statement needs none: `Polynomial.roots`, `Polynomial.derivative`, `Polynomial.natDegree`
and the norm on `ℂ` are all Mathlib's own. There is nothing project-specific to audit
between the statement and its meaning, which is why `comparator/all.json` carries no
`definition_names` entry.

`Solution.lean` proves those statements by direct term assignment from the development.

## The route

| Paper | Lean |
|---|---|
| Thm 1.1 — the main theorem | `Sendov9/Final.lean` — `sendov_degree_nine_general` |
| Lemma 2.1 — separation from a zero | `Sendov9/Final.lean` — `separation` |
| — its input, Grace–Walsh–Szegő | `Sendov9/GWS.lean` — **proved, not assumed** |
| — its input, Grace's apolarity theorem | `Sendov9/Grace2Lib.lean` |
| — its input, Laguerre's theorem | `Sendov9/Grace2Lib.lean` (`Laguerre2`, `Laguerre3`, `LagGen`) |
| — the constant `2 sin(π/9)` | `Sendov9/RootUnity.lean` — **without trigonometry** |
| Lemma 2.2 — the σ bound | `Sendov9/Sigma22Gen.lean` — general `(m,M,C,ν)` form |
| §3 — the reciprocal reduction | `Sendov9/Core.lean`, `Sendov9/Data.lean` |
| §4 — the range `0 ≤ a ≤ 9/20` | `Sendov9/Final.lean` — `small_excluded` |
| §5 — the range `9/20 ≤ a ≤ 9/10` | `Sendov9/MidRows.lean` — 18 certificates |
| §6 — the boundary `9/10 ≤ a ≤ 1` | `Sendov9/TopRow.lean` |
| §7 — completion (rotation) | `Sendov9/RotateData.lean` |
| §8 — exact Bernstein verification | `Sendov9/CertData.lean` |

Three classical theorems are **proved here rather than assumed**, so the formalization has
no literature dependency at all: Laguerre's theorem, **Grace's apolarity theorem** (to the
best of our knowledge, the first formalization in any proof assistant), and
Grace–Walsh–Szegő. Maclaurin's inequality at `n = 8` is proved too, by butterfly smoothing
rather than real-rootedness.

## Three things worth knowing

**The certificates are integer-scaled.** The usual monomial-to-Bernstein conversion carries
`C(i,k)/C(N,k)`, which would force rational arithmetic — and the kernel's `Nat.gcd` is not
GMP-accelerated, so 40-digit rationals would have been fatal. But
`C(N,i)·C(i,k) = C(N,k)·C(N−k,i−k)`, so after cancelling the basis's own `C(N,i)` the
coefficients are **integers** and `decide` runs on GMP-accelerated integer arithmetic. No
floating point and no `native_decide` appears anywhere.

**The separation constant is reached algebraically.** The paper reads `2 sin(π/9)` off the
ninth roots of unity. Here a vanishing integral forces `ω⁹ = 1, ω ≠ 1`, and then the
Laurent identity `ω⁴((t+1)(t³−3t+1)) = ∑_{k<9} ωᵏ` with `t = ω + ω⁻¹` — an identity needing
only `ω ≠ 0` — reduces `min‖1−ω‖` to the largest root of `t³ − 3t + 1`. So `Real.sin`,
`Real.arg` and root-of-unity enumeration never appear.

**A statement can be true for the wrong reason.** The one genuine defect this
formalization turned up was a carried hypothesis that was *vacuous* at `n = 0`
(`Sendov9/GWSFix.lean` refutes it), which would have trivialised every dependent theorem
without leaving a trace in `#print axioms`. Everything targets the corrected statement, and
`Sendov9/NonVacuous.lean` applies the main theorem to `p = X⁹` to confirm the final
hypotheses are satisfiable.

## Verification

See `VERIFICATION.md` for the ledger: every command, its real output, the paper's sha256
pins, the negative control, and what is *not* claimed. Comparator runs on CI
(`.github/workflows/sendov9-comparator.yml`), Linux-only, in a landrun/Landlock sandbox.
