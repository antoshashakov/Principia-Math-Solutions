# Principia Math — Solutions

Lean 4 formalizations of solved open problems, one folder per problem. Each folder is a
self-contained Lake project with its own paper, build, and verification record.

| Problem | Result | Status |
| --- | --- | --- |
| [`erdos123/`](erdos123/) | [Erdős Problem 123](https://www.erdosproblems.com/123) — for pairwise-coprime `a,b,c ≥ 2`, every large integer is a subset sum of a divisibility antichain in `{aᵏbˡcᵐ}` — together with a local central limit theorem for the subset sums of a short multiplicative band | Complete, `sorry`-free; **Comparator-certified on CI** |
| [`erdos1054/`](erdos1054/) | [Erdős Problem 1054](https://www.erdosproblems.com/1054) — the limsup part: for every `A ≥ 1` the represented `N` with `f(N) > A·N` have positive lower density, so `f(N)/N` is unbounded — together with an unconditional formalization of the almost-all binary Goldbach theorem it rests on | Complete, `sorry`-free; Comparator **not yet run** (see [`erdos1054/VERIFICATION.md`](erdos1054/VERIFICATION.md) §5) |
| [`sendov9-11/`](sendov9-11/) | **Sendov's conjecture, degrees nine to eleven** — every complex polynomial of degree `n` with all zeros in the closed unit disk has, for each zero `a`, a zero of the derivative within distance `1` of `a`. Degree nine was the open case (Brown–Xiang settled `n ≤ 8`; Tao all sufficiently large `n`) | **Degree 9: PROVED** — `sorry`-free & **axiom-free**, no carried hypotheses; Grace–Walsh–Szegő, Grace's apolarity theorem and Laguerre's theorem are **proved here, not assumed**; **Comparator-certified on CI**. **Degrees 10/11: PARTIAL, not claimed** — the finite certificate half is kernel-checked (10: 51/51 boxes; 11: 329/531, in progress); the analytic reduction is an explicit unproved hypothesis (see [`sendov9-11/VERIFICATION.md`](sendov9-11/VERIFICATION.md) Part II) |
| [`hrt-lambda0/`](hrt-lambda0/) | **HRT conjecture at `Λ₀ = {(0,0),(1,0),(0,1),(√2,√2)}`** — the four-point resonant subconjecture (Heil 2006, Conjecture 9.2(a); Heil–Speegle, Conjecture 2): the translates `g(x), g(x−1), e^{2πix}g(x), e^{2πi√2x}g(x−√2)` of a nonzero window are linearly independent | **CONDITIONAL, not claimed unconditionally** — the paper's *endgame* (Jensen constancy vs Vieta rigidity) is formalized `sorry`-free & axiom-clean, and HRT at `Λ₀` is derived from the explicitly named, unproved analytic hypothesis `ZakReduction` (see [`hrt-lambda0/VERIFICATION.md`](hrt-lambda0/VERIFICATION.md)) |
| [`erdos361/`](erdos361/) | [Erdős Problem 361](https://www.erdosproblems.com/361) — for `f_c(n) = max{\|A\| : A ⊆ [1,⌊cn⌋], n ∉ Σ(A)}`, the sequence `f_c(n)/n` converges **iff `c ≥ 1`**: the `c ≥ 1` exact formula `⌊cn⌋ − ⌈n/2⌉` and, for every `c ∈ (0,1)`, non-convergence — the Erdős–Graham irregularity question | both results `sorry`-free & **axiom-free** (Alon 1987 Thm 1.1 is proved via general-`h` Dias da Silva–Hamidoune from Mathlib's Combinatorial Nullstellensatz, not postulated — see [`erdos361/VERIFICATION.md`](erdos361/VERIFICATION.md) §4); **Comparator-certified on CI** |

## Conventions

Every solution folder follows the same layout, so a reviewer knows where to look
without reading the whole tree:

- **`paper/`** — the manuscript the Lean is measured against, committed and sha256-pinned
  so "the paper" refers to exact bytes.
- **`formalization.yaml`** — metadata per the
  [mathlib-initiative reporting standard](https://github.com/mathlib-initiative/formalization.yaml),
  including an `alignment` block mapping each numbered result in the paper to the Lean
  declaration that proves it.
- **`Challenge.lean` + a definition-only statement module** — the trusted statements,
  with a deliberately tiny import closure. This pair is the entire audit surface: read
  it and you have read everything you must trust. (`sendov9-11/` has no statement module
  at all: its statement is phrased entirely in Mathlib's own vocabulary, so
  `Challenge.lean` plus Mathlib is the whole surface.)
- **`Solution.lean`** — the same statements, proved. (`erdos1054/` has three:
  one bridge per master, since the same statements are proved by two independent
  routes plus a standalone Goldbach master.)
  [Comparator](https://github.com/leanprover/comparator) verifies mechanically that the
  two match and that no extra axioms were used; configs live in `comparator/`.
- **`VERIFICATION.md`** — the honest ledger. Every claim is either a command that was
  run with its actual output recorded, or an explicit note that it was **not** run.

The point of the split is that Lean's kernel already rules out an unsound proof. What it
cannot rule out is a sound proof of a subtly *different* statement — so the statements
are isolated, kept short, and checked separately from the proofs.

## License

Apache-2.0. See [LICENSE](LICENSE).
