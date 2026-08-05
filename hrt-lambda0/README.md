# HRT at Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)} — the endgame, Lean 4 (CONDITIONAL)

**What is machine-checked here, in one sentence:** the *endgame* of the paper
`paper/hrt-lambda0.tex` — that the paper's analytic reduction **suffices** to prove the
HRT conjecture at the resonant four-point configuration `Λ₀` — is formalized axiom-free;
the reduction itself is an **unproved hypothesis** (`ZakReduction`), so the HRT
subconjecture at `Λ₀` is **NOT claimed unconditionally** by this directory.

## The problem

The Heil–Ramanathan–Topiwala (HRT) conjecture asserts that finitely many time–frequency
translates of a nonzero `g ∈ L²(ℝ)` are linearly independent. The four-point
configuration `Λ₀ = {(0,0), (1,0), (0,1), (√2,√2)}` is a distinguished open special
case: it is Conjecture 9.2(a) of Heil's 2006 survey *Linear Independence of Finite Gabor
Systems* and Conjecture 2 of the Heil–Speegle survey, and it is **unreachable** from the
solved lattice (Linnell) and parallel-line cases — `lambda0_symplectic_escape` proves the
obstruction inside Lean.

## The statement proved

```lean
theorem HRTLambda0.Statement.lambda0_independent_of_reduction {g : ℝ → ℂ}
    (h : HRTLambda0.ZakReduction g) : HRTLambda0.Lambda0Independent g
```

*If the paper's analytic reduction applies to the window `g`, then the four translates
`g(x), g(x−1), e^{2πix}g(x), e^{2πi√2x}g(x−√2)` are linearly independent.*

`#print axioms`: exactly `[propext, Classical.choice, Quot.sound]`. No `sorry` outside
the deliberate placeholder in `Challenge.lean`; no declared axiom anywhere.

**The hypothesis is the honesty-critical part.** `ZakReduction g`
(`HRTLambda0/Statement.lean`) packages what the paper establishes before its endgame —
the Zak-transform reduction, the fibre dichotomy, the degree identity at `j = 0`, and
Jensen's formula on the fibre. The paper proves these for every window whose Zak
transform has a continuous representative (in particular every nonzero Schwartz `g`),
attributing the fibration, dichotomy and winding identity to Oussa (cited there as
arXiv:2508.04613v2); **none of that analysis is formalized here**. Discharging it would
need a Lean theory of the Zak transform, circle-map degree theory, and Jensen's formula
— none of which is in Mathlib.

## What IS formalized (all axiom-clean, `HRTLambda0/Endgame.lean`)

| paper item | Lean |
|---|---|
| Remark — `Λ₀` escapes the solved cases | `lambda0_symplectic_escape` |
| Lemma "dichotomy", propagation step | `zero_propagates` |
| Lemma "dichotomy", full | `fibre_dichotomy` (from density of the irrational orbit) |
| Lemma "degree identity", arithmetic core (`\|j\| ≥ 2` dies) | `degree_identity_kills` |
| quadratic rigidity | `two_of_three_eq_of_quadratic` |
| two-circle rigidity (continuity-free strengthening) | `circle_pair_quadratic` |
| **the endgame: Jensen constancy vs Vieta ⇒ contradiction** | `hrt_endgame` |
| Theorem "main", conditional form | `lambda0_independent_of_reduction` |

The formalized endgame is *stronger* than the paper's prose in one respect: the paper
uses continuity of `ζ_out` to force constancy; `circle_pair_quadratic` cuts the
two-circle intersection out by a single fixed quadratic, so three sample fibres suffice
and no continuity is needed.

## What to read

`Challenge.lean` + `HRTLambda0/Statement.lean` + Mathlib are the entire audit surface.
`Solution.lean` proves the challenge statement by direct term assignment from the
development. `comparator/all.json` lists the five project-specific definitions the
statement rests on — read `ZakReduction` before anything else.

## Relation to the wider campaign

A separate, much larger Lean campaign (in the private development repository) is
attacking the reduction itself — the Zak transform as an `L²` object, the shift
covariance, the Birkhoff/cocycle machinery — with the aim of discharging `ZakReduction`
and making the theorem unconditional. Until that lands, what this directory certifies is
exactly the conditional statement above, nothing more.

## Verification

See `VERIFICATION.md`: the local kernel-check log (recorded verbatim), the paper's
sha256 pins, what is and is not claimed, and the CI/Comparator posture
(`.github/workflows/hrt-lambda0-build.yml`, `hrt-lambda0-comparator.yml`).
