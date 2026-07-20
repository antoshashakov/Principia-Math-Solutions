# Erdős Problem 123 — a Lean 4 formalization

A complete, `sorry`-free Lean 4 + Mathlib formalization of every numbered result in
**"Antichain Subset Sums in Rank-Three Multiplicative Semigroups"**
([`paper/erdos123_lean_journal.pdf`](paper/erdos123_lean_journal.pdf)), including
[Erdős Problem 123](https://www.erdosproblems.com/123) and a local central limit theorem
for the Bernoulli subset sums of a short multiplicative band.

> Let `a, b, c ≥ 2` be pairwise coprime and `S = {aᵏbˡcᵐ}`. For every real
> `1 < ρ < min(a,b,c)`, every sufficiently large integer is a subset sum of
> `S ∩ [x, ρx)` for some `x`. Such a set is automatically a divisibility antichain,
> resolving Erdős Problem 123.

## The results

Six theorems are checked mechanically against a trusted statement file. All six have
axiom footprint exactly `[propext, Classical.choice, Quot.sound]` — Lean's standard
classical base, with no `sorryAx`.

| Paper | Statement | Lean | Module |
| --- | --- | --- | --- |
| Thm 1.2 | Erdős 123, real ratio `ρ` | `erdos123_dcomplete_real` | `Erdos123/GMain.lean` |
| Thm 1.1, eq. (1.1) | The local limit law, uniformly in `n` | `glclt_asymptotic` | `Erdos123/GLCLTAsymptotic.lean` |
| Thm 1.1, 2nd assertion | Coverage of the full central window | `glclt_coverage` | `Erdos123/GLCLT.lean` |
| Thm 1.2 | Erdős 123, classical `d`-complete phrasing | `erdos123_dcomplete'` | `Erdos123/Main.lean` |
| Prop 3.1, eq. (3.1) | Rigidity: low-energy measure bound | `glow_energy_measure_general` | `Erdos123/GLowEnergyGen.lean` |
| Prop 3.1, eq. (3.2) | Rigidity: very low energy pins `t` | `gvery_low_sharp` | `Erdos123/GTail.lean` |

Proposition 2.1 (band geometry) and Lemma 4.1 (Fourier tails) are also fully proved;
[`formalization.yaml`](formalization.yaml) carries the complete statement-by-statement
map from the paper into the Lean, including these.

**Nothing is assumed from the literature.** Every result is proved outright on top of
Mathlib. The paper makes no effectivity claim, and the Lean thresholds are existential
(`∃ X₀`, `∃ N₀`) exactly as the paper states them.

## How the statements are kept honest

The risk with a large formalization is not an unsound proof — Lean's kernel handles
that — but a proof of a subtly *different* statement. Three things guard against it:

1. **[`Erdos123/Statement.lean`](Erdos123/Statement.lean)** — a definition-only module
   importing nothing but Mathlib. Every notion the theorems mention (`Smooth3`,
   `IsPrimitive`, `GBand`, `gProb`, `gSigma`, `gMu`, `GQenergy`, …) is defined here and
   nowhere else in the trusted path.
2. **[`Challenge.lean`](Challenge.lean)** — the six statements, with their proofs left
   open. Its entire import closure is `Erdos123.Statement` plus Mathlib. **These two
   files are the whole audit surface**: read them and you have read everything you must
   trust. Together they are under 200 lines.
3. **[`Solution.lean`](Solution.lean)** — the same six statements, each discharged by a
   *direct term assignment* from the development's theorem. A term assignment forces
   Lean to check the two statements are definitionally equal, which in turn forces every
   definition in `Statement.lean` to agree with its counterpart in the development. No
   transport lemma does hidden work, and a drifted copy would fail to compile.

[Comparator](https://github.com/leanprover/comparator) then verifies mechanically that
`Solution.lean` proves exactly the statements in `Challenge.lean` using no axioms beyond
the permitted three. Configs are in [`comparator/`](comparator/).

The six `sorry`s in `Challenge.lean` are deliberate and are the only ones in the
repository.

## Verify it yourself

```bash
cd erdos123
lake exe cache get      # Mathlib oleans
lake build              # every module; expect: Build completed successfully (8587 jobs)
```

[`VERIFICATION.md`](VERIFICATION.md) records every check that was actually run, with its
verbatim output, the commit, and the toolchain — including what was *not* run and why.
Read it before trusting any claim on this page.

## Layout

```
Challenge.lean            trusted statements, proofs left open  ← audit surface
Solution.lean             the same statements, proved
Erdos123/Statement.lean   definitions only, Mathlib-only imports ← audit surface
Erdos123/                 the development (24 modules, ~12k lines)
Erdos123.lean             build root; imports every module in the development
Erdos123Complete.lean     the whole development as one standalone file (not in `lake build`)
comparator/               Comparator configs, one per main result
paper/                    the source manuscript, sha256-pinned in VERIFICATION.md
formalization.yaml        metadata per the mathlib-initiative reporting standard
```

## License

Apache-2.0. See [LICENSE](LICENSE).
