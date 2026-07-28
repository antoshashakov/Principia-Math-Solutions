# VERIFICATION — Sendov's conjecture in degree nine

The honest ledger. Every claim below is either a command that was run with its actual
output recorded, or an explicit note that it was **not** run and where it *is* run.

The result claimed is:

```lean
theorem Sendov9.Statement.sendov_degree_nine_general {p : ℂ[X]} (hdeg : p.natDegree = 9)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (ha : a ∈ p.roots) :
    ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1
```

with `#print axioms` showing exactly `[propext, Classical.choice, Quot.sound]`, no carried
hypotheses, and no `sorry` in its import closure.

## §1 Scope

- The mathematics is **Anton Shakov's** (`paper/sendov9.tex`, Theorem 1.1). This directory
  contributes the machine-checked verification, nothing else.
- The formalization is **unconditional**. There is no carried hypothesis and no literature
  axiom. The three classical inputs the paper's Lemma 2.1 rests on — Laguerre's theorem,
  Grace's apolarity theorem, and Grace–Walsh–Szegő — are **proved here**, not assumed.
- The paper's two finite positivity checks (§5, §6) are performed **inside Lean** as
  nineteen exact integer-scaled Bernstein certificates discharged by `decide`. The paper's
  ancillary Python verifiers are *not* used; the certificates were independently
  re-derived from the LaTeX and are checked by Lean's kernel on integer arithmetic. No
  floating point, no `native_decide`.
- **Not claimed:** anything about degrees other than nine, any effectivity or uniformity
  statement the paper does not make, and any assessment of Meng's arXiv:1705.07235.

## §2 The build

**Environment.** Lean `leanprover/lean4:v4.31.0`; Mathlib `rev
fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (tag `v4.31.0`), pinned in `lake-manifest.json`.

**Where the authoritative build runs: CI.** `.github/workflows/sendov9-build.yml` builds
the `Sendov9` library, then `Solution`, then `Challenge`, and asserts:

1. no `declaration uses 'sorry'` anywhere in the `Sendov9` or `Solution` build logs;
2. no axiom outside `{propext, Classical.choice, Quot.sound}` appears in *any* footprint
   across both logs (this also catches `sorryAx`);
3. `Solution`'s two results each carry the full clean triple;
4. no `native_decide` / `implemented_by` / `unsafe` / `axiom` declaration in
   `Sendov9/*.lean`, `Solution.lean`, `Challenge.lean`;
5. `Challenge.lean` has exactly two `sorry`s (the audit fixture);
6. `Sendov9.NonVacuous` builds.

**Locally (Windows), partially run.** The standalone project was compiled from a cold
cache and was **stopped after three modules** — it is redundant with CI and the first
module alone took 45 minutes to import Mathlib over a freshly-unpacked olean tree:

```
⚠ [8558/8558] Built Sendov9.Apolarity2 (2707s)
⚠ [8558/8558] Built Sendov9.Bridge5 (66s)
```

with `Sendov9.CertData` in progress when it was stopped. **Zero errors up to that point.**
What this does establish is that the standalone layout, `lakefile.toml` options and
toolchain are correct; what it does **not** establish is the full build, which is CI's job.

**The full build WAS run, in the development repository**, from which every module here was
copied byte-for-byte (see §3). That gate is committed there as
`Principia Application/LeanSandbox/problems/Sendov9/final.gate.log`:

```
lake build Sendov9.Final
→ 0 errors, 0 sorries, 368 `#print axioms` lines
→ 'Sendov9.Final.sendov_degree_nine'         depends on axioms: [propext, Classical.choice, Quot.sound]
→ 'Sendov9.Final.sendov_degree_nine_general' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Of those 368 footprints, 367 are exactly `[propext, Classical.choice, Quot.sound]` and one
(`Sendov9.Top.radical_ineq`) is the strictly smaller `[propext]`.

## §3 Provenance of the copied modules

All 46 modules in `Sendov9/` are **byte-identical** to the gated originals in the
development repository (`PrincipiaAI`, commits `e3add8b` and `625ccac`). Verified with
`cmp` on every file:

```
modules compared: 46, differing: 0
```

The import closure of `Sendov9.Final` is 45 modules and is complete within this directory —
no import resolves outside it. The 46th is `Sendov9/NonVacuous.lean` (§6).

## §4 No `sorry` / axiom / `native_decide` (run locally)

Comments were stripped (block *and* line) before scanning, so prose mentioning the word
`sorry` — two module headers discuss the scaffold this development superseded — cannot mask
or fake a result:

```
import closure of Sendov9.Final: 45 modules
CODE-LEVEL HITS (comments stripped): 0
```

for the patterns `sorry`, `sorryAx`, `native_decide`, `^axiom `, `@[implemented_by`,
`unsafe`.

**The decisive check is not this scan.** Any `sorry` anywhere in the transitive dependency
graph — including Mathlib's — surfaces as `sorryAx` in `#print axioms`. The footprint in §2
is therefore a complete proof that no `sorry` is reachable; the scan above is corroboration.

`Challenge.lean` contains exactly **two deliberate `sorry`s**. They are the Comparator audit
fixture — the statements without proofs — and live in a separate library that nothing else
imports. They are the only `sorry`s in this directory.

## §5 Statement fidelity

The risk Lean's kernel cannot address is a sound proof of a subtly *different* statement.
Two checks:

**(a) The trusted statements are character-identical to the development's.** Comparing the
signatures in `Challenge.lean` and `Solution.lean` against `Sendov9/Final.lean` (whitespace
normalized):

```
Challenge.lean  sendov_degree_nine           identical to Final.lean: True
Challenge.lean  sendov_degree_nine_general   identical to Final.lean: True
Solution.lean   sendov_degree_nine           identical to Final.lean: True
Solution.lean   sendov_degree_nine_general   identical to Final.lean: True
```

So `Solution.lean`'s proofs are term assignments at literally the same type; there is no
transport lemma and no room for a coercion to weaken the statement. This is stronger here
than in the other solutions in this repository, because the statement uses **no
project-specific definitions at all** — only `Polynomial.roots`, `Polynomial.derivative`,
`Polynomial.natDegree` and the norm on `ℂ`, all Mathlib's own. That is also why
`comparator/all.json` carries no `definition_names` entry and why there is no
`Statement.lean`: `Challenge.lean` plus Mathlib is the entire audit surface.

**(b) Negative control — RUN, three failures as required.** Three deliberately wrong
variants must fail to elaborate: radius `1/2` instead of `1`; strict `<` instead of `≤`;
and dropping the degree hypothesis. Run against the development tree (`lake env lean` on
the probe reproduced as `_negcontrol.lean`), the actual output was **exactly three
errors**:

```
NegControlProbe.lean:17:2: error: Type mismatch
  Sendov9.Final.sendov_degree_nine_general hdeg hroots ha
has type
  ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1
but is expected to have type
  ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1 / 2

NegControlProbe.lean:23:2: error: Type mismatch
  Sendov9.Final.sendov_degree_nine_general hdeg hroots ha
has type
  ∃ z ∈ (derivative p).roots, ‖a - z‖ ≤ 1
but is expected to have type
  ∃ z ∈ (derivative p).roots, ‖a - z‖ < 1

NegControlProbe.lean:29:43: error: Application type mismatch: The argument
  hroots
has type
  ∀ w ∈ p.roots, ‖w‖ ≤ 1
but is expected to have type
  natDegree ?m.42 = 9
```

So the constant `1`, the direction of the inequality, and the degree hypothesis are each
load-bearing: no coercion or defeq silently weakens the statement. Note that this check
tests the *reasoning* in (a) rather than adding independent evidence — its outcome was
already fixed by the signatures being character-identical. The adversarial check is
Comparator (§7).

## §6 Non-vacuity

A theorem with unsatisfiable hypotheses proves nothing, and `#print axioms` cannot detect
that. This is not hypothetical here: the one genuine defect found during the formalization
was a carried hypothesis that was **vacuously true** at `n = 0`, which would have
trivialised every dependent theorem silently (`Sendov9/GWSFix.lean` contains the refutation,
`not_graceWalshSzego`). Everything targets the corrected `GraceWalshSzegoPos`.

`Sendov9/NonVacuous.lean` therefore applies the main theorem to `p = X⁹` and obtains an
actual critical point:

```
'Sendov9.NonVacuous.sanity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## §7 Comparator

**Linux-only** (landrun / Landlock sandbox); **NOT run on this platform (Windows).** Runs on
CI in `.github/workflows/sendov9-comparator.yml`, which builds pinned `comparator`,
`lean4export` (matched to Lean v4.31.0) and `landrun`, probes that the sandbox actually
denies out-of-policy writes, and then runs two configs — both with permitted axioms
`propext`, `Quot.sound`, `Classical.choice` only:

- `comparator/sendov9_general.json` — `sendov_degree_nine_general`, axiom-free.
- `comparator/sendov9_monic.json` — `sendov_degree_nine`, axiom-free.

The workflow requires the string `Your solution is okay!` twice. That job deliberately does
**not** pre-build `Challenge` or `Solution`: Comparator's threat model assumes the solution
has not been compiled beforehand. **Its result is the authoritative check and supersedes
§2/§4/§5 if they ever disagree.**

**Result: PASSED**, on commit `e547beb`
([run 30390230659](https://github.com/antoshashakov/Principia-Math-Solutions/actions/runs/30390230659),
2026-07-28, 21 minutes). Every step succeeded, including the sandbox self-test:

```
landrun denies out-of-policy writes (rc=2)
=== comparator on comparator/sendov9_general.json ===
Your solution is okay!
=== comparator on comparator/sendov9_monic.json ===
Your solution is okay!
comparator 'okay' count: 2 (expected 2 — general + monic)
comparator accepted both configs
```

The sandbox self-test matters: if landrun silently no-opped, a Comparator pass would mean
nothing, so the workflow refuses to trust the result unless an out-of-policy write is
actually denied first.

**Note on the companion `sendov9-build` run for `e547beb`:** it reported *failure*, and the
failure was in this repository's own CI assertion, not in the Lean. Every substantive step
passed there — the library built, `Solution` built, no declaration used `sorry`, and all 744
footprints were inside `{propext, Classical.choice, Quot.sound}`, with

```
'Sendov9.Statement.sendov_degree_nine'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Sendov9.Statement.sendov_degree_nine_general' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The failing step asserted that `solution.log` holds exactly two footprint lines; it holds
372, because `lake build Solution` replays the cached info messages of every dependency.
Fixed in the following commit by matching on the declaration name instead of counting.

## §8 The paper

Committed as supplied by the author and pinned by sha256:

```
c164b5f1e0d046e0e6f1a22d1f60eaff72b81e6881cd696babfba79839f78c83  paper/sendov9.tex
5a09b83cac6353ca333ef8cd7a5c7ed01c6e5c6ad53a7f5e4537e2e94ba15aa1  paper/sendov9.pdf
```

Unlike `erdos361/`, there is **no paper-rebuild workflow** here, deliberately: recompiling
the PDF in CI would replace the author's bytes with CI-built ones and break exactly the
provenance the hash is there to provide.

## §9 Deliberately excluded

- The paper's ancillary Python verifiers (`verify_interior.py`, `verify_boundary.py`) are
  not part of this repository and are not used. The certificates are re-derived and checked
  by Lean's kernel instead.
- The development repository's superseded Stage-0 scaffold (`Skeleton.lean`, which still
  carries its original `sorry`s and is imported by nothing) was **not** copied here.
- The website publication step of the project's solution SOP has **not** been performed.

## §10 Reproduction

```sh
# Build and audit (Linux, macOS or Windows):
cd sendov9
lake exe cache get
lake build            # the Sendov9 library
lake build Solution   # prints the two #print axioms lines
lake build Challenge  # two intentional sorries

# Negative control (must FAIL to elaborate, three times):
lake env lean _negcontrol.lean

# Comparator (Linux only; see .github/workflows/sendov9-comparator.yml for the pins):
lake env <comparator> comparator/sendov9_general.json
lake env <comparator> comparator/sendov9_monic.json
```
