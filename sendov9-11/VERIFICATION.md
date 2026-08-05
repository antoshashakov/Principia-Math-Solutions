# VERIFICATION — Sendov's conjecture, degrees nine to eleven

The honest ledger. Every claim below is either a command that was run with its actual
output recorded, or an explicit note that it was **not** run and where it *is* run.

This directory contains two developments in **very different states**, and this ledger
keeps them strictly apart:

- **Part I — degree nine: PROVED.** Unconditional, axiom-free, Comparator-certified on CI.
  This is the only degree for which Sendov's conjecture is claimed.
- **Part II — degrees ten and eleven: PARTIAL.** The finite certificate half is
  machine-checked (degree 10 completely, degree 11 in progress); the analytic half is an
  explicit **hypothesis** (`CertificateReduction`), not a theorem. **Sendov's conjecture in
  degrees ten and eleven is NOT claimed.**

---

# Part I — degree nine (PROVED, unconditional)

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

**Where the authoritative build runs: CI.** `.github/workflows/sendov9-11-build.yml` builds
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
CI in `.github/workflows/sendov9-11-comparator.yml`, which builds pinned `comparator`,
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
cd sendov9-11
lake exe cache get
lake build            # the Sendov9 library
lake build Solution   # prints the two #print axioms lines
lake build Challenge  # two intentional sorries

# Negative control (must FAIL to elaborate, three times):
lake env lean _negcontrol.lean

# Comparator (Linux only; see .github/workflows/sendov9-11-comparator.yml for the pins):
lake env <comparator> comparator/sendov9_general.json
lake env <comparator> comparator/sendov9_monic.json
```

---

# Part II — degrees ten and eleven (PARTIAL: certificates checked, reduction ASSUMED)

Extends the Lean work to the finite certificate halves of the degrees-10/11 proof of
`paper/sendov9-11.tex`. Adapted from the development ledger of 2026-08-05, with every
count recomputed from the logs actually shipped in `certlogs1011/` at commit time.

## §11 What is and is not claimed

Two things are added, and neither of the paper's analytic gaps is closed:

1. **The finite half is machine-checked** (degree 10 completely, degree 11 partially).
   Every verified certificate below is discharged by Lean's kernel on exact integer
   arithmetic — no floating point, no `native_decide`, no `sorry`, no declared axiom.
2. **A conditional capstone exists.** `Sendov911Capstone.lean` names the analytic inputs
   in one predicate, `CertificateReduction`, and proves
   `CertificateReduction n boxes → CoveringPositive boxes → Sendov n`.

**Not claimed: Sendov's conjecture in degree ten or eleven.** The analytic reduction is a
hypothesis, not a theorem — see §16. Degree nine (Part I) is in a categorically different
position: unconditional, with Grace–Walsh–Szegő *proved*.

## §12 The engine and what each box file proves

`Sendov911Bern.lean` proves both directions of the Bernstein argument: the *bound*
direction (a table dominating `c > 0` forces positivity) and the *representation*
direction (`monomial_eq_bern`, the bivariate tensor-product change of basis), plus the
**integer bridge** (`intTable` / `cert_of_intTable`): supplying the cofactors as data makes
every kernel obligation an integer comparison, so `decide` runs on GMP-accelerated integer
arithmetic. Build: `lake build Sendov911Bern` → success (its olean is a prerequisite of
every box check).

For one box, `box_positive` states that the paper's certificate polynomial for that box,
pulled back to the unit square, is strictly positive there — exactly the assertion the
paper delegates to `certificates/degree10_verify.py` / `degree11_verify.py`. Per box the
kernel discharges two `decide` obligations: `hQ` (cofactors correct) and `hint` (every
integer Bernstein coefficient dominates `cnum > 0`).

## §13 Provenance of the data

The tables are **re-derived from the paper's own construction** — imported verbatim from
the committed verifiers in `certificates/` — then scaled to integers. Cross-check: for
every degree-10 interior box and the degree-10 boundary box, the emitted integer table was
checked against the verifier's rational Bernstein table entry-by-entry. For degree 11 the
same identity was spot-checked on **5 boxes only** (`37_0`, `38_5`, `39_9`, `55_3`,
`60_7`), all matching. **Degree 11 was cross-checked on a sample, not exhaustively.**

The emitter scripts themselves (`genlean10.py`, `genbound10.py`, `genlean11.py`,
`crosscheck11.py`) were **not preserved** — they were working files on the certification
machine and are not in this repository. The independent ground truth that *is* shipped is
`certificates/` (the paper's own verifiers, sha256-pinned in `certificates/SHA256SUMS`),
from which the tables can be re-derived.

## §14 Negative controls — RUN, recorded in `controls/`

`decide` succeeding is only meaningful if it can fail. Four perturbations of the degree-10
box `a ∈ [2/5, 41/100]`, shipped with their actual logs:

| control | perturbation | result |
| --- | --- | --- |
| NegA | demand a bound `10×` too large | `decide` proved the proposition **false** — rejected |
| NegB | *increase* the constant coefficient by `10²⁰⁰` | **passed** — and correctly so: raising the constant term raises every Bernstein coefficient. A badly designed control, recorded because it was run. |
| NegC | *decrease* the constant coefficient by `10²³⁰` | `hint` rejected |
| NegD | swap two cofactors in `Qdata` | `hQ` **and** `hint` both rejected |

## §15 Results — recomputed from the shipped logs

Every log counted below ends with
`depends on axioms: [propext, Classical.choice, Quot.sound]`.

| item | boxes | status |
| --- | --- | --- |
| degree 10, interior (`a ∈ [0.40,0.90]`, width 1/100) | 50 | **PASSED — 50/50**, all axiom-clean (`certlogs1011/Sendov911Box10_*.log`) |
| degree 10, boundary (bidegree 28×10) | 1 | **PASSED**, axiom-clean (`certlogs1011/boundary10.log`) |
| degree 11, interior (`a ∈ [0.37,0.90]` × 10 η-slices) | 530 | **329/530 verified** axiom-clean; **201 not yet checked** (run interrupted by memory exhaustion, not by any failure) |
| degree 11, boundary (`Sendov911Box11Boundary.lean`, bidegree 30×10) | 1 | **NOT RUN** — the file is shipped, its kernel check has never been executed |

So **degree 10's finite half is complete: 51/51. Degree 11's is partial: 329/531.** The
unchecked degree-11 boxes are contiguous: a-indices 68–70 (11 boxes) and 71–89 (10 each).

The non-zero exit codes in `certlogs1011/RESULTS11.txt` (one exit 1, two exit 127, one
exit 139, three exit 4) were all **infrastructure failures under parallel load** — the two
non-empty failing logs read `libc++abi: terminating due to uncaught exception of type
std::bad_alloc`, and the exit-1 box's log shows a `lake` subprocess crash before Lean ran;
that box passes when re-run alone. **No box has ever failed its `decide`.** To finish:
`./check-boxes.sh 11` (~53 s per box; do not exceed `-P 4`).

`IntegrationCheck.lean` wires two real boxes (`Box10_40` + `Box10Boundary`) into the
capstone's `CoveringPositive` list and derives `sendov10_of_reduction`. **RUN, 2026-08-05**
(single-file kernel check, `lake env lean`, after rebuilding `Sendov911Box10Boundary`'s
olean — both exit 0). Actual output, shipped as `certlogs1011/IntegrationCheck.lean.log`:

```
'IntegrationCheck.covering' depends on axioms: [propext, Classical.choice, Quot.sound]
'IntegrationCheck.sendov10_of_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

So the capstone wiring is kernel-checked; what `sendov10_of_reduction` proves remains
**conditional** on `CertificateReduction 10` (§16).

## §16 What is still assumed — the analytic half

`CertificateReduction` bundles, as an unproved hypothesis, everything between "the box
polynomials are positive" and "Sendov holds": Grace–Walsh–Szegő and the separation lemma
for degrees 10/11, the reciprocal-square extremum, variance-under-differentiation, the
centered elementary-symmetric bounds, the assembly of the certificate polynomial from the
integral identity, and — emphatically — that the boxes **cover** `a ∈ [0,1]` and that a
counterexample must land in one of them with a non-positive certificate value. None of
this is proved here for degrees 10/11. (Part I proves the degree-9 instances of these
steps; those proofs do not transfer automatically.)

`Sendov9to11.lean` (the earlier framework file) states
`PaperMainTheorem := Sendov 9 ∧ Sendov 10 ∧ Sendov 11` as a `def` and proves 19 supporting
lemmas; it concludes nothing and carries no `sorry`.

## §17 The degrees 9–11 paper

Committed as supplied and pinned by sha256 (also pinned, together with the verifiers, in
`certificates/SHA256SUMS`):

```
dab64cb4d6edb4ed59d7dc0aa11419342666af88a865f0d8486a930ef449675f  paper/sendov9-11.tex
389874af8ba634cac09e614917946704732d727e20fd481442177d570a3e015b  paper/sendov9-11.pdf
```

Note the paper *claims* degrees 9–11 with its §§5–8 analytic argument plus these
certificates; the Lean in this directory certifies the certificates (partially, for
degree 11) and **does not certify the analytic argument** for degrees 10/11.

## §18 CI posture for Part II

The `sendov9-11-build` workflow builds the three Mathlib-only framework libraries
(`Sendov911Bern`, `Sendov911Capstone`, `Sendov9to11`) and includes their footprints in the
axiom sweep. **The 581 box files are deliberately NOT built in CI** — at ~53 s per box that
is ~8.6 CPU-hours of `decide`, past the runner budget. Their evidence is the shipped
per-box logs (§15), reproducible one file at a time with `./check-boxes.sh`. Comparator
covers Part I only; there is no Comparator config for Part II because there is no
unconditional theorem to certify.

## §19 Reproduction (Part II)

```sh
cd sendov9-11
lake exe cache get
lake build Sendov911Bern Sendov911Capstone Sendov9to11   # the framework (Mathlib-only)
./check-boxes.sh 10        # re-check the 50 degree-10 interior boxes + resume logs
./check-boxes.sh 11        # check/resume the degree-11 boxes (201 outstanding)
lake build Sendov911Box10Boundary Sendov911Box11Boundary # the two boundary certificates
lake build IntegrationCheck                              # the capstone wiring

# Independent ground truth (the paper's own verifiers, pinned in certificates/SHA256SUMS):
cd certificates && sha256sum -c SHA256SUMS && python3 degree10_verify.py
```
