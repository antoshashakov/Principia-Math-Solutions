# VERIFICATION — Sendov's conjecture, degrees nine to eleven

The honest ledger. Every claim below is either a command that was run with its actual
output recorded, or an explicit note that it was **not** run and where it *is* run.

This directory contains two developments, and this ledger keeps them strictly apart:

- **Part I — degree nine: PROVED.** Unconditional, axiom-free, Comparator-certified on CI.
- **Part II — degrees ten and eleven: PROVED** (2026-08-06). The analytic reduction that
  was previously the explicit hypothesis `CertificateReduction` is now a **theorem** for
  both degrees (`Sendov1011/`), the finite certificate half is kernel-checked in full
  (degree 10: 51/51 boxes; degree 11: 531/531 **regenerated v2** boxes), and the two are
  wired through the unchanged capstone into
  `SendovN.Final10.sendov10 : Sendov911Capstone.Sendov 10` and
  `SendovN.Final11.sendov11 : Sendov911Capstone.Sendov 11`, each with axiom footprint
  exactly `[propext, Classical.choice, Quot.sound]`. Part II of this ledger was rewritten
  accordingly; the earlier PARTIAL ledger is in git history.

**The two parts do not yet have equal evidentiary standing, and this ledger does not
pretend otherwise.** Part I is Comparator-certified on CI and its whole closure is rebuilt
by the per-push job. For Part II, as of this commit: Comparator has **never been run** on
the four degree-10/11 statements (§20), the two workflows that rebuild the 582-certificate
corpus are **`workflow_dispatch` only and have not been dispatched** (§18), and the local
full rebuild of this packaged copy **was started and stopped short** (§18). The proof
itself was completed and audited in the development tree — that is what "PROVED" records
— and the files here are byte-identical copies (§13). What is outstanding is independent
re-verification *of this repository's copy*, not the mathematics.

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
  statement the paper does not make, and any assessment of the previous claimed proofs of
  Sendov's conjecture in the literature. Several exist, at these degrees and in general;
  none has been publicly accepted, none is used here, and this ledger takes no position on
  any of them.

## §2 The build

**Environment.** Lean `leanprover/lean4:v4.31.0`; Mathlib `rev
fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (tag `v4.31.0`), pinned in `lake-manifest.json`.

**Where the authoritative build runs: CI.** `.github/workflows/sendov9-11-build.yml` builds
the `Sendov9` library, then `Sendov1011` (Part II), then `Solution`, then `Challenge`, and
asserts:

1. no `declaration uses 'sorry'` anywhere in the `Sendov9`, `Sendov1011` or `Solution`
   build logs;
2. no axiom outside `{propext, Classical.choice, Quot.sound}` appears in *any* footprint
   across those logs (this also catches `sorryAx`);
3. `Solution`'s six results each carry the full clean triple;
4. no `native_decide` / `implemented_by` / `unsafe` / `axiom` declaration in
   `Sendov9/*.lean`, `Sendov1011/*.lean`, `boxes10/*.lean`, `boxes11v2/*.lean`,
   `Solution.lean`, `Challenge.lean`;
5. `Challenge.lean` has exactly six `sorry`s (the audit fixture — two per degree
   since the Part II completion; the checks 1–4 sweep the 10/11 logs too);
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

`Challenge.lean` contains exactly **six deliberate `sorry`s** (two at the time of the
Part I record above; the degree-10/11 statements added four more). They are the Comparator
audit fixture — the statements without proofs — and live in a separate library that
nothing else imports. They are the only `sorry`s in this directory.

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

At the time of the recorded run below the workflow required the string
`Your solution is okay!` twice; since the degrees-10/11 completion it runs **four**
configs (§20) and requires it four times. That job deliberately does
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
lake build Solution   # the two degree-nine #print axioms lines; degree-nine closure only
lake build Challenge  # six intentional sorries (two degree-nine, four degree-10/11)

# Negative control (must FAIL to elaborate, three times):
lake env lean _negcontrol.lean

# Comparator (Linux only; see .github/workflows/sendov9-11-comparator.yml for the pins):
lake env <comparator> comparator/sendov9_general.json
lake env <comparator> comparator/sendov9_monic.json
```

---

# Part II — degrees ten and eleven (PROVED, unconditional)

Rewritten 2026-08-06, when the analytic reduction was proved in Lean and the two final
theorems landed. The earlier Part II (finite half checked, reduction ASSUMED) is in git
history and its claims remain accurate **about that earlier state**; every count below is
recomputed from the files actually shipped at this commit.

The results claimed are:

```lean
theorem SendovN.Final10.sendov10 : Sendov911Capstone.Sendov 10
theorem SendovN.Final11.sendov11 : Sendov911Capstone.Sendov 11
```

together with the Mathlib-vocabulary statement layer
(`Sendov1011/SendovNStatement.lean`, surfaced in `Challenge.lean`/`Solution.lean` as
`Sendov1011.Statement.sendov_degree_ten{,_general}` and
`sendov_degree_eleven{,_general}`), each with `#print axioms` exactly
`[propext, Classical.choice, Quot.sound]`, no carried hypotheses, and no `sorry` in the
import closure.

## §11 What changed relative to the earlier PARTIAL state

1. **The analytic half is now proved.** `CertificateReduction 10 boxes10` and
   `CertificateReduction 11 boxes11` — previously the named unproved hypothesis — are
   theorems (`Sendov1011/SendovNReduction10.lean`, `SendovNReduction11.lean`). The
   capstone (`Sendov911Capstone.lean`) is **unchanged**; the new development plugs into
   `sendov_of_reduction` exactly as designed.
2. **The degree-11 boxes were regenerated (v2).** The proof of the centered
   elementary-symmetric bound at `m = 4` formalized cleanly only in its Cauchy form,
   giving `c₄ = 1447/50` (≈ 28.94) instead of the paper's original Schoenberg value
   `70/3` (≈ 23.33). `1447/50` is *weaker* (larger), so the certificate polynomials
   changed and all 531 degree-11 certificates were **re-emitted and re-kernel-checked**
   with the new constant: `boxes11v2/` (531 files) replaces `boxes11/`, whose superseded
   70/3 set — 531/531 kernel-checked in its own right, logs in `certlogs1011/` — remains
   in git history. Degree 10 is untouched by this change.
3. **The paper was revised to match** (§17): the `c₄` entry of its degree-11 table
   (eq. `c11`) now reads `1447/50` with attribution to the Cauchy bound, and both
   ancillary degree-11 verifiers carry the same constant. The original paper bytes are in
   git history. This is a *weakening* of one constant, honestly recorded — the
   certificates verify against the weaker value, so nothing anywhere relies on `70/3`.

## §12 The development (`Sendov1011/`, 91 modules)

The analytic reduction is a port of the degree-9 chain, parametric in the degree where
possible. Hand-written core (each module named `SendovN*`):

- `Data/Core/Bridge/Sigma/JBound` — the counterexample data structure `DataN n`, the
  reciprocal normalization, localization, the integral identity, the σ spreading
  machinery and the J lower bound (the J bound is proved for **all** `n ≥ 1`).
- `Esp/Esymm/Esp10/Esp11` — the centered elementary-symmetric bounds: the easy cases
  (`c₂`, `c₃`, `c_N`), the roots-of-unity Cauchy extraction (`esymm_extract`, `esymm_le`),
  and the two per-degree c-tables. `Esp11` carries the decisive
  `c4_deg11 : ‖e₄(D)‖ ≤ (1447/50)·η⁴` (via `EspCauchy.c4_deg11`).
- `Sep10/Sep11` — the separation constants, reached algebraically (tenth roots of unity
  through the golden-ratio branch `t² − t − 1`; eleventh roots through the quintic
  Laurent identity `ω⁵(t⁵+t⁴−4t³−3t²+3t+1) = ∑ωᵏ`), no trigonometry.
- `MidChain/Split11` — the reshaped Proposition 4.1 (`row_nonpos`) and its τ-split
  degree-11 form (`split_row_nonpos`).
- `Small10/Small11/CoverGrid/RotData/Statement` — small-range exclusion, the grid cover,
  rotation to a distinguished zero, and the Mathlib-vocabulary statement layer.
- The Grace–Walsh–Szegő chain is **reused from Part I** — `Sendov9/GWS.lean` is already
  parametric in `n`, so degrees 10 and 11 consume the same proved theorem (still no
  literature axiom anywhere).

Generated modules (emitters shipped in `scripts/`, see §13): `EInt` (closed-form
integrals, both limits free), `Rows10/Rows11` (per-row σ/L/λ/Y certificates),
`EmajEq` (folding the integral majorants into explicit polynomials), `BdryEq10/BdryEq11`
(the two boundary identities), `Red10A..E`, `Red10Bdry`, `Red11_37..89`, `Red11Bdry`
(per-row reductions wiring analytic facts to the box tables through exact `ring`
identities), `Covering10/Covering11` (the `CoveringPositive` folds over all 51 resp. 531
boxes), `Reduction10/Reduction11`, and the finals. Every generated file's box table was
regenerated from the verifier arithmetic and matched against the shipped box file
**integer-for-integer before emission**; each then elaborates through Lean's kernel like
any other module — generation is a convenience, not a trust step.

## §13 Provenance of the v2 data — emitters SHIPPED, cross-check RUN here

The earlier ledger honestly recorded that the degree-11 v1 emitters were not preserved
and that v1 was cross-checked on a 5-box sample only. **Both gaps are closed for v2:**

- The emitter that produced every `boxes11v2/` file is shipped
  (`scripts/emit_boxes11v2.py`, with its per-box τ/margin table
  `scripts/boxes11v2-tau.csv`); its arithmetic is line-for-line
  `certificates/degree11_verify.py` with the single constant change, and per box it
  asserts the exact margin against the recorded value before writing.
- An independent parser-based cross-check (`scripts/crosscheck_boxes11v2.py`) — it reads
  the emitted Lean files back, trusts nothing from the emitter's construction, and
  re-verifies `hQ`, `cnum > 0`, and every Bernstein numerator on Python
  integers/fractions — was **run in this repository against the shipped files**
  (2026-08-06, log `certlogs11v2/crosscheck-repo.log`):

```
531/531 checked
ALL 531 FILES PASS: hQ, cnum>0, every Bernstein numerator >= cnum (min tight), margins match the c4 experiment exactly.
worst margin 4.344719e-03 in Sendov911Box11_79_8.lean
```

- The other emitters (`scripts/emit_eint1011.py`, `emit_rows1011.py`,
  `emit_emajeq1011.py`, `emit_assembly1011.py`) are shipped as supplied from the
  certification machine; their internal self-checks (identity re-verification at random
  rational points by independent evaluation routes; byte-matching of every consumed box
  table) are described in their headers. They expect the certification machine's flat
  working-directory layout, which differs from this repository's (`boxes10/` files at the
  root, etc.); they are provenance artifacts, not part of any build.
- The paper's own verifiers in `certificates/` remain the independent ground truth,
  re-run for v2 (§15).

## §14 Negative controls

The four `decide`-level controls of the earlier ledger (`controls/`, three rejected as
required, one honestly recorded as badly designed) are unchanged and still apply: the
engine (`Sendov911Bern`) and the box-file shape are identical in v2. In addition, the
degree-9 statement-level negative control (§5b) covers the statement layer shared by all
six headline theorems — the four new statements are character-identical in shape to the
degree-9 pair up to the degree numeral (§16).

## §15 Results — recomputed from the shipped logs

Every log counted below ends with
`depends on axioms: [propext, Classical.choice, Quot.sound]`.

| item | count | evidence |
| --- | --- | --- |
| degree 10 interior + boundary boxes | **51/51** | `certlogs1011/` (unchanged from the earlier ledger) |
| degree 11 **v2** interior + boundary boxes | **531/531** | `certlogs11v2/*.log`, one per box; `certlogs11v2/RESULTS11V2.txt` = 531 lines, all exit 0 |
| v2 cross-check (independent parse-and-reverify) | **531/531 PASS** | `certlogs11v2/crosscheck-repo.log`, run in this repo |
| primary Python verifier re-run at `c₄ = 1447/50` | 530 interior, **0 fails** + boundary | `certificates/degree11_verification_log.txt` (2026-08-06) |
| independent SymPy reconstruction at `c₄ = 1447/50` | **530 interior PASSED + boundary PASSED**, minima matching the shipped margins exactly | `certificates/degree11_independent_check.log` (2026-08-06) |

On the certification machine every box additionally went through a **second kernel
pass**: the olean builds for the assembly layer re-elaborated each box file's `decide`s
(promoted only on exit 0 plus a clean-axioms grep), on top of the one-at-a-time
certification batch recorded in the logs above. `sorryAx` appears in no footprint
anywhere.

The final theorems, as re-elaborated fresh on the certification machine over the complete
olean DAG (statement layer `Sendov1011/SendovNStatement.lean`, same command shape as
`check-boxes11v2.sh`, i.e. `lake env lean` after `lake env printenv LEAN_PATH`):

```
'SendovN.Final10.sendov10' depends on axioms: [propext, Classical.choice, Quot.sound]
'SendovN.Final11.sendov11' depends on axioms: [propext, Classical.choice, Quot.sound]
'SendovN.Final10.sendov_degree_ten' depends on axioms: [propext, Classical.choice, Quot.sound]
'SendovN.Final10.sendov_degree_ten_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'SendovN.Final11.sendov_degree_eleven' depends on axioms: [propext, Classical.choice, Quot.sound]
'SendovN.Final11.sendov_degree_eleven_general' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## §16 Statement fidelity (degrees 10/11)

Same check as §5: comparing the four new signatures in `Challenge.lean` and
`Solution.lean` against the development's `Sendov1011/SendovNStatement.lean`
(whitespace-normalized), run 2026-08-06:

```
Challenge.lean  sendov_degree_ten              identical to SendovNStatement.lean: True
Solution.lean   sendov_degree_ten              identical to SendovNStatement.lean: True
Challenge.lean  sendov_degree_ten_general      identical to SendovNStatement.lean: True
Solution.lean   sendov_degree_ten_general      identical to SendovNStatement.lean: True
Challenge.lean  sendov_degree_eleven           identical to SendovNStatement.lean: True
Solution.lean   sendov_degree_eleven           identical to SendovNStatement.lean: True
Challenge.lean  sendov_degree_eleven_general   identical to SendovNStatement.lean: True
Solution.lean   sendov_degree_eleven_general   identical to SendovNStatement.lean: True
```

As in Part I the statements are pure Mathlib vocabulary (`Polynomial.roots`,
`Polynomial.derivative`, `Polynomial.natDegree`, the norm on `ℂ`) — no project
definitions, hence no `definition_names` in the comparator configs. The bridge from the
capstone's `Sendov n` shape (`(derivative p).IsRoot ζ`) to roots-membership is
`Polynomial.derivative_ne_zero` plus `Polynomial.mem_roots`; the non-monic forms scale by
`leadingCoeff⁻¹` exactly as in degree 9.

Provenance of the copied modules, verified with `cmp` against the certification
machine's gated originals at commit time:

```
dev modules compared: 91, differing: 0
boxes11v2 compared: 531, differing: 0
```

## §17 The degrees 9–11 paper — REVISED (v2), and why

The paper was **revised in this repository** on 2026-08-06: the degree-11 coefficient
majorant `c₄` in eq. (c11) changed from `70/3` (Schoenberg) to `1447/50` (a rational
upper bound for the Cauchy bound, `1447/50 ≥ √(10¹⁰/(4⁴·6⁶))`), with a parenthetical in
the text recording the change. This is the constant the shipped certificates and the
Lean development actually verify against.

The same revision also **corrected the paper's quoted degree-11 interior certificate
floor** from `> 1/2800` to `> 1/4000`, in the prose and in the degree-11 row of Table 1.
`1/2800` is true only for the certificates as shipped in `boxes11v2/`, whose per-box `τ`
is the *best-margin* choice recorded in `scripts/boxes11v2-tau.csv` (worst interior
margin ≈ `4.3447·10⁻³`, at box `79_8`, `τ = 3/5`). The bundled verifier
`certificates/degree11_verify.py` selects instead the **first** `τ` of a fixed preference
order that already makes the box positive, and its own shipped log
`certificates/degree11_verification_log.txt` therefore ends at a smaller global minimum,
≈ `2.6419·10⁻⁴` (box `55_8`, `τ = 13/20`) — below `1/2800`. Both minima were recomputed
here exactly in Python fractions (the verifier was re-run in full: `boxes 530 fails 0`,
same exact rational as the shipped log), and both exceed `1/4000 = 2.5·10⁻⁴`, so the
revised floor is the one both `τ` selections satisfy. A clarifying sentence in the paper
now states which selection the recorded `τ` values are and that the bundled verifier's
first-positive selection yields a smaller but still positive minimum. The boundary claim
(`> 3/50`, actual ≈ `6.44·10⁻²`) is unchanged and remains true.

No other mathematical constant changed. The PDF was rebuilt from the revised source with
two `pdflatex` passes (both exit 0). The **original** tex/pdf (sha256
`dab64cb4…`/`389874af…`) are in git history, at `HEAD` as of this revision; the
intermediate `c₄`-only state (sha256 `0fd76832…`/`2b027535…`), which still carried the
`1/2800` figure, was never committed and is superseded by the pins below.

Current pins (also in `certificates/SHA256SUMS`, which was re-pinned and re-verified
with `sha256sum -c` — all OK):

```
d2d91f7bb1d1a29b190cff29957fff3f6a0f95ee70a8fefb2ea6996f6da9725c  paper/sendov9-11.tex
787f16ebb975bb06d1206876f8ff9c547185d3f083d18907505d677395f33a80  paper/sendov9-11.pdf
```

Note this weakens Part I's §8 provenance posture for THIS paper only (the degree-9 paper
`sendov9.tex`/`.pdf` is untouched and keeps its original author-supplied bytes): the
committed `sendov9-11.pdf` is now built on the verification machine from the committed
tex, because pinning author bytes that contradict the shipped certificates would have
been the greater dishonesty.

## §18 The build and CI posture for Part II

**Environment**: unchanged — Lean `leanprover/lean4:v4.31.0`, Mathlib
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (tag `v4.31.0`), byte-identical pins to the
certification machine's project.

**Layout.** The development keeps the certification machine's flat module names
(byte-identical files, §16); `lakefile.toml` registers them through three glob
libraries — `Sendov1011` (the 91 development modules), `Sendov911Boxes10` (51),
`Sendov911Boxes11` (531, `srcDir = boxes11v2`) — none of them default targets, so plain
`lake build` still builds exactly the certified degree-nine library.

**CI is split three ways, because the full closure does not fit a free runner.** The
degrees-10/11 closure measures ~13.5 CPU-hours of `decide` and `ring`, against GitHub's
hard 360-minute job ceiling on a 4-vCPU `ubuntu-latest`. So:

- `.github/workflows/sendov9-11-build.yml` — **the fast per-push job**. Builds `Sendov9`,
  `Solution`, the three Mathlib-only framework libs, `Challenge`, and `Sendov1011Core`
  (the 21 box-independent modules of the degrees-10/11 development), then sweeps the logs
  with the same no-sorry/no-foreign-axiom assertions as Part I. It does **not** build
  `Sendov1011` or `Solution1011`: their import closure is all 582 certificates. It also
  asserts that the four degree-10/11 statements are still present in `Solution1011` and
  that `Sendov1011Core` is still a registered library, so a broken dispatch-only workflow
  cannot hide until someone dispatches it. Timeout 180 minutes.
- `.github/workflows/sendov1011-boxes.yml` — **`workflow_dispatch` only**. Re-checks all
  582 certificates, matrix-sharded twelve ways. This is the load-bearing CI evidence for
  the corpus.
- `.github/workflows/sendov1011-full.yml` — **`workflow_dispatch` only**. The whole proof
  end to end in one job: `Sendov1011`, `Solution1011`, the four axiom footprints, then
  Comparator on `comparator/sendov10.json` and `comparator/sendov11.json`. Its own header
  records the honest warning that it may exceed the runner ceiling (realistic range
  230–345 minutes against the hard 360), and what the fallbacks are.

So the earlier "box certificates are exempt from CI" caveat is **narrowed, not gone**:
they are exempt from the *per-push* job and covered by a dispatch-only job. Neither
dispatch-only workflow has been run yet — see §20.

**Locally (Windows):** `lake build Sendov1011 Solution Challenge IntegrationCheck` from a
cold `.lake/` in this repository, which validates the lakefile wiring, the flat-name glob
resolution, and re-elaborates every module from source independently of the development
tree the proof was completed in. **This run is INCOMPLETE as of this commit** — see below.

<!-- LOCALBUILD -->

**Local full-corpus rebuild of the packaged copy: STARTED, NOT FINISHED (2026-08-06).**
Run from a cold `.lake/` in this repository, `LEAN_NUM_THREADS=4`, 08:43–11:38 local:

| | |
| --- | --- |
| modules completed | 403 |
| CPU-hours consumed | 14.72 (2.92 wall hours, 5.05× effective parallelism) |
| `boxes10/` | **51/51** |
| `SendovNRed10A..E` + `SendovNRed10Bdry` | **6/6** |
| `SendovNCovering10`, `SendovNReduction10` | **built** |
| `boxes11v2/` | **285/531** |
| `SendovNRed11_*` | **26/53** |
| `SendovNCovering11`, `SendovNReduction11`, `SendovNStatement`, `Solution1011` | **not reached** |
| errors | 0 |
| `sorryAx` occurrences | 0 |
| axiom lines emitted | 2494, all `[propext, Classical.choice, Quot.sound]` |

The run was **stopped deliberately, not by a failure**: four concurrent workers put the
machine at 92% of its commit limit (47.5 / 51.4 GB) with 1.2 GB of physical RAM free, a
single `SendovNRed11_*` elaboration having been measured holding 10.5 GB of private
commit. That is the same memory-exhaustion condition that killed an earlier degree-11
batch with `bad_alloc`. `build1011.sh` now pins `LEAN_NUM_THREADS=2` for the resume.
Lake is resume-safe: the completed oleans persist and a rerun continues from them.

**What this does and does not establish.** It establishes that the packaged copy's
lakefile wiring and flat-name glob resolution are correct, and that everything it did
reach elaborates clean from source. It does **not** yet establish an end-to-end rebuild of
the degrees-10/11 proof *in this repository*. The proof itself was completed and audited
in the development tree (§15, §16) — including a fresh re-elaboration of both final
theorems against the complete olean DAG — and the files here are byte-identical copies
(§13). Until either this local run or `sendov1011-full.yml` completes, the end-to-end
rebuild of the packaged copy is **pending**, and this ledger says so rather than implying
otherwise.

## §19 Non-vacuity (degrees 10/11)

Part I's §6 lesson (a vacuously-true carried hypothesis is invisible to
`#print axioms`) is addressed structurally in Part II: the former carried hypothesis is
now itself proved, and `IntegrationCheck.lean` continues to build against real boxes.
The statements quantify over the same hypotheses as degree nine's, whose satisfiability
`Sendov9/NonVacuous.lean` witnesses at `p = X⁹`; the degree-10/11 hypotheses are
satisfiable by the same construction (`p = Xⁿ`). No additional per-degree non-vacuity
module is shipped; this is the one Part I check without a Part II twin, recorded here
rather than papered over.

## §20 Comparator (degrees 10/11)

**NOT YET RUN. Comparator has certified the two degree-nine statements only (§7); the
four degree-10/11 statements have never been through it.** Nothing in Part II may be
described as Comparator-certified.

The configs are written and shipped — `comparator/sendov10.json` and
`comparator/sendov11.json` (each naming the monic and general forms for its degree),
plus `comparator/all1011.json` naming all four. All three name `Solution1011` as
`solution_module` and the same shared `Challenge` as `challenge_module`; permitted axioms
are exactly `propext`, `Quot.sound`, `Classical.choice`; no `definition_names`, for the
same reason as Part I (§16 — the statements use only Mathlib vocabulary).

`sendov9-11-comparator.yml`, the per-push comparator job, is deliberately scoped to
**degree nine only**. Comparator's threat model assumes the solution has not been
compiled beforehand, so that job does not pre-build `Challenge` or `Solution` — which
means running it over `Solution1011` would make the first config pay for the entire
~13.5-CPU-hour closure from scratch, well past GitHub's hard 360-minute ceiling. The
degree-10/11 configs are therefore run by `sendov1011-full.yml` (`workflow_dispatch`),
which has not been dispatched.

Two honest caveats about that job when it is run. It **pre-builds** the solution, which
is a real weakening of Comparator's threat model — it is the only way two configs over a
13.5-CPU-hour closure fit in one job at all. Comparator still re-elaborates and exports
both environments inside the landrun sandbox, so the comparison itself is unchanged; what
is lost is the guarantee that no earlier step primed the build. And it may still exceed
the ceiling, in which case the fallbacks are a paid larger runner or the sharded
`sendov1011-boxes.yml`.

**Why this matters here.** Comparator is the only check that what was proved is
*definitionally the statement in `Challenge.lean`* rather than something adjacent to it.
§16 argues fidelity by inspection and the term-assignment elaboration in `Solution1011`
forces definitional equality at build time, which is strong — but it is not the
adversarial, sandboxed, independently-exported check that Part I has and Part II does not.
That gap is the single largest difference in evidentiary standing between the two parts.

## §21 Reproduction (Part II)

```sh
cd sendov9-11
lake exe cache get
lake build Sendov1011        # the ENTIRE degrees-10/11 proof (~13.5 CPU-hours)
lake build Solution          # the two DEGREE-NINE #print axioms lines
lake build Solution1011      # the four DEGREE-10/11 lines; NOT pulled in by Sendov1011
lake build IntegrationCheck  # the capstone wiring demo

# On a memory-constrained machine, cap concurrency first: Lake 5.0.0 has no --jobs
# option, and LEAN_NUM_THREADS governs its job count as well as per-worker threading.
# A single SendovNRed11_* elaboration was measured at 10.5 GB of private commit.
#   export LEAN_NUM_THREADS=2      # or use ../build1011.sh, which is resume-safe

# Re-check the box certificates one file at a time (resume-safe):
./check-boxes.sh 10          # degree 10 (boxes10/, logs to certlogs1011/)
./check-boxes11v2.sh         # degree 11 v2 (boxes11v2/, logs to certlogs11v2/)

# Independent ground truth (exact rational arithmetic, no Lean involved):
cd certificates && sha256sum -c SHA256SUMS && python3 degree11_verify.py
cd .. && python3 scripts/crosscheck_boxes11v2.py boxes11v2/*.lean
```
