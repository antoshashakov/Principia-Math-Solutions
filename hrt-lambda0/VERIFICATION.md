# VERIFICATION — HRT at Λ₀, the endgame (CONDITIONAL)

The honest ledger. Every claim below is either a command that was run with its actual
output recorded, or an explicit note that it was **not** run and where it *is* run.

The result claimed is:

```lean
theorem HRTLambda0.Statement.lambda0_independent_of_reduction {g : ℝ → ℂ}
    (h : HRTLambda0.ZakReduction g) : HRTLambda0.Lambda0Independent g
```

with `#print axioms` showing exactly `[propext, Classical.choice, Quot.sound]`.

## §1 Scope — read this first

- **The theorem is CONDITIONAL.** Its hypothesis `ZakReduction g`
  (`HRTLambda0/Statement.lean`) packages the paper's entire pre-endgame analysis — the
  Zak-transform reduction, the fibre dichotomy, the degree identity at `j = 0`, and
  Jensen's formula on the fibre — and **none of that is proved in this repository**.
- **Therefore the HRT subconjecture at `Λ₀` (Heil 2006 Conjecture 9.2(a) /
  Heil–Speegle Conjecture 2) is NOT claimed unconditionally here.** What is
  machine-checked is the paper's *endgame*: that the reduction suffices. The paper
  (`paper/hrt-lambda0.tex`) argues the reduction for every window whose Zak transform
  has a continuous representative (in particular every nonzero Schwartz window); that
  analysis is on paper, not in Lean.
- **Mathematical attribution**, as recorded in the paper itself: the fibration of `𝕋²`,
  the zero-propagation dichotomy and the winding identity are due to Oussa (cited in the
  paper as arXiv:2508.04613v2); the paper's own contribution — what is formalized here —
  is the Jensen-constancy + Vieta-rigidity contradiction, plus the continuity-free
  strengthening `circle_pair_quadratic`.
- **An honest caveat about conditional theorems:** `ZakReduction g` is an implication
  (`¬ independent → ∃ …`), so it holds *vacuously* for any window whose translates are
  already independent. The formalization's value is that it machine-checks the endgame
  *reasoning* — the step every window class must pass through — not that the hypothesis
  is hard to satisfy. A skeptic should read the definition of `ZakReduction` and decide
  whether it faithfully transcribes the paper's §Reduction; that transcription is the
  trust boundary of this folder.
- **No `sorry`** outside the single deliberate placeholder in `Challenge.lean`; **no
  declared axiom** anywhere in this directory.

## §2 The build

**Environment.** Lean `leanprover/lean4:v4.31.0`; Mathlib `rev
fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (tag `v4.31.0`), pinned in
`lake-manifest.json` — identical pins to `sendov9-11/`.

**Where the authoritative build runs: CI.** `.github/workflows/hrt-lambda0-build.yml`
builds the `HRTLambda0` library, then `Solution`, then `Challenge`, and asserts: no
`declaration uses 'sorry'` in the development or Solution logs; no axiom outside the
permitted triple in any footprint (this also catches `sorryAx`); the headline result
carries the clean triple; no `native_decide` / `implemented_by` / `unsafe` / `axiom`
declaration; and `Challenge.lean` has exactly one `sorry`. **Not yet run at commit
time** — it triggers on this push.

**Locally (Windows), RUN — the monolithic development file.** The development was
written and certified as a single file; before this folder was assembled it was
kernel-checked in the certification environment (same toolchain and Mathlib pins),
2026-08-05, `lake env lean HRTLambda0.lean` → **exit 0**, actual output in full:

```
'HRTLambda0.lambda0_symplectic_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.zero_propagates' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.fibre_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.degree_identity_kills' depends on axioms: [propext, Quot.sound]
'HRTLambda0.two_of_three_eq_of_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.circle_pair_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.hrt_endgame' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.lambda0_independent_of_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(`degree_identity_kills` legitimately needs only `[propext, Quot.sound]` — it is pure
integer arithmetic by `omega`.)

**Locally (Windows), RUN — this folder's split layout.** For this repository the file
was split into `HRTLambda0/Statement.lean` (definitions, byte-identical) +
`HRTLambda0/Endgame.lean` (theorems, byte-identical bodies) + `Challenge.lean` +
`Solution.lean`. Each module was then kernel-checked in dependency order with
`lake env lean` under the same pins (see §3 for the recorded log). This is what
establishes that the split introduced no drift.

## §3 The split check — actual output

Sequential `lake env lean` on `Statement` → `Endgame` → build root → `Challenge` →
`Solution`, 2026-08-05:

```
== Statement ==
STATEMENT_EXIT=0
== Endgame ==
'HRTLambda0.lambda0_symplectic_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.zero_propagates' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.fibre_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.degree_identity_kills' depends on axioms: [propext, Quot.sound]
'HRTLambda0.two_of_three_eq_of_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.circle_pair_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.hrt_endgame' depends on axioms: [propext, Classical.choice, Quot.sound]
'HRTLambda0.lambda0_independent_of_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
ENDGAME_EXIT=0
== Root ==
ROOT_EXIT=0
== Challenge ==
hrtcheck\Challenge.lean:34:8: warning: declaration uses `sorry`
CHALLENGE_EXIT=0
== Solution ==
'HRTLambda0.Statement.lambda0_independent_of_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
SOLUTION_EXIT=0
```

Exits all 0; `Challenge` reports exactly its one deliberate `sorry`; `Solution` reprints
the clean footprint for `HRTLambda0.Statement.lambda0_independent_of_reduction`; the
`Endgame` footprints are **identical** to the monolithic file's (§2), so the split
introduced no drift.

## §4 Statement fidelity

The risk Lean's kernel cannot address is a sound proof of a subtly *different*
statement. Mitigations:

- The definitions in `HRTLambda0/Statement.lean` are copied **verbatim** from the
  certified development file; the theorem in `Challenge.lean` is stated at literally the
  type `ZakReduction g → Lambda0Independent g`, and `Solution.lean` proves it by a
  **direct term assignment** from the development — no transport lemma, no coercion.
- `comparator/all.json` therefore carries `definition_names` for all five
  project-specific definitions (`tfTranslate`, `configTranslates`, `lambda0Translates`,
  `Lambda0Independent`, `ZakReduction`): Comparator checks the definitions as well as
  the theorem.
- **Negative control: NOT run** for this folder. The statement's load-bearing pieces are
  the five definitions, which Comparator audits directly; a perturbation control in the
  style of `sendov9-11/`'s §5(b) has not been constructed here and this ledger says so
  rather than implying otherwise.

## §5 Comparator

**Linux-only** (landrun / Landlock sandbox); **NOT run on this platform (Windows) and
not yet run on CI at commit time.** `.github/workflows/hrt-lambda0-comparator.yml` runs
`comparator/all.json` on push with permitted axioms exactly
`propext / Quot.sound / Classical.choice` and requires `Your solution is okay!`. Note
what a pass will and will not mean: it certifies statement fidelity and the axiom
footprint of the **conditional** theorem; it cannot upgrade a conditional theorem to an
unconditional one.

## §6 The paper

The `.tex` is committed as supplied; the `.pdf` was built from that exact `.tex` with
`pdflatex` (two passes, exit 0 both) on the certification machine, 2026-08-05 — unlike
`sendov9-11/paper/`, the PDF here is a build product, not author-supplied bytes, and
this ledger says so. Pins:

```
1a886f0739941407d84a2bb78fb80f1ff5d3ca31acccf37bab2062cd0223244b  paper/hrt-lambda0.tex
a66a23a3d929ce03907c184eabd0f95a300ae334448c37b52c13612ad9fc1513  paper/hrt-lambda0.pdf
```

## §7 Deliberately excluded

- The wider Lean campaign attacking `ZakReduction` itself (Zak transform as an `L²`
  object, shift covariance, Birkhoff/cocycle machinery) lives in the private
  development repository and is **not** part of this folder; nothing here depends on it.
- A second, stronger manuscript claiming the result for **every** nonzero `g ∈ L²`
  exists in draft. It has not passed the same audit as `paper/hrt-lambda0.tex` and is
  **not** committed here; this folder's claims are calibrated to the continuous-Zak
  paper only.
- The website publication step of the project's solution SOP has **not** been performed.

## §8 Reproduction

```sh
cd hrt-lambda0
lake exe cache get
lake build             # the HRTLambda0 library (Statement + Endgame)
lake build Solution    # prints the #print axioms line for the headline theorem
lake build Challenge   # one intentional sorry

# Comparator (Linux only; see .github/workflows/hrt-lambda0-comparator.yml for pins):
lake env <comparator> comparator/all.json
```
