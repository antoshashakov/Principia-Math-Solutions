# Verification ledger — Erdős Problem 883

Every claim below is either a command that was run with its actual output recorded,
or an explicit note that it was **not** run. Last updated: 2026-07-23.

## 1. What this folder claims — and what it does not

- **Claimed and proved (axiom-free):** the two sharpness statements of
  `Challenge.lean` (`erdos883_threshold_sharp`, `erdos883_ceiling_sharp`).
- **Stated but NOT proved:** the forcing direction
  `Erdos883.Statement.erdos883Forcing` — the actual content of the manuscript's
  Theorem 1.1 and of the Erdős–Sárközy conjecture. **No declaration in this
  repository proves it, and this folder must not be cited as a formal
  verification of the solve.**
- **The manuscript** (`paper/erdos883.tex`, `paper/erdos883.pdf`) is a
  harness-produced (GPT-5 side) claimed proof. Its referee status is §5.

## 2. Pinned artifacts

```
sha256(paper/erdos883.pdf) = 7C316BB150A3B86EA25F54B71E12D09417AB83C7A80329BE25555BA7FAE8DDCC
sha256(paper/erdos883.tex) = 7BB9FCB26C73580EE806904E82A7D7E340BDE3624700F2FEC741D586B56307EB
```

Toolchain: `leanprover/lean4:v4.31.0`; Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (tag v4.31.0).

## 3. Lean verification record

Local verification, 2026-07-23, on Windows against the LeanSandbox checkout of
Mathlib v4.31.0 (same rev as `lake-manifest.json`):

- The exact concatenated text of `Erdos883/Statement.lean` + `Erdos883/Core.lean`
  (bodies verbatim; imports narrowed from `import Mathlib` to the nine modules
  actually used, to fit local memory limits) was compiled with `lake env lean`:
  **0 errors, 0 warnings, 0 sorries**.
- Caveat: the local run used narrowed imports; the shipped files import all of
  Mathlib. The full-import `lake build` + `lake build Challenge Solution`
  (including the `Solution.lean` term-assignment layer) runs on CI
  (`.github/workflows/erdos883-build.yml`) and had **not** been run at commit
  time on this machine.

## 4. Axiom footprints

`#print axioms` on the same locally verified development:

```
'Erdos883.erdos883_threshold_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos883.erdos883_ceiling_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no extra axioms: both sharpness theorems are axiom-free.

## 5. Referee status of the manuscript (the claimed solve)

The manuscript rests on (i) an elementary combinatorial skeleton, (ii) two finite
exact-rational computations (Lemmas 4.1 and 5.2), and (iii) analytic prose
(Lemmas 3.1 connector, 3.2 deficient-vertex counts, 6.1 closing vertex, and the
`n < n₀` Moon–Moser regime).

**Independently recomputed (exact rational arithmetic, `referee/`):**

- `verify_lemma41.py` (output: `verify_lemma41.output.txt`) recomputes the
  2¹⁸-pattern multilinear expansion of Lemma 4.1 from scratch: it reproduces the
  manuscript's `C'_S = 8668.19… < 8669` exactly, obtains `E_S = 0.0262287…`, and
  **confirms the hinge inequality** `E_S + tail + C'_S/N_odd < 4351/150000` with
  exact rational margin `≈ 5.56·10⁻⁷`. Caveat: the margin is razor-thin — a tail
  majorant for `Σ_{p>71} p⁻²` certified past 10⁶ is required (the script sums
  primes to 10⁷ by ceiling-accumulation at scale 10⁴⁰ and bounds the remainder by
  `1/(2(B−1))` over odd integers). The manuscript's `β* ≤ 0.217020` follows:
  the recomputed bound is `0.2170183… < 0.217020`.
- `verify_lemma52.py` (output: `verify_lemma52.output.txt`) recomputes the
  independent-model main term of Lemma 5.2's CDF certificate across the full
  δ-range (1001-point exact sweep); worst margin ≈ 0.2223 (at δ ≈ 1.334) before
  finite-n/tail corrections, consistent with the manuscript's claimed 0.0873
  post-correction margin. The per-subinterval correction bookkeeping was **not**
  reproduced.
- Lemma 3.2's threshold constants (first deficient vertices `2P₀`, `3P₀`,
  `P₀ = 37 182 145`) were checked by hand.

**NOT independently verified:** the connector/transportation lemma (3.1) — whose
written proof is a sketch; the Rankin-argument constant `0.067` and Hall-ratio
`7.46` of Lemma 3.2; the Erdős–Wintner/CVaR transfer in Lemma 4.1's surrounding
argument; Lemma 6.1; and the entire `n < n₀` (`n₀ = 74 364 290`) Moon–Moser
regime. The manuscript itself notes its independent checks (exhaustive `n ≤ 17`,
odd-length search to `n = 72`, extremal configurations to `n = 12000`) are not
part of the proof.

**Conclusion:** the numerical core is genuine and reproducible; the paper as a
whole should be treated as a **plausible, partially-checked claimed proof**, not
a verified theorem, until the forcing direction is formalized or the prose is
fully refereed.

## 6. Comparator

Comparator was **not** run at commit time (configs in `comparator/`; CI pending).
