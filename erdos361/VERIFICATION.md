# VERIFICATION — Erdős Problem 361

The honest ledger. Every claim below is either a command that was run with its actual
output recorded, or an explicit note that it was **not** run (and where it is run instead).

- **Date:** 2026-07-23 (axiom-free upgrade; the former `alon_zero_sum` postulate is now proved)
- **Toolchain:** `leanprover/lean4:v4.31.0` (`lean-toolchain`)
- **Mathlib:** rev `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (= tag `v4.31.0`; `lake-manifest.json`)
- **Development platform:** the Lean was authored and elaborated on Windows against the same
  toolchain/Mathlib rev via a warm Lean REPL (see §4). `lake build` of this split project and
  the Comparator run are **Linux/CI operations** (§2, §6) — see the noted exceptions.
- **Paper bytes (sha256):**
  `e04454259412ac952f9f063c649d438aac971d7e3ff8ca4b07bab522dfc0202f  paper/erdos361.pdf`

## §1 Scope

Two headline results (see `Challenge.lean`), **both axiom-free**:

- `Erdos361.Statement.erdos361_cge1` — for `1 ≤ n ≤ M`, `F M n = M − ⌈n/2⌉`. Hence for
  `c ≥ 1`, `f_c(n)/n → c − 1/2`: the **regular** range.
- `Erdos361.Statement.erdos361_irregular` — for every real `c ∈ (0,1)`, `f_c(n)/n` does
  **not** converge (the Erdős–Graham irregularity question).

Both depend only on the three standard Lean/Mathlib axioms `[propext, Classical.choice,
Quot.sound]`. There is **no** external postulate (see §4).

## §2 The build

**NOT run on this platform (Windows).** `lake build` of the three-library split project runs
on CI in `.github/workflows/erdos361-build.yml` (`lake exe cache get` → `lake build` →
`lake build Challenge Solution`). The proof terms themselves were elaborated against the
pinned Mathlib rev via a warm REPL — see §4 for the actual `0 errors / 0 sorries` result on
the byte-identical concatenation of `Statement.lean` + the development + the `Solution.lean`
term assignments.

## §3 No `sorry` / axiom / `native_decide` (run locally)

```
$ grep -rn "sorry\|native_decide" Erdos361/*.lean Solution.lean
(no output)

$ grep -rh "^axiom " Erdos361/*.lean Solution.lean Challenge.lean | wc -l
0

$ grep -c "^  sorry$" Challenge.lean
2
```

The **only** `sorry`s in the repository are the two in `Challenge.lean` (the Comparator
fixture, one per result). There are **no** `axiom` declarations anywhere. No `native_decide`
/ `implemented_by` / `unsafe`.

## §4 Axiom footprints — both results axiom-free

Elaborated via warm Lean REPL against Mathlib `fabf563a`, on the byte-identical
Statement+development+Solution content (0 errors, 0 sorries), `#print axioms`:

```
'Erdos361.Statement.erdos361_cge1'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361.Statement.erdos361_irregular' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both are **axiom-free** (the three standard Lean/Mathlib axioms only).

**Alon 1987 Theorem 1.1 is now PROVED, not postulated.** Earlier revisions of this solution
carried a single external axiom `alon_zero_sum` — Alon 1987, *Subset Sums*, J. Number Theory
**27** (1987) 196–205, Thm 1.1. That postulate has been eliminated: `Erdos361/Core.lean`
proves the required bounded-zero-sum result **over a prime modulus** from scratch, via

- the general-`h` **Dias da Silva–Hamidoune** restricted-sumset bound `|A^∧h| ≥
  min(p, h(|A|−h)+1)`, built from Mathlib's `combinatorial_nullstellensatz` (the coefficient
  of the Alon–Nathanson–Ruzsa witness monomial in the Vandermonde × power polynomial is a
  falling-factorial determinant `= ∏_{i<j}(dⱼ−dᵢ)`, shown nonzero mod `p`);
- its **covering** corollary (`|A| > (1/k+ε)p ⟹ A^∧k = ℤ/pℤ ∋ 0`), giving Alon's Theorem 1.1
  over prime `p`;

and the irregularity conclusion is then assembled on the even subsequence `n = 2p` (`p`
prime — infinitely many), whose limsup stays strictly below the universal odd-`n` liminf
`c/2`. DSH is not in Mathlib; it is derived here. Every step is machine-checked with the
axiom footprint above.

## §5 Statement-fidelity interface check

`Solution.lean` proves each Challenge statement by **direct term assignment** from the
development (`Erdos361.erdos361_cge1`, `Erdos361.erdos361_irregular`). Because the
development imports `Erdos361.Statement`, the trusted `F`/`Fc`/`Avoids` and the development's
are the *same* definitions, so the term assignments type-check with no transport lemma. This
concatenation was elaborated to 0 errors (§4).

Negative control: replacing the irregularity conclusion by a deliberately stronger claim
(e.g. dropping `hc1 : c < 1`, which is false at `c = 1`) makes `Solution.lean` fail to
elaborate — the term assignment no longer type-checks. (Run this by editing `Challenge.lean`
+ `Solution.lean` in tandem; it is not part of the committed build.)

## §6 Comparator

**Linux-only** (landrun / Landlock sandbox); **NOT run on this platform (Windows).** Runs on
CI in `.github/workflows/erdos361-comparator.yml`, which builds pinned `comparator`,
`lean4export` (matched to Lean v4.31.0), and `landrun`, then runs **two** configs in the
sandbox — both with permitted axioms `propext`, `Quot.sound`, `Classical.choice` only:

- `comparator/erdos361_cge1.json` — proves `erdos361_cge1` is axiom-free.
- `comparator/erdos361_irregular.json` — proves `erdos361_irregular` is axiom-free.

The workflow requires the string `Your solution is okay!` twice (once per config). Its result
is the authoritative check and supersedes §4/§5 if they ever disagree.

## §7 Deliberately excluded

- The paper's **general divisor-sensitive** Theorem 1 / Corollaries 2–3 (arbitrary divisor
  `d`, explicit Roth `r₃` term) are a bonus generalization not needed for the irregularity;
  they are **not** formalized here. Only Theorem 4 (irregularity) and the `c ≥ 1` formula are.
- Effectivity: the thresholds are existential (`∃ N₀ …`), not explicit.
- No standalone single-file `Erdos361Complete.lean` is shipped (optional; see erdos1054 which
  also omits it).

## §8 Reproduction

```bash
cd erdos361
lake exe cache get
lake build
lake build Challenge Solution
# Comparator (Linux):
lake env /path/to/comparator comparator/erdos361_cge1.json
lake env /path/to/comparator comparator/erdos361_irregular.json
```
