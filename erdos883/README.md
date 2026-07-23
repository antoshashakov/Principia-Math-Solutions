# Erdős Problem 883 — odd cycles in the coprime graph (statement + sharpness)

> For `A ⊆ {1, …, n}` let `G(A)` be the graph on `A` joining two integers when they
> are coprime. **If `|A| > ⌊n/2⌋ + ⌊n/3⌋ − ⌊n/6⌋`, must `G(A)` contain all odd cycles
> of length ≤ n/3 + 1?** (Erdős–Sárközy 1997, who proved it for lengths ≤ cn with some
> `c > 0`.)
>
> The companion manuscript (`paper/`) claims the sharp `c = 1/6` resolution: writing
> `q = ⌊n/3⌋ − ⌊n/6⌋`, above the threshold **every** odd cycle length `3, 5, …, 2q+1`
> occurs, and both the threshold and the ceiling `2q+1` are best possible.

## ⚠ What is and is not proved here

**This folder is NOT a completed formalization of the solve.** The status is:

| Piece | Status |
| --- | --- |
| Statement of record (`erdos883Forcing`) | **stated** in `Erdos883/Statement.lean`, *not proved* |
| Threshold sharpness (no odd cycle at `|A| = T(n)`) | **proved, axiom-free** |
| Ceiling sharpness + attainment (`2q+1` exact at `|A| = T(n)+1`) | **proved, axiom-free** |
| Forcing direction (the actual solve) | **not formalized** — open target |
| Manuscript referee status | numerical certificates independently recomputed (`referee/`); analytic prose **not** independently verified |

## Results

| Paper result | Statement | Lean name | Module |
| --- | --- | --- | --- |
| Prop. 1.2 (threshold sharp) | some `A`, `\|A\| = T(n)`, has bipartite `G(A)`: no odd cycle | `Erdos883.Statement.erdos883_threshold_sharp` | `Erdos883/Core.lean` |
| Prop. 1.2 (ceiling sharp + attained) | some `A`, `\|A\| = T(n)+1`, has `C_{2t+1}` for all `1 ≤ t ≤ q` and no longer odd cycle | `Erdos883.Statement.erdos883_ceiling_sharp` | `Erdos883/Core.lean` |
| Thm 1.1 forcing (claimed solve) | `\|A\| > T(n)` forces `C_{2ℓ+1}`, `1 ≤ ℓ ≤ q` | `Erdos883.Statement.erdos883Forcing` — **statement only** | `Erdos883/Statement.lean` |

## How the statements are kept honest

`Erdos883/Statement.lean` (definitions only — **no axioms**, Mathlib-only import) and
`Challenge.lean` (the two proved statements, `sorry`) are the **entire audit surface**.
`Solution.lean` proves the same statements by direct term assignment from the development.
[Comparator](https://github.com/leanprover/comparator) configs live in `comparator/`.

## Verify it yourself

```bash
cd erdos883
lake exe cache get
lake build                 # the development (Erdos883)
lake build Challenge Solution
```

## Layout

```
erdos883/
├── Erdos883/
│   ├── Statement.lean   trusted defs (coprimeGraph/HasCycleLength/T/q) + erdos883Forcing (Prop)
│   └── Core.lean        the development: bipartite parity argument, cycle counting, both sharpness theorems
├── Erdos883.lean        build root (imports Core)
├── Challenge.lean       the two proved statements, `sorry`  (audit surface)
├── Solution.lean        the same statements, proved by term assignment + #print axioms
├── comparator/          one config per proved result
├── paper/erdos883.pdf   the manuscript (claimed solve), sha256-pinned in VERIFICATION.md
├── referee/             independent exact-rational recomputation of the paper's certificates
├── formalization.yaml   mathlib-initiative metadata + alignment
└── VERIFICATION.md      the honest ledger
```
