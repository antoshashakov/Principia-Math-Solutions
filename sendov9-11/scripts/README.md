# scripts/ — the degrees-10/11 emitters and cross-check (provenance artifacts)

These are the exact scripts that produced the generated parts of the degrees-10/11
development, shipped as supplied from the certification machine. They are **not** part of
any build: every file they emitted is committed, elaborates through Lean's kernel like
any hand-written module, and is independently evidenced by the logs in `../certlogs1011/`
and `../certlogs11v2/`. Generation is a convenience, not a trust step.

| script | emits | self-check before writing |
| --- | --- | --- |
| `emit_boxes11v2.py` | `../boxes11v2/` (531 box certificates, c₄ = 1447/50) | per box, asserts the exact Bernstein margin against `boxes11v2-tau.csv`; construction is line-for-line `../certificates/degree11_verify.py` |
| `emit_eint1011.py` | `SendovNEInt.lean` | re-verifies every closed-form identity at random rational points by three independent evaluation routes |
| `emit_rows1011.py` | `SendovNRows10/11.lean` | asserts every transcribed constant against ALL shipped box-file headers |
| `emit_emajeq1011.py` | `SendovNEmajEq.lean`, `SendovNBoxEq10_40.lean` | RHS identities verified at 25 random rational points by two independent routes; box table matched integer-for-integer against the shipped file |
| `emit_assembly1011.py` | `SendovNBdryEq*/Red*/Covering*/Reduction*` | every consumed box table regenerated from the verifier arithmetic and matched integer-for-integer against the shipped file |
| `crosscheck_boxes11v2.py` | (nothing — pure checker) | parses the emitted Lean files back and re-verifies `hQ`, `cnum > 0`, and every Bernstein numerator on Python integers/fractions, trusting nothing from the emitter; run in this repo → `../certlogs11v2/crosscheck-repo.log` |
| `boxes11v2-tau.csv` | (data) | per-box τ choice and exact margin from the c₄ = 1447/50 experiment |

**Paths.** The emitters were written for the certification machine's flat working
directory (dev modules and degree-10 box files at the repository root, `boxes11v2/` and
`certificates/` as siblings). In this repository the corresponding outputs live in
`../Sendov1011/`, `../boxes10/` and `../boxes11v2/`, so re-running an emitter here
requires recreating that flat layout (or adjusting its `HERE`-relative paths). The
cross-check runs as-is from the repo root:

```sh
python3 scripts/crosscheck_boxes11v2.py boxes11v2/*.lean
```
