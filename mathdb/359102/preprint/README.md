# Preprint: The $\ell^1$-boundedness conjectures of Heil and Yu

Draft preprint growing out of this dossier. **Not submitted anywhere. Byline
and outreach not yet settled.**

## Files

| file | what it is |
|---|---|
| `heil-yu-preprint.tex` | source, `amsart`, compiles under `tectonic` with no errors |
| `heil-yu-preprint.pdf` | 8 pages |

## What changed relative to `solution.md`

The dossier refutes **Conjecture 4.10** of Heil and Yu (bounded plus uniformly
separated does not imply $\ell^1$-bounded) using a Reed-Muller construction.

The preprint keeps that result and adds:

1. **Conjecture 4.13 is resolved** — the collection of $\ell^1$-bounded sets is
   closed under neither finite unions nor finite sums. This is the conjecture
   Heil and Yu called "a very difficult question". By their Theorem 4.12 it
   settles four structural statements at once.
2. **One construction settles both conjectures.** Take
   $\mathcal{H} = \bigoplus_k \mathbb{C}^{4^k}$, let $M_1$ be the standard bases
   of the blocks and $M_2$ the Fourier bases. Separation inside a block is
   $\sqrt{2 - 2/\sqrt d} \ge 1$ since $d = 4^k \ge 4$, and across blocks it is
   $\sqrt 2$. So $M_1 \cup M_2$ is bounded and uniformly separated (giving 4.10)
   and is a union of two $\ell^1$-bounded sets (giving 4.13).
3. **A frame lower bound.** For any frame with bounds $A \le B$,
   $\max_{x \in \mathcal{B} \cup \mathcal{F}} \|x\|_{1,\mathcal{G}} \ge (A/\sqrt B) d^{1/4}$.
   This is the engine; the dossier's bound applied to one coded family, this one
   applies to every frame.
4. **The extremal constant.** $L(d) = d^{1/4}$ exactly for perfect squares, and
   $L(8) = 1 + 1/\sqrt 2$ exactly, which shows the natural picket-fence
   construction is not optimal in general.

The Reed-Muller construction is kept as Section 5 because it is **not**
subsumed: it gives the better rate $\sqrt{d/3}$ against $d^{1/4}$, but it does
not settle 4.13, since that conjecture needs a counterexample that splits into
two $\ell^1$-bounded pieces and the coded set has no such splitting. Neither
construction subsumes the other; see Remark 5.4.

## Attribution as currently written

- Byline: **Eric Hou and Principia Math**.
- Acknowledgements state that the Section 5 construction originated in this
  dossier and the remaining results are due to the first author.
- Donoho-Stark 1989 is credited in Section 1.3, before any claim is made, for
  the picket fence, its Fourier self-duality, the uniqueness of extremisers, and
  the divisor sensitivity. Those are classical and the preprint says so.

If individual Principia contributors should be named instead of, or alongside,
the group byline, that is a one-line change at the top of the `.tex`.

## Open before this goes anywhere

1. **Byline confirmation.** Group byline versus named individuals.
2. **Email addresses.** Both `\email{}` fields are empty; arXiv and any journal
   will require at least one.
3. **MathSciNet / zbMATH search on Lemma 2.1**, the $\ell^1$ uncertainty
   inequality $\|x\|_1 \|Fx\|_1 \ge \sqrt d \|x\|_2^2$. It is elementary and may
   be folklore. Not run — no institutional access. This is the main novelty risk
   in the paper.
4. **Contact Heil and Yu.** They posed the conjecture and can say quickly
   whether Lemma 2.1 is known and whether the reduction is sound. Conjecture
   4.13 comes from Yu's 2024 Georgia Tech thesis, so this letter is worth
   handling carefully.
5. **Close-form the $d = 8$ matrix.** The upper bound in Theorem 1.4 currently
   rests on a numerically constructed unitary, verified to $1.44 \times 10^{-15}$,
   not on a closed-form construction. A referee could object.

## Status of the numerics

Everything in Section 8 is a consistency check. The theorems are proved in
Sections 2 through 6 and do not depend on the computations. Where the paper says
"verified" it means numerically checked and nothing stronger.

Target venue on current content: **JMAA**, which published the source paper.
