# Literature and status audit for MathDB #380445

Checked through: 2026-08-18.

## Exact primary statement

Sascha Kurz, *Convex hulls of polyominoes*, arXiv:math/0702786v1
(26 February 2007), Conjecture 2, states that the area of the convex hull of
an edge-to-edge connected system of `n` regular unit hexagons is at most

\[
\frac16\left\lfloor n^2+\frac{14}{3}n+1\right\rfloor.
\]

- arXiv HTML: https://arxiv.org/html/math/0702786#S4
- arXiv record: https://arxiv.org/abs/math/0702786
- journal version: *Beiträge zur Algebra und Geometrie* 49 (2008), 125–136,
  https://www.emis.de/journals/BAG/vol.49/no.1/b49h1kur.pdf

The factor `1/6` is outside the floor.  A secondary OEIS entry moves the floor
outside the division; that is a different statement and is false as an upper
bound already for two adjacent cells.

## Later direct discussion

Veronika Steffanova, *Extremal Polyominoes*, Charles University master's
thesis (defended 2015), Section 3.2.3, pp. 28–29, explicitly says that the
author tried but did not succeed in proving Kurz's polyhex conjecture.  It
identifies the likely extremal “washtub” construction and records area `24.5`
for `n=10`, versus `23.5` for the three-armed star.

- Repository record: https://dspace.cuni.cz/handle/20.500.11956/67578
- Primary PDF: https://dspace.cuni.cz/bitstream/handle/20.500.11956/67578/DPTX_2014_1_11320_0_392267_0_158242.pdf?isAllowed=y&sequence=1

This is consistent with the sharpness construction in the present proof, but
does not supply the missing upper bound.

## Current search

- Exact title, formula, “polyhex convex hull,” author/citation, and
  English/German terminology searches found no later proof or counterexample.
- OpenAlex work `W1566507365` reports only one linked forward citation,
  Kurz's own later habilitation record:
  https://api.openalex.org/works?filter=cites%3AW1566507365&per-page=100
- Semantic Scholar likewise exposed only that linked citation in the audit.
- OEIS A126026 still describes the item as a “Conjectured upper bound” as of
  2026-08-18: https://oeis.org/A126026.  Its displayed formula incorrectly
  parenthesizes the floor and therefore is used only as bibliographic evidence
  of continued conjectural status, not as mathematical authority.

## Verdict

No published resolution was located through 2026-08-18.  The proof in this
directory is therefore counted as an internally verified campaign result.
This search cannot establish absolute novelty, and no publication-priority
claim is made.
