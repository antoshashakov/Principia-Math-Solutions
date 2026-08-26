# MathDB #380445 — proof skeleton

## Status

- Claim: the conjectured upper bound is true.
- Stronger claim: the exact maximum for `n` cells is

  \[
  M(n)=\frac16\left\lceil n^2+\frac{14}{3}n\right\rceil
  =\frac16\left(\left\lfloor n^2+\frac{14}{3}n+1\right\rfloor-
  \mathbf 1_{3\mid n}\right).
  \]

- Internal proof state: complete; hostile independent audit passed.
- Literature/priority state: current audit closed with no published proof located
  through 2026-08-18. Publication priority is not claimed.

## Normalization

Use axial coordinates `(q,r)` for the triangular lattice of hexagon centers.
The three unoriented unit-edge directions are represented by

\[
e_1=(1,0),\qquad e_2=(0,1),\qquad e_3=(1,-1).
\]

Choose the scale in which a fundamental lattice parallelogram, and hence one
Voronoi hexagon, has area `1`.  The centered unit hexagon is

\[
H=\operatorname{conv}\left\{
(1/3,1/3),(-1/3,2/3),(-2/3,1/3),
(-1/3,-1/3),(1/3,-2/3),(2/3,-1/3)
\right\}.
\]

For the set `S` of centers put `P=conv(S)`.  Convex hull commutes with
Minkowski addition by a convex set, so the convex hull of all cells is `P+H`.

Define the three linear forms

\[
f_1(q,r)=q+2r,\qquad f_2(q,r)=q-r,\qquad
f_3(q,r)=2q+r=f_1(q,r)+f_2(q,r),
\]

and write `w_i=max_P f_i-min_P f_i` and `L(P)=w_1+w_2+w_3`.

## Gate G1 — exact parallel-body identity

Prove

\[
\operatorname{area}(P+H)=\operatorname{area}(P)+1+\frac13L(P). \tag{G1}
\]

For a fully explicit calculation, set

\[
g_1=(2/3,-1/3),\quad g_2=(-1/3,-1/3),\quad g_3=(1/3,-2/3).
\]

Then `H=sum_i[-g_i/2,g_i/2]` is a zonotope,
`sum_{i<j}|det(g_i,g_j)|=1`, and, up to permutation and sign,
`det(g_i,(q,r))=f_i(q,r)/3`.  The planar zonotope/mixed-area formula gives

\[
\operatorname{area}(P+H)=\operatorname{area}(P)
+\sum_{i<j}|\det(g_i,g_j)|
+\sum_i\operatorname{range}_{P}\det(g_i,\mathord\cdot),
\]

which is exactly (G1).  This also covers a segment or point `P` directly.

Status: closed.

## Gate G2 — center-hull area bound from a spanning tree

Choose a spanning tree `T` of the center adjacency graph.  It has
`s=n-1` edges.  Let `a,b,c` be the numbers of its edges in the three
unoriented directions.

Prove

\[
\operatorname{area}(P)\leq \frac12(ab+bc+ca). \tag{G2}
\]

### One-point extension lemma

If `K` is convex, `x in K`, and `v` is a vector, then

\[
\operatorname{area}(\operatorname{conv}(K\cup\{x+v\}))-
\operatorname{area}(K)
\leq \frac12\left(\max_{y\in K}\det(v,y)-
\min_{y\in K}\det(v,y)\right). \tag{E}
\]

If `x+v` lies in `K`, the increment is zero.  Otherwise use affine
coordinates with `x=(0,0)` and `v=(0,1)`.  The two tangents from `(0,1)` to
`K` split the new cap into a left and right part.  On either side, the segment
from `x` to the tangency point lies in `K`, so the vertical thickness of the
new cap is bounded by the linear function that drops from `1` to `0`.  Its
integral is half that side's horizontal span.  Adding the two sides gives
half the full transverse width.  Point and segment cases follow directly,
or by replacing `K` with `K+epsilon B` and letting `epsilon` tend to zero.

Root `T` and add vertices parent-before-child.  When an edge of one
direction is added, the transverse width in (E) is at most the number of
previous edges in the other two directions: along every tree path, a
parallel edge contributes determinant `0`, and either nonparallel direction
contributes determinant of absolute value `1`.  Summing (E), every unordered
pair of differently directed tree edges is counted once, proving (G2).

Status: closed.

## Gate G3 — three-width bound from the same tree

Put `m=max(a,b,c)`.  Prove

\[
L(P)\leq 3s+m. \tag{G3}
\]

For each `i`, choose tree vertices attaining the minimum and maximum of
`f_i`, and orient the unique tree path `Q_i` from the minimum to the maximum.
Telescoping along the path gives

\[
w_i=\sum_{e\in Q_i}\Delta_i(e).
\]

After summing over `i` and regrouping by tree edge, call the contribution of
an edge `gamma(e)`.  On a unit edge, the absolute changes of
`(f_1,f_2,f_3)` are a permutation of `(1,1,2)`.  Hence `gamma(e)<=4`.
If `gamma(e)>3`, integrality forces `gamma(e)=4`: all three paths cross the
edge and all three signed contributions have their maximum positive signs.

All such exceptional edges lie in `R=Q_1 intersect Q_2 intersect Q_3`, which
is a path (or empty).  Orient `R` as `Q_3`.  Each of `Q_1,Q_2` has a fixed
orientation relative to `R`.  Along an edge of `R` on which `Delta f_3>0`,
the possible change triples for the three unoriented edge directions are

\[
(1,1,2),\qquad(2,-1,1),\qquad(-1,2,1).
\]

An exceptional edge necessarily has `Delta f_3>0`, because its `Q_3`
contribution is positive and `R` is oriented as `Q_3`.  For the fixed pair
of relative signs of `Q_1,Q_2`, at most one of these
three triples makes all three oriented contributions positive.  Thus every
edge with `gamma(e)=4` has the same unoriented direction.  There are at most
`m` of them; all other edges contribute at most `3`.  Therefore

\[
L(P)=\sum_e\gamma(e)\leq 3s+m.
\]

Status: closed.

## Gate G4 — integer optimization

By (G1)--(G3),

\[
\operatorname{area}(P+H)
\leq 1+s+\frac{m}{3}+\frac12(ab+bc+ca). \tag{1}
\]

If the smallest and largest of `a,b,c` differ by at least `2`, transfer one
unit from the largest to the smallest.  The pair sum `ab+bc+ca` increases by
at least `1`, while `m/3` decreases by at most `1/3`; hence the right side of
(1) increases by at least `1/6`.  Its maximum is therefore attained by the
balanced triples:

| `s` | balanced `(a,b,c)` | six times the maximum in (1) |
|---|---|---|
| `3k` | `(k,k,k)` | `9k^2+20k+6` |
| `3k+1` | `(k,k,k+1)` | `9k^2+26k+14` |
| `3k+2` | `(k,k+1,k+1)` | `9k^2+32k+23` |

Substituting `n=s+1` shows that these values equal

\[
\left\lceil n^2+\frac{14}{3}n\right\rceil
=
\left\lfloor n^2+\frac{14}{3}n+1\right\rfloor-
\mathbf 1_{3\mid n}.
\]

This proves the conjectured upper bound, and is stronger by `1/6` when
`3` divides `n`.

Status: closed.

## Gate G5 — sharpness construction

For a balanced triple `(a,b,c)`, choose the largest entry as `b` and take a
three-segment lattice path with consecutive step directions

\[
(0,1)^a,\qquad(1,0)^b,\qquad(1,-1)^c.
\]

Its center hull has vertices

\[
(0,0),\quad(0,a),\quad(b,a),\quad(b+c,a-c).
\]

Direct shoelace calculation gives center-hull area
`(ab+bc+ca)/2`, and direct range calculation gives `L=3s+b=3s+m`.
Thus equality holds in (1), including the degenerate cases with a zero
segment.  The stronger formula is the exact maximum.

Status: closed.

## Gate G6 — exact computational verification

`verify_polyhex.py` enumerates every translation class of fixed polyhexes
through `n=9`, uses exact rational arithmetic, and checks (G2), (G3), the
claimed exact maximum, and a sharp example at every size.  Result:

- 98,759 polyhexes checked;
- observed maxima `1, 7/3, 23/6, 35/6, 49/6, 32/3, 41/3, 17, 41/2`;
- every assertion passed.

Status: closed.  See `verification.out`.

## Gate G7 — hostile independent proof audit

An independent line-by-line audit checked the G1 constants, the factor `1/2`
in G2, the path-intersection/sign argument in G3 (including tied extrema),
the residue optimization, all degenerate cases `n=1,2,3`, and the sharpness
construction.  No mathematical flaw was found; the exposition refinements
above were incorporated.

Status: closed.

## Gate G8 — current-literature/priority audit

The exact source statement, the 2008 journal version, forward citations,
exact-title/formula searches, the 2015 Steffanova thesis, and the live OEIS
entry were checked.  The thesis explicitly says its attempt did not prove the
polyhex upper bound.  No published resolution was located through
2026-08-18.  The OEIS entry still labels the claim conjectural, but its own
parenthesization moves the floor outside Kurz's intended position and is not
a mathematically valid restatement.  See `literature-audit.md`.

Status: closed for internal campaign purposes.  This is not a claim of
publication priority or peer review.
