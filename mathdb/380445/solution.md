# Exact maximum convex-hull area of a hexagonal polyomino

Let the centers of the `n` hexagons be points of the triangular lattice, in
axial coordinates `(q,r)`, and normalize area so that a fundamental lattice
parallelogram (equivalently, one hexagonal cell) has area `1`.  Put
`S` for the set of centers and `P=conv(S)`.

The centered cell is

\[
H=\operatorname{conv}\{(1/3,1/3),(-1/3,2/3),(-2/3,1/3),
(-1/3,-1/3),(1/3,-2/3),(2/3,-1/3)\}.
\]

Thus the convex hull of the polyhex is `P+H`.  Define

\[
f_1=q+2r,\qquad f_2=q-r,\qquad f_3=2q+r,
\]

and let `w_i` be the range of `f_i` on `P`.  The elementary mixed-area
formula for the six edges of `H` gives

\[
\operatorname{area}(P+H)=1+\operatorname{area}(P)
 +\frac{w_1+w_2+w_3}{3}. \tag{1}
\]

Choose a spanning tree of the center adjacency graph.  It has `s=n-1`
unit edges; let `a,b,c` be the numbers in its three unoriented directions
and let `m=max(a,b,c)`.

We need two estimates.  First,

\[
\operatorname{area}(P)\leq\frac{ab+bc+ca}{2}. \tag{2}
\]

To see this, root the tree and add its vertices parent-before-child.  If a
point `x+v` is added to a convex hull already containing `x`, the added area
is at most half the old width transverse to `v`.  Indeed, after sending
`x` to `(0,0)` and `v` to `(0,1)`, the two tangents from `(0,1)` cut the new
cap into two pieces.  On each side the segment from `(0,0)` to the tangency
point is already in the old hull, so the cap thickness is bounded by a
linear function decreasing from `1` to `0`; its integral is half that
side's horizontal span.  A previous tree edge parallel to `v` contributes
zero to the transverse width, and either other lattice direction contributes
at most one.  On summing, each differently directed pair of tree edges is
counted once, proving (2).

Second,

\[
w_1+w_2+w_3\leq3s+m. \tag{3}
\]

For each `i`, orient the unique tree path from a vertex minimizing `f_i` to
one maximizing it.  The width `w_i` is the telescoping sum of the signed
`f_i`-increments along this path.  Regroup the three sums by tree edge.
The absolute increments on a unit edge are a permutation of `(1,1,2)`, so
an edge contributes at most `4`.  A contribution greater than `3` must be
exactly `4`; then all three extremal paths cross that edge with all signs
positive.

The common part of the three paths is itself a path.  Orient it as the
`f_3` path.  The other two path orientations are fixed on this common part.
For an edge oriented so that its `f_3` increment is positive, the three
possible increment triples are

\[
(1,1,2),\quad(2,-1,1),\quad(-1,2,1).
\]

For a fixed pair of orientations of the first two paths, only one of the
three direction classes can make every signed increment positive.  Hence
all edges contributing `4` are parallel, and there are at most `m` of them.
Every other edge contributes at most `3`, proving (3).

Combining (1)--(3),

\[
\operatorname{area}(P+H)
\leq1+s+\frac m3+\frac{ab+bc+ca}{2}. \tag{4}
\]

The right side is maximized when `a,b,c` differ by at most one.  Indeed, if
the largest exceeds the smallest by at least two, moving one unit from the
largest to the smallest increases `ab+bc+ca` by at least one and decreases
`m/3` by at most `1/3`, a net gain of at least `1/6` in (4).

Writing `s=3k,3k+1,3k+2`, substitution of the balanced triples gives,
respectively, six times the upper bound

\[
9k^2+20k+6,\qquad 9k^2+26k+14,\qquad 9k^2+32k+23.
\]

Equivalently, the exact upper bound is

\[
\boxed{\displaystyle
M(n)=\frac16\left\lceil n^2+\frac{14}{3}n\right\rceil
=\frac16\left(
\left\lfloor n^2+\frac{14}{3}n+1\right\rfloor
-\mathbf 1_{3\mid n}\right).}
\]

It is attained as follows.  Take balanced nonnegative `a,b,c` with
`a+b+c=n-1`, choose a largest entry as `b`, and form a path with `a` steps
in direction `(0,1)`, then `b` steps in direction `(1,0)`, then `c` steps
in direction `(1,-1)`.  Its center hull has area `(ab+bc+ca)/2`, while its
three widths sum to `3s+b`; hence equality holds above.

In particular,

\[
M(n)\leq\frac16\left\lfloor n^2+\frac{14}{3}n+1\right\rfloor,
\]

which proves MathDB #380445.  When `3` divides `n`, the proposed bound is
not sharp: the exact maximum is smaller by `1/6`.
