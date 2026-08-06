import Sendov9.Final
import Sendov9.NonVacuous

/-!
# Sendov's conjecture in degree nine — build root

`Sendov9.Final.sendov_degree_nine_general` is the result:

> every complex polynomial of degree nine with all zeros in the closed unit disk has,
> for each zero `a`, a critical point within distance one of `a`.

`#print axioms` shows exactly `[propext, Classical.choice, Quot.sound]`; there are no
carried hypotheses and no `sorry` anywhere in the 46 modules of this library.  The only
`sorry`s in this directory are the deliberate ones in `Challenge.lean`, which is the
audit surface.

`Sendov9.NonVacuous.sanity` applies the theorem to `p = X⁹` and obtains an actual
critical point, so the hypotheses are satisfiable and the statement is not true for the
wrong reason.

This formalizes Principia Math, *Sendov's Conjecture in Degree Nine* (`paper/sendov9.tex`).
See `VERIFICATION.md` for the ledger and `README.md` for the route.
-/
