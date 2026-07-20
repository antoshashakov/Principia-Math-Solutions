/-
Default build target for the Erdős #123 formalization.

This file exists so that `lake build` is an HONEST signal: it imports EVERY module under
`Erdos123/`. Nothing that is proved is hidden from the build, and nothing that is in the
build is unproved. The whole tree compiles and contains no unproved placeholder, no
additional postulate, and no `native_decide`.

The results, and where they live:

  * `Erdos123.Statement`                       — trusted definitions, Mathlib-only imports.
                                                 This is the import closure of the
                                                 repository-root `Challenge.lean`.

  * `Erdos123Band.erdos123_dcomplete_real`     (Erdos123/GMain.lean)
      Paper Theorem 1.2 — Erdős #123 for any real ratio `ρ ∈ (1, min(a,b,c))`.

  * `Erdos123Band.glclt_asymptotic`            (Erdos123/GLCLTAsymptotic.lean)
      Paper Theorem 1.1, eq. (1.1) — the local limit law, uniformly in `n`.

  * `Erdos123Band.glclt_coverage`              (Erdos123/GLCLT.lean)
      Paper Theorem 1.1, second assertion — coverage of the full central window.

  * `Erdos123Band.erdos123_dcomplete'`         (Erdos123/Main.lean)
      Paper Theorem 1.2 in the classical `d`-complete phrasing, by an independent
      Phase-1 route over the fixed band `[x, 3x/2)`. See `formalization.yaml`
      (`fidelity.divergences`).

  * `Erdos123Band.glow_energy_measure_general` (Erdos123/GLowEnergyGen.lean)
  * `Erdos123Band.gvery_low_sharp`             (Erdos123/GTail.lean)
      Paper Proposition 3.1, eq. (3.1) and eq. (3.2) — the arithmetic rigidity core.

All have axiom footprint exactly `[propext, Classical.choice, Quot.sound]`.

`formalization.yaml` carries the full statement-by-statement map from the paper into the
Lean. `VERIFICATION.md` records every check that was actually run, and what was not.
-/

-- The trusted statement layer: definitions only, Mathlib-only imports. Kept deliberately
-- small so that it, together with `Challenge.lean`, is the entire audit surface.
import Erdos123.Statement

-- Phase 1: the fixed band [x, 3x/2), ending in `erdos123_dcomplete'`.
import Erdos123.Band
import Erdos123.Slab
import Erdos123.Grid
import Erdos123.Routing
import Erdos123.Rigidity
import Erdos123.LowEnergy
import Erdos123.MajorArcLB
import Erdos123.Main

-- The ρ = p/q generalization: band, slab, grid, rigidity.
import Erdos123.GBand
import Erdos123.GSlab
import Erdos123.GGrid
import Erdos123.GRigidity
import Erdos123.GBandAux
import Erdos123.GLowEnergy

-- The general-ρ local central limit theorem and its analytic inputs.
import Erdos123.GCosApprox
import Erdos123.GaussFT
import Erdos123.GPrincipal
import Erdos123.GTail
import Erdos123.GLCLT
import Erdos123.GMain

-- Paper Theorem 1.1 eq. (1.1) — the local limit law itself — the remaining two-sided
-- bounds of Proposition 2.1, and the general-`z` form of Proposition 3.1.
import Erdos123.GLowEnergyGen
import Erdos123.GMuBounds
import Erdos123.GLCLTAsymptotic
