import Mathlib
import SendovNReduction10

/-!
# Sendov's conjecture, degree 10 — final theorem

`CertificateReduction 10 boxes10` (the analytic reduction, proved) +
`CoveringPositive boxes10` (the kernel-checked finite half) through
`Sendov911Capstone.sendov_of_reduction`.

Acceptance gate: `#print axioms` must show exactly
`[propext, Classical.choice, Quot.sound]`.
-/

namespace SendovN.Final10

/-- **Sendov's conjecture in degree 10.** -/
theorem sendov10 : Sendov911Capstone.Sendov 10 :=
  Sendov911Capstone.sendov_of_reduction Reduction10.certificateReduction10
    Covering10.covering10

end SendovN.Final10

#print axioms SendovN.Final10.sendov10
