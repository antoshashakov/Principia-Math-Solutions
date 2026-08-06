import Mathlib
import SendovNReduction11

/-!
# Sendov's conjecture, degree 11 — final theorem

`CertificateReduction 11 boxes11` (the analytic reduction, proved) +
`CoveringPositive boxes11` (the kernel-checked finite half) through
`Sendov911Capstone.sendov_of_reduction`.

Acceptance gate: `#print axioms` must show exactly
`[propext, Classical.choice, Quot.sound]`.
-/

namespace SendovN.Final11

/-- **Sendov's conjecture in degree 11.** -/
theorem sendov11 : Sendov911Capstone.Sendov 11 :=
  Sendov911Capstone.sendov_of_reduction Reduction11.certificateReduction11
    Covering11.covering11

end SendovN.Final11

#print axioms SendovN.Final11.sendov11
