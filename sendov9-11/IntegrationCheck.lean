/-
Integration check: the `Box` abstraction in `Sendov911Capstone` really is what
the generated certificate files prove.  Builds a `CoveringPositive` family from
two genuinely machine-checked boxes (one degree-10 interior, one degree-10
boundary), with no `sorry` and no restatement of their content.
-/
import Sendov911Capstone
import Sendov911Box10_40
import Sendov911Box10Boundary

namespace IntegrationCheck

open Sendov911Capstone

/-- The degree-10 interior box `a ∈ [2/5, 41/100]`, as a `Box`. -/
noncomputable def box40 : Box where
  nx := 10
  ny := 10
  A := Sendov911Box10_40.tab Sendov911Box10_40.Adata
  D := (Sendov911Box10_40.Dscale : ℝ)
  hD := by norm_num [Sendov911Box10_40.Dscale]

/-- The degree-10 boundary box, as a `Box`. -/
noncomputable def boxB : Box where
  nx := 28
  ny := 10
  A := Sendov911Box10Boundary.tab Sendov911Box10Boundary.Adata
  D := (Sendov911Box10Boundary.Dscale : ℝ)
  hD := by norm_num [Sendov911Box10Boundary.Dscale]

/-- Both boxes are certified, straight from their own `box_positive`. -/
theorem covering : CoveringPositive [box40, boxB] := by
  refine coveringPositive_cons ?_ (coveringPositive_cons ?_ coveringPositive_nil)
  · intro U V hU0 hU1 hV0 hV1
    exact Sendov911Box10_40.box_positive hU0 hU1 hV0 hV1
  · intro U V hU0 hU1 hV0 hV1
    exact Sendov911Box10Boundary.box_positive hU0 hU1 hV0 hV1

/-- Hence, given the analytic reduction against this family, Sendov in degree 10. -/
theorem sendov10_of_reduction
    (hred : CertificateReduction 10 [box40, boxB]) : Sendov 10 :=
  sendov_of_reduction hred covering

end IntegrationCheck

#print axioms IntegrationCheck.covering
#print axioms IntegrationCheck.sendov10_of_reduction
