module

public import SHE.NativeCurrentBudgetFrequency

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeCurrentBudgetFrequency
open GaussianAssignmentBlocks AssignmentGapPartition AllocatedAssignmentKernel
  MeanRMSTimeFactors QuarterRMSTimeFactors PhysicalAssignmentGapScale
open scoped BigOperators

/-- The native time envelope depends only on the structural profile
constants, so its frequency constant is uniform for canonical smooth
companions with those same constants. -/
theorem majorant_congr (P Q:CanonicalCovariance.ProfileParameters)
    (hl:P.lower=Q.lower)(hh:P.holder=Q.holder)(he:P.exponent=Q.exponent)
    (ell:ℝ)(Cs:ℕ→ℝ)(k:ℕ)(ρ χ ν w:ℝ):
    majorant P ell Cs k ρ χ ν w=majorant Q ell Cs k ρ χ ν w:=by
  simp only [majorant,assignmentCoefficient,PhysicalAssignmentGapScale.prefactor,
    PhysicalAssignmentGapScale.leafPrefactor,hl,hh,he]

end SHE.NativeCurrentBudgetFrequency
