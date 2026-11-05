module

public import SHE.MixedPastWordMoments
public import SHE.PhysicalAssignmentGapScale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHE.MixedPastWordMoments
open MeasureTheory Real GaussianAssignmentBlocks
open scoped BigOperators
variable {k d : ℕ}

/-- Conditional past-v estimates use the original RELATIVE native
leaf ages. Their old-interval factor is exactly the already integrated
minimum-gap/root-clip factor; no age is changed to an absolute time. -/
theorem factor_eq_plain (P : CanonicalCovariance.ProfileParameters) (lo hi : Fin k→ℝ)
    (age : Fin k→ℝ) (choices : List (Fin k×Fin (k+1))) (A0 ν : ℝ) :
    factor (d:=d) P lo hi age choices A0 ν=
      PhysicalAssignmentGapScale.plainFactor P choices (fun j=>hi j-lo j) age A0 ν d := by
  simp only [factor,PhysicalAssignmentGapScale.plainFactor,VectorPhysicalRoot.scale,
    NativeAssignedLeafMoments.leafScale,MinimumGapChoice.blockChoice,sub_zero]

/-- The block minimum and every root clip commute with a simultaneous
shift of the observation/history clock. The supplied ages remain the
relative ages appropriate to the conditional profile. -/
theorem factor_translate (P : CanonicalCovariance.ProfileParameters) (lo hi : Fin k→ℝ)
    (age : Fin k→ℝ) (choices : List (Fin k×Fin (k+1))) (A0 ν v : ℝ) :
    factor (d:=d) P (fun j=>lo j+v) (fun j=>hi j+v) age choices A0 ν=
      factor (d:=d) P lo hi age choices A0 ν := by
  rw [factor_eq_plain,factor_eq_plain]
  have he : (fun j=>hi j+v-(lo j+v))=(fun j=>hi j-lo j) := by
    funext j
    ring
  rw [he]

theorem total_translate (P : CanonicalCovariance.ProfileParameters) (lo hi : Fin k→ℝ)
    (age : Fin k→ℝ) (A0 ν v : ℝ) :
    total (d:=d) P (fun j=>lo j+v) (fun j=>hi j+v) age A0 ν=
      total (d:=d) P lo hi age A0 ν := by
  simp only [total,factor_translate]

/-- Literal relative-age conditional factor in the scalar gap ledger. -/
theorem factor_eq_allocated_gain (P : CanonicalCovariance.ProfileParameters) (lo hi : Fin k→ℝ)
    (age : Fin k→ℝ) (choices : List (Fin k×Fin (k+1))) (A0 ν : ℝ) :
    factor (d:=d) P lo hi age choices A0 ν=
      PhysicalAssignmentGapScale.prefactor P choices A0 d*
        AllocatedAssignmentKernel.gain choices (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2)))
          (P.exponent/4) (fun j=>hi j-lo j)*
        AllocatedAssignmentKernel.emptyGain choices (P.exponent/4) age := by
  rw [factor_eq_plain,PhysicalAssignmentGapScale.plainFactor_eq]

end SHE.MixedPastWordMoments
