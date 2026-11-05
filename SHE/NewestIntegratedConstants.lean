module
public import SHE.MixedPastNewestCurrentEnergy
public import SHE.NewestErrorConstants

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NewestErrorConstants
open Real MeasureTheory ControlledProfile
open scoped NNReal

theorem output_congr (P Q:CanonicalCovariance.ProfileParameters)
    (hl:P.lower=Q.lower)(hu:P.upper=Q.upper)(hh:P.holder=Q.holder)(he:P.exponent=Q.exponent)
    (κ M:ℝ)(v b:ℝ≥0)(B Hr:ℝ)(k:ℕ)(B0:ℝ≥0)(A0 ν:ℝ):
    MixedPastNewestCurrentEnergy.constant κ (M:=M) P v b B Hr k B0 A0 ν=
      MixedPastNewestCurrentEnergy.constant κ (M:=M) Q v b B Hr k B0 A0 ν:=by
  simp only [MixedPastNewestCurrentEnergy.constant,collision_congr P Q hl hu hh he,
    ControlledOldIntervals.fraction,hl,hu,he,current_congr P Q hl hh he]

variable (D:SmoothApproximation.ScalarData){h:ℝ}(hh:0<h)(hh1:h≤1)
  (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*h^(D.beta/4)≤1/2)

/-- The whole repaired q-integrated error coefficient is independent of
the canonical smoothing index, including the original collision budget. -/
theorem canonical_output (κ M:ℝ)(v b:ℝ≥0)(B Hr:ℝ)(k:ℕ)(B0:ℝ≥0)(A0 ν:ℝ)(j:ℕ):
    MixedPastNewestCurrentEnergy.constant κ (M:=M)
      (ControlledSmoothLimit.smoothTotalParameters D hh hh1 hsmall j) v b B Hr k B0 A0 ν=
    MixedPastNewestCurrentEnergy.constant κ (M:=M)
      (ControlledSmoothLimit.roughTotalParameters D hh hh1 hsmall) v b B Hr k B0 A0 ν:=by
  apply output_congr <;> rfl

end SHE.NewestErrorConstants
