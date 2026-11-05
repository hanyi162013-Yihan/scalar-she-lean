module
public import SHE.MixedPastNewestCollision
public import SHE.PastNewestCurrentBudget
public import SHE.ControlledSmoothLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.NewestErrorConstants
open Real MeasureTheory
open scoped NNReal

theorem moment_congr (P Q:CanonicalCovariance.ProfileParameters)
    (hu:P.upper=Q.upper)(he:P.exponent=Q.exponent)(r m b:ℕ)(C0:ℝ):
    MixedPastWordMoments.momentConstant P r m b C0=
      MixedPastWordMoments.momentConstant Q r m b C0:=by
  simp only [MixedPastWordMoments.momentConstant,FullResidualAssignedMoments.constant,
    OffsetAssignedLeafMoments.leafConstant,hu,he]

theorem collision_congr (P Q:CanonicalCovariance.ProfileParameters)
    (hl:P.lower=Q.lower)(hu:P.upper=Q.upper)(hh:P.holder=Q.holder)(he:P.exponent=Q.exponent)
    (κ M B Hr:ℝ)(k:ℕ)(B0:ℝ≥0):
    MixedPastNewestCollision.constant κ (M:=M) P B Hr k B0=
      MixedPastNewestCollision.constant κ (M:=M) Q B Hr k B0:=by
  simp only [MixedPastNewestCollision.constant,MixedPastNewestInterpolation.holderCost,
    IntervalScoreHolderMass.constant,he,hl,hu,hh,moment_congr P Q hu he]

theorem current_congr (P Q:CanonicalCovariance.ProfileParameters)
    (hl:P.lower=Q.lower)(hh:P.holder=Q.holder)(he:P.exponent=Q.exponent)
    (ell:ℝ)(C:ℕ→ℝ)(n k:ℕ)(span fresh A0 ν:ℝ):
    PastNewestTimeIntegral.currentConstant P ell C n k span fresh A0 ν=
      PastNewestTimeIntegral.currentConstant Q ell C n k span fresh A0 ν:=by
  simp only [PastNewestTimeIntegral.currentConstant,PhysicalAssignmentGapScale.prefactor,
    PhysicalAssignmentGapScale.leafPrefactor,hl,hh,he]

variable (D:SmoothApproximation.ScalarData){h:ℝ}(hh:0<h)(hh1:h≤1)
  (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*h^(D.beta/4)≤1/2)

/-- The repaired actual-error constants are identical at every canonical
companion index. No approximation-dependent derivative bound occurs. -/
theorem canonical_collision (κ M B Hr:ℝ)(k:ℕ)(B0:ℝ≥0)(j:ℕ):
    MixedPastNewestCollision.constant κ (M:=M) (ControlledSmoothLimit.smoothTotalParameters D hh hh1 hsmall j) B Hr k B0=
      MixedPastNewestCollision.constant κ (M:=M) (ControlledSmoothLimit.roughTotalParameters D hh hh1 hsmall) B Hr k B0:=by
  apply collision_congr <;> rfl

theorem canonical_current (ell:ℝ)(C:ℕ→ℝ)(n k:ℕ)(span fresh A0 ν:ℝ)(j:ℕ):
    PastNewestTimeIntegral.currentConstant (ControlledSmoothLimit.smoothTotalParameters D hh hh1 hsmall j)
      ell C n k span fresh A0 ν=
    PastNewestTimeIntegral.currentConstant (ControlledSmoothLimit.roughTotalParameters D hh hh1 hsmall)
      ell C n k span fresh A0 ν:=by
  apply current_congr <;> rfl

end SHE.NewestErrorConstants
