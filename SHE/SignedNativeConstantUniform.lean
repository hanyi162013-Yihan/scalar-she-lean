module

public import SHE.PastSignedEndpointTime
public import SHE.ControlledSmoothLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SHE.SignedNativeConstantUniform
open scoped NNReal

/-- Complete physical old-word moments involve only the scalar upper
bound and exponent; no derivative of the companion coefficient enters. -/
theorem moment (P Q:CanonicalCovariance.ProfileParameters)(hu:P.upper=Q.upper)(he:P.exponent=Q.exponent)
    (r m b:ℕ)(C0:ℝ):
    MixedPastWordMoments.momentConstant P r m b C0=MixedPastWordMoments.momentConstant Q r m b C0:=by
  simp only [MixedPastWordMoments.momentConstant,FullResidualAssignedMoments.constant,
    OffsetAssignedLeafMoments.leafConstant,hu,he]

variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall

theorem actual_moment (n k p:ℕ)(B0:ℝ≥0)(κ M:ℝ):
    MixedPastWordMoments.momentConstant (Smooth n) k k p
      ((k:ℝ)*(NativeHybridMoments.momentConstant (p*(k+2)) B0 κ M)^(Smooth n).exponent)=
    MixedPastWordMoments.momentConstant Rough k k p
      ((k:ℝ)*(NativeHybridMoments.momentConstant (p*(k+2)) B0 κ M)^(Rough).exponent):=by
  apply moment <;> rfl

theorem coefficients (n k:ℕ)(J ρ η U C:ℝ):
    PastSignedEndpointTime.goodCoefficient (Smooth n) k J ρ η=
      PastSignedEndpointTime.goodCoefficient Rough k J ρ η ∧
    PastSignedEndpointTime.badCoefficient (Smooth n) k U C=
      PastSignedEndpointTime.badCoefficient Rough k U C ∧
    ControlledOldIntervals.fraction (Smooth n)*(Smooth n).lower=
      ControlledOldIntervals.fraction Rough*(Rough).lower:=by
  exact ⟨rfl,rfl,rfl⟩

end SHE.SignedNativeConstantUniform
