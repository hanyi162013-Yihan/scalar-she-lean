module

public import SHE.MixedPastNativeKernelActual
public import SHE.ControlledSmoothLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.NativeKernelConstantCongruence

theorem whole (P Q:CanonicalCovariance.ProfileParameters)
    (hu:P.upper=Q.upper)(he:P.exponent=Q.exponent)(r m b:ℕ)(C0:ℝ):
    NativeFirstWholeComplete.momentConstant P r m b C0=
      NativeFirstWholeComplete.momentConstant Q r m b C0:=by
  simp only [NativeFirstWholeComplete.momentConstant,NativeFirstWholeMoments.constant,
    OffsetAssignedLeafMoments.leafConstant,hu,he]

theorem twoFresh (P Q:CanonicalCovariance.ProfileParameters)
    (hu:P.upper=Q.upper)(he:P.exponent=Q.exponent)(r m b:ℕ)(C0:ℝ):
    TwoFreshCompleteWord.momentConstant P r m b C0=
      TwoFreshCompleteWord.momentConstant Q r m b C0:=by
  simp only [TwoFreshCompleteWord.momentConstant,TwoFreshFullResidualMoments.constant,
    OffsetAssignedLeafMoments.leafConstant,hu,he]

theorem omitted (P Q:CanonicalCovariance.ProfileParameters)
    (hu:P.upper=Q.upper)(he:P.exponent=Q.exponent)(r m:ℕ)(j:Fin m)(b:ℕ)(C0:ℝ):
    NativeOmittedCompleteWord.momentConstant P r m j b C0=
      NativeOmittedCompleteWord.momentConstant Q r m j b C0:=by
  simp only [NativeOmittedCompleteWord.momentConstant,NativeFirstOmittedMoments.constant,
    OffsetAssignedLeafMoments.leafConstant,hu,he]

theorem packet (P Q:CanonicalCovariance.ProfileParameters)
    (hu:P.upper=Q.upper)(he:P.exponent=Q.exponent)(r m b:ℕ):
    MixedPastNativePacketUniform.constant P r m b=MixedPastNativePacketUniform.constant Q r m b:=by
  simp only [MixedPastNativePacketUniform.constant,whole P Q hu he,twoFresh P Q hu he]

theorem sharp (P Q:CanonicalCovariance.ProfileParameters)
    (hl:P.lower=Q.lower)(hh:P.holder=Q.holder)(he:P.exponent=Q.exponent):
    ControlledProfile.sharpUnit P=ControlledProfile.sharpUnit Q:=by
  simp only [ControlledProfile.sharpUnit,hl,hh,he]

theorem baseline (P Q:CanonicalCovariance.ProfileParameters)
    (hl:P.lower=Q.lower)(he:P.exponent=Q.exponent):
    BaselineOriginalGain.unitCoefficient P=BaselineOriginalGain.unitCoefficient Q:=by
  simp only [BaselineOriginalGain.unitCoefficient,hl,he]

variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall

/-- Every complete native packet coefficient is exactly uniform in the
canonical smooth companion index. No coefficient derivative is present. -/
theorem canonical (n r m b:ℕ)(C0:ℝ):
    NativeFirstWholeComplete.momentConstant (Smooth n) r m b C0=
      NativeFirstWholeComplete.momentConstant Rough r m b C0 ∧
    TwoFreshCompleteWord.momentConstant (Smooth n) r m b C0=
      TwoFreshCompleteWord.momentConstant Rough r m b C0 ∧
    (∀j:Fin m,NativeOmittedCompleteWord.momentConstant (Smooth n) r m j b C0=
      NativeOmittedCompleteWord.momentConstant Rough r m j b C0) ∧
    MixedPastNativePacketUniform.constant (Smooth n) r m b=MixedPastNativePacketUniform.constant Rough r m b ∧
    ControlledProfile.sharpUnit (Smooth n)=ControlledProfile.sharpUnit Rough ∧
    BaselineOriginalGain.unitCoefficient (Smooth n)=BaselineOriginalGain.unitCoefficient Rough:=by
  refine ⟨?_,?_,fun j=>?_,?_,?_,?_⟩
  · apply whole <;> rfl
  · apply twoFresh <;> rfl
  · apply omitted <;> rfl
  · apply packet <;> rfl
  · apply sharp <;> rfl
  · apply baseline <;> rfl

end SHE.NativeKernelConstantCongruence
