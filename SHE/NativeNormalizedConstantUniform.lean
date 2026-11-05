module

public import SHE.MixedPastNativeEnergyNormalization
public import SHE.NativeKernelConstantCongruence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.NativeNormalizedConstantUniform
open scoped NNReal
variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall

theorem current (κ M:ℝ)(k p:ℕ)(χ Cdim:ℝ)(B0:ℝ≥0)(n:ℕ):
    MixedPastNativeEnergyNormalization.currentCoefficient κ (M:=M) (Smooth n) k p χ Cdim B0=
      MixedPastNativeEnergyNormalization.currentCoefficient κ (M:=M) Rough k p χ Cdim B0:=by
  unfold MixedPastNativeEnergyNormalization.currentCoefficient
  rw [NativeKernelConstantCongruence.packet (Smooth n) Rough rfl rfl]
  rfl

theorem past (κ M:ℝ)(k:ℕ)(B0:ℝ≥0)(n:ℕ):
    MixedPastNativeEnergyNormalization.pastCoefficient κ (M:=M) (Smooth n) k B0=
      MixedPastNativeEnergyNormalization.pastCoefficient κ (M:=M) Rough k B0:=by
  unfold MixedPastNativeEnergyNormalization.pastCoefficient
  dsimp only
  rw [NativeKernelConstantCongruence.twoFresh (Smooth n) Rough rfl rfl]
  simp_rw [NativeKernelConstantCongruence.omitted (Smooth n) Rough rfl rfl]
  rfl

end SHE.NativeNormalizedConstantUniform
