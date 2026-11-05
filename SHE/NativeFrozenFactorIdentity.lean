module
public import SHE.NativeCanonicalGammaEnergy
public import SHE.NativeFrozenFactorGammaTime
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeFrozenFactorIdentity
open Set MeasureTheory NativeHeatObservation DyadicApproximation StoppedFourier
open scoped NNReal ENNReal
local instance nativeFrozenFactorIdentity_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeFrozenFactorIdentity_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeFrozenFactorIdentity_circleSigma : MeasurableSpace CircleL2:=borel _
local instance nativeFrozenFactorIdentity_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
/-- The literal frozen coefficient in the stochastic six-slot bound is
exactly the coefficient whose sharp initial/future time energy was
proved, at every original post-past time. -/
theorem coefficient_eq (U V : ℝ≥0×Ω→RealL2) (P : CanonicalCovariance.ProfileParameters)
    (Λ κ : ℝ) (hκP : κ<P.lower) {m W:ℝ} (hmP:m≤P.lower-κ) (hWP:P.upper-κ≤W)
    (v q : ℝ≥0) (hvq:v<q) (θ:ℝ) (ω:Ω) :
    (NativeCanonicalGammaEnergy.frozen (v:=v) (U:=U) (V:=V) (P:=P) (Λ:=Λ) (κ:=κ)
      (hκP:=hκP) (hmP:=hmP) (hWP:=hWP) θ (q,ω)).val=
    NativeFrozenFactorGammaTime.coefficient P Λ κ hκP
      (fun ω=>embed (U (v,ω))) (fun ω=>embed (V (v,ω)-U (v,ω))) θ ((q:ℝ)-(v:ℝ)) ω := by
  unfold NativeCanonicalGammaEnergy.frozen NativeCanonicalGammaEnergy.widen FrozenReferenceFields.field
  rw [PredictablePastParameter.held_eq _ _ hvq]
  rfl
end SHE.NativeFrozenFactorIdentity
