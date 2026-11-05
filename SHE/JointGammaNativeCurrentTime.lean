module

public import SHE.JointGammaCurrentTime
public import SHE.NativeJointCurrentSections
public import SHE.JointGammaCurrentIdentity
public import SHE.NativeJointGammaCurrent
public import SHE.JointInterpolationFields
public import SHE.ScalarCovarianceTailScale
public import SHE.NativeScalarProductAlgebra
public import SHE.JointGammaAffine
public import SHE.FirstGammaEndpointPhysical
public import SHE.FirstGammaEndpointCoherence
public import SHE.FirstGammaCurrentIdentity
public import SHE.FirstGammaEndpointConstruction
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaRows
public import SHE.RescaledRowsCoherence
public import SHE.FiniteSpliceStopCoherence
public import SHE.FirstGammaEndpointRows
public import SHE.SingularReferenceSplice
public import SHE.FullHorizonEndpointVersion
public import SHE.SingularInputBounds
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.MixedNativeFrozenInterpolationRows
public import SHE.MixedNativeFrozenPrefixValues
public import SHE.FiniteReferenceSplicePast
public import SHE.StoppedInputAlgebra
public import SHE.PastFrozenPrefixRows
public import SHE.MixedPastJointData
public import SHE.FiniteReferenceSplice
public import SHE.MixedNativeJointPhysical
public import SHE.MixedNativePairMartingale
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2300000

namespace SHE.JointGammaNativeCurrentTime
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaNativeCurrentTime_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaNativeCurrentTime_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaNativeCurrentTime_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaNativeCurrentTime_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaNativeCurrentTime_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaNativeCurrentTime_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaNativeCurrentTime_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaNativeCurrentTime_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v b : ℝ≥0) (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hbH : b≤H)


local instance jointGammaNativeCurrentTime_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance jointGammaNativeCurrentTime_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointGammaNativeCurrentTime_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointGammaNativeCurrentTime_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
attribute [local irreducible] FirstGammaEndpointConstruction.value NativeJointGammaCurrent.state

include hH B hBDG hIJ₀ hIJ₁ in
/-- Genuine native-root/original-time/sample coherence for the actual
finite joint current. No fixed-time exceptional set is substituted. -/
theorem current_eq_field_time (hb0:0<b) (θ:ℝ):
    ∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐp∂energyMeasure μ H,v<p.1→p.1<b→
      JointGammaAffine.current 1 Λ θ (fun _=>(b:ℝ))
        (FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (ScalarCovarianceTailScale.observation b x) J P hκP hΛ v b (fun _=>le_rfl) hbH θ p) 0=
      PredictableScalarField.nativeField
        (NativeJointGammaCurrent.state (Function.uncurry S.first) (Function.uncurry S.second) Λ θ b) (p,x):=by
  haveI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  have hn:=NativeJointCurrentSections.product_ae 𝓕 (energyMeasure μ H)
    (Function.uncurry S.first) (Function.uncurry S.second) S.first_predictable S.second_predictable Λ θ b
  filter_upwards [hn] with x hx
  filter_upwards [hx,JointGammaCurrentTime.current_eq_joint_time 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S (ScalarCovarianceTailScale.observation b x) J P hκP hΛ v b
      (fun _=>le_rfl) hbH hH B hBDG hIJ₀ hIJ₁ hb0 θ] with p hn hc hvp hpb
  exact (hc hvp hpb 0).trans (hn hpb).symm

end SHE.JointGammaNativeCurrentTime
