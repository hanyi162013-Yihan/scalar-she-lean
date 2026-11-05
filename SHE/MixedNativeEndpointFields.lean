module

public import SHE.MixedNativeEndpointMoments
public import SHE.ControlledProfileFamilies
public import SHE.MixedNativeJointHistory
public import SHE.MixedNativePastThetaCentering
public import SHE.HeatPhysicalSubsequence
public import SHE.ObservationTargetContinuity
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedNativeEndpointFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeEndpointFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeEndpointFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeEndpointFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeEndpointFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeEndpointFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeEndpointFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)


local instance mixedNativeEndpointFields_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeEndpointFields_circleCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance mixedNativeEndpointFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeEndpointFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩

/-- Joint Borel dependence of the genuine zero-age offset, allowing
all clocks, interpolation parameters and original centers to vary. -/
theorem offset_variable_measurable {W : Type*} [MeasurableSpace W]
    (θ : W → ℝ) (v q : W → ℝ≥0) (x : W → HeatCircle) (ω : W → Ω)
    (hθ : Measurable θ) (hv : Measurable v) (hq : Measurable q)
    (hx : Measurable x) (hω : Measurable ω) :
    Measurable (fun w => MixedNativeEndpointLimit.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (θ w) (v w) (q w) (x w) (ω w)) := by
  have hp : Measurable (fun w => (ω w,((q w:ℝ),x w))) :=
    hω.prodMk ((measurable_coe_nnreal_real.comp hq).prodMk hx)
  have hU := (PredictableScalarField.wordField_measurable 𝓕 S.first_predictable).comp hp
  have hV := (PredictableScalarField.wordField_measurable 𝓕 S.second_predictable).comp hp
  have hu : Measurable (fun w => S.first (v w) (ω w)) :=
    (S.first_predictable.mono (predictable_le_product 𝓕)).measurable.comp (hv.prodMk hω)
  have huc : Measurable (fun w => embed (S.first (v w) (ω w))) := embed.continuous.measurable.comp hu
  have hvc : Measurable (fun w => embed (S.second (v w) (ω w))) := embed.continuous.measurable.comp
    ((S.second_predictable.mono (predictable_le_product 𝓕)).measurable.comp (hv.prodMk hω))
  have hdc : Measurable (fun w => embed (S.second (v w) (ω w)-S.first (v w) (ω w))) := by
    convert hvc.sub huc using 1
    funext w
    exact map_sub embed _ _
  have harg := ((huc.prodMk hdc).prodMk hθ).prodMk
      (((measurable_coe_nnreal_real.comp hq).sub (measurable_coe_nnreal_real.comp hv)).prodMk hx)
  have hb := (ControlledProfile.meanFamily_measurable Λ).comp harg
  exact (hU.add (hθ.mul (hV.sub hU))).sub hb

theorem offset_measurable (θ : ℝ) (v q : ℝ≥0) (x : HeatCircle) :
    Measurable (MixedNativeEndpointLimit.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q x) :=
  offset_variable_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (fun _ => θ) (fun _ => v) (fun _ => q) (fun _ => x) id
    measurable_const measurable_const measurable_const measurable_const measurable_id

omit [IsProbabilityMeasure μ] in
/-- The endpoint field is literally the scalar representative used by
the actual native recursive words. -/
theorem offset_eq_physicalField (θ : ℝ) (v q : ℝ≥0) (x : HeatCircle) (ω : Ω) :
    MixedNativeEndpointLimit.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q x ω=
      (MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField (ω,((q:ℝ),x))+
      θ*((MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField (ω,((q:ℝ),x))-
        (MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField (ω,((q:ℝ),x)))-
      ControlledProfile.mean Λ (embed (S.first v ω)) (embed (S.second v ω-S.first v ω))
        (θ,((q:ℝ)-(v:ℝ),x)) := rfl

end SHE.MixedNativeEndpointFields
