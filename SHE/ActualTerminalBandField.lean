module
public import SHE.ActualFiniteGaussianComparison
public import SHE.NativeBesselParameterSection
public import SHE.MixedFirstDefectHeatBandBound
public import SHE.MixedFirstDefectFiniteBandEnergy
public import SHE.DefectGapFiniteCoefficient
public import SHE.MixedFirstDefectActualBound
public import SHE.ScalarHeatRootBands
public import SHE.JointGammaRootHilbertPair
public import SHE.MixedFirstDefectNativeBound
public import SHE.MixedFirstDefectEnvelopeIdentity

public import SHE.MixedFirstDefectNormEnvelope
public import SHE.MixedFirstDefectConvolutionTransport
public import SHE.MixedFirstDefectMinkowski
public import SHE.MixedFirstDefectDisintegration
public import SHE.NativeBesselParameterSection
public import SHE.MixedFirstDefectIntegral
public import SHE.MixedJointActiveVolume
public import SHE.MixedFirstDefectRMS
public import SHE.ControlledReferenceFamilyDefectL1
public import SHE.RootHistoryCurrentMeasure
public import SHE.NativeBesselParameterAverageAE
public import SHE.HistoryMeasureGeometry
public import SHE.MixedCanonicalRootFields
public import SHE.DefectRelativeFactor
public import SHE.DefectCombinedTime
public import SHE.NativeBesselFieldAE
public import SHE.NativeSignedHaarProcess
public import SHE.ControlledScalarReference
public import SHE.ControlledThetaDefectEnvelope
public import SHE.MixedJointUncutDefectTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.ActualTerminalBandField
open Set MeasureTheory Real AddCircle StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
  NativeHeatObservation CutoffWordLevel CutoffWordHistories CutoffCarriers ControlledProfile
  ControlledReferenceLevel PhysicalChainArrays PhysicalParentGeometry PhysicalScoreChain HistoryProductMeasure
  CoveredControlledLaw
open scoped NNReal ENNReal BigOperators
open Classical
local instance mixedFirstDefectRMS_period:Fact (0<2*π):=⟨by positivity⟩
local instance mixedFirstDefectRMS_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedFirstDefectRMS_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedFirstDefectRMS_borel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
local instance :MeasurableSpace RealL2:=borel _
local instance :BorelSpace RealL2:=⟨rfl⟩
variable {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a)(j:ℕ)
variable (hL:1≤Λ){ρ:ℝ}(hρ:0<ρ)
def scalar(z:(ℝ≥0×Ω)×HeatCircle):ℂ:=
  (ScalarHeatBands.band a (j+1) (PredictableScalarField.nativeField (Function.uncurry S.second) z)-
    ScalarHeatBands.band a (j+1) (PredictableScalarField.nativeField (Function.uncurry S.first) z):ℝ)
local notation "Scalar"=>scalar 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (a:=a) j

include ha in
theorem scalar_measurable:Measurable Scalar:=by
  have hU:Measurable (Function.uncurry S.first):=
    S.first_predictable.measurable.mono (predictable_le_product 𝓕) le_rfl
  have hV:Measurable (Function.uncurry S.second):=
    S.second_predictable.measurable.mono (predictable_le_product 𝓕) le_rfl
  have hb:Measurable (ScalarHeatBands.band a (j+1)):=
    (ScalarHeatBands.band_boundedSmooth ha (j+1)).smooth.continuous.measurable
  exact Complex.measurable_ofReal.comp ((hb.comp (PredictableScalarField.nativeField_measurable hV)).sub
    (hb.comp (PredictableScalarField.nativeField_measurable hU)))

def value:ℝ≥0×Ω→CircleL2:=NativeBesselFieldAE.value Λ ρ hL hρ.le Scalar
local notation "Value"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (a:=a) j hL hρ

include ha in
theorem measurable:Measurable Value:=NativeBesselFieldAE.measurable Λ ρ hL hρ.le Scalar
  (scalar_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ha j)

/-- Exact actual terminal slot in the stochastic finite comparison. -/
theorem at_time(b:ℝ≥0)(ω:Ω):Value (b,ω)=ActualFiniteGaussianComparison.terminal
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S b (a:=a) j hL hρ ω:=by
  apply NativeBesselParameterSection.congr
  funext x
  rfl
end SHE.ActualTerminalBandField
