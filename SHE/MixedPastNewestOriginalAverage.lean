module
public import SHE.MixedPastNewestOriginalMass
public import SHE.RootSectionParameterSwap
public import SHE.MixedPastNewestIntegratedError
public import SHE.ControlledNewestNodeMass
public import SHE.RootSectionAverage
public import SHE.NewestIntegratedConstants
public import SHE.MixedPastNewestTimeFields
public import SHE.NewestErrorConstants
public import SHE.ScalarApproximationDiscrepancy
public import SHE.PastNewestOldTimeEnergy
public import SHE.MixedPastNewestFields
public import SHE.ParentScoreInput
public import SHE.ParentMeanMass
public import SHE.WeightedSFiniteMoments
public import SHE.PastWordTimeFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
namespace SHE.MixedPastNewestOriginalAverage
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestOriginalAverage_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestOriginalAverage_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestOriginalAverage_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestOriginalAverage_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestOriginalAverage_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestOriginalAverage_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestOriginalAverage_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestOriginalAverage_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestOriginalAverage_period : Fact (0<2*π):=⟨by positivity⟩
attribute [local irreducible] MixedPastNewestError.value WordRecursion.directionalSecond
  GaussianConvolution.gaussianAverage UncutSmoothWords.test MeasurableGaussianScores.scoreVariance
  MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Value"=>MixedPastNewestError.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

open HistoryProductMeasure OrderedHeatForests
open ActualMeanKernel
local notation "Active"=>MixedPastNewestFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

local notation "R₀"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
local notation "U"=>MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir"=>MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean"=>MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

/-- Current-time integration commutes with the ORIGINAL old history,
with the root retained. The fixed-index absolute bound justifies the
interchange; it does not alter the uniform approximation estimate. -/
theorem drift_eq_original_average
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (k:ℕ)(ε:ℝ)(hε:0≤ε)(e:(ℝ≥0×Ω)×HeatCircle→ℝ)(he:Measurable e)(hecap:∀p,|e p|≤ε):
    ∀ᵐz:Ω×HeatCircle∂μ.prod haarAddCircle,
      MixedPastNewestIntegratedError.drift 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k 0 e (z.2,z.1)=
      RootSectionAverage.average R₀ k
        (MixedPastNewestOriginalMass.primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP v b hvb Z htarget hstop F hF hFm k e) z:=by
  let f:=MixedPastNewestOriginalMass.current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k e
  have hm:=MixedPastNewestOriginalMass.current_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k e he
  have hi:=MixedPastNewestOriginalMass.joint_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages k ε hε e he hecap
  have hswap:=RootSectionAverage.parameter_integral_ae R₀ k
    (volume.restrict (Ioc (v:ℝ) (b:ℝ))) μ f hm hi
  filter_upwards [hswap] with z hz
  exact hz.2

end SHE.MixedPastNewestOriginalAverage
