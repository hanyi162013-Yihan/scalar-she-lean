module

public import SHE.MixedPastCovarianceTimeFields
public import SHE.PastCovarianceRMS
public import SHE.MixedPastCovarianceSpatialAbsoluteUniform
public import SHE.HistoryRelativeSample
public import SHE.HistoryAverageEnergy
public import SHE.MixedPastCovarianceAverageUniform
public import SHE.MixedPastCovarianceHistoryEnergy
public import SHE.MixedNativeCovarianceJointFields
public import SHE.MixedNativeCovarianceFTCIdentity
public import SHE.PastCovarianceCurrentBudget
public import SHE.SectionEnergy
public import SHE.RandomScoreSpatialAverage
public import SHE.HistoryRelativeOldFirst
public import SHE.ScalarRootSharpSections
public import SHE.MixedPastScoreEnergy
public import SHE.RandomFutureCenters
public import SHE.PastMeanSections
public import SHE.QuarterSpatialEvent
public import SHE.PastCovarianceMassSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastCovarianceCurrentFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceCurrentFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceCurrentFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceCurrentFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceCurrentFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceCurrentFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceCurrentFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastCovarianceCurrentFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceCurrentFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceCurrentFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open ScalarRootRelativeGeometry ControlledResidualScoreInput MeasurableGaussianScores
  ProfileStability QuarterSpatialEvent OrderedHeatForests
local notation "Actual" => MixedPastLiteralCovariance.actualPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "Point" => MixedPastCovarianceSpatialFields.relativePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mass" => MixedPastCovarianceSpatialFields.scoreMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "Leg" => MixedNativeMarkedBudgets.covariance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "R₀" => referenceData P P.coefficient haP Λ 0 v b hvb (0,0)

/-- Literal original-history covariance integral on the open current
window; endpoint values do not enter the current-time energy. -/
def currentField (k : ℕ) (θ : ℝ) (z : ℝ≥0×Ω) : ℝ :=
  if v<z.1 ∧ z.1<b then ∫ h,Leg k θ z.1 z.2 h ∂historyMeasure R₀ haarAddCircle k else 0

theorem current_joint_measurable (hΛ : 0≤Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (fun z : ℝ×(ℝ≥0×Ω)=>currentField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k z.1 z.2) := by
  have hh:=MixedNativeCovarianceJointFields.history_average_joint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      hΛ hsmallPoint haarAddCircle k
  have hmap : Measurable (fun z : ℝ×(ℝ≥0×Ω)=>((z.1,(z.2.1:ℝ)),z.2.2)):=
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd.fst)).prodMk measurable_snd.snd
  have hG : Measurable (fun z : ℝ×(ℝ≥0×Ω)=>∫ h,Leg k z.1 z.2.1 z.2.2 h ∂historyMeasure R₀ haarAddCircle k):=by
    have hr:=hh.comp hmap
    change Measurable (fun z : ℝ×(ℝ≥0×Ω)=>∫ h,Leg k z.1 ((z.2.1:ℝ).toNNReal) z.2.2 h ∂historyMeasure R₀ haarAddCircle k) at hr
    simpa only [Real.toNNReal_coe] using hr
  have hset : MeasurableSet {z : ℝ×(ℝ≥0×Ω)|v<z.2.1 ∧ z.2.1<b}:=
    (measurableSet_Ioo : MeasurableSet (Ioo v b)).preimage measurable_snd.fst
  exact hG.ite hset measurable_const

end SHE.MixedPastCovarianceCurrentFields
