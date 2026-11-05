module

public import SHE.MixedPastProfileDerivative
public import SHE.MixedPastBaselineHistoryMass
public import SHE.MixedPastBaselineRMS
public import SHE.HistoryAverageEnergy
public import SHE.HistoryRelativeSample
public import SHE.MixedNativeBaselineJointFields
public import SHE.MixedPastBaselineSpatialMass
public import SHE.MixedPastBaselineSpatialFields
public import SHE.PastBaselineTimeFields
public import SHE.HilbertFiniteAverage
public import SHE.MixedPastBaselineSpatialEnergy
public import SHE.BaselineStrictSupport
public import SHE.MixedPastBaselineLeafEnergy
public import SHE.MixedPastOmittedLeafAbsolute
public import SHE.FiniteSpatialBaseline
public import SHE.MixedPastBaselineFTCIdentity
public import SHE.MixedPastOmittedLeafSpatial
public import SHE.MixedPastBaselineEnergySections
public import SHE.BaselineUnitGain
public import SHE.ForestLeafMarkEnergy
public import SHE.MixedPastOmittedLeafMoments
public import SHE.ScalarRootSharpSections
public import SHE.HistoryRelativeSections
public import SHE.MixedPastDerivativeRMS
public import SHE.MixedPastOmittedMarkFields
public import SHE.MixedPastLiteralOmitted
public import SHE.ControlledThetaOmittedFields
public import SHE.ControlledFamilyProfileMarkFields
public import SHE.MixedPastLiteralFields
public import SHE.JointInterpolationFields
public import SHE.WeightedRowTimeShift
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledThetaWeightedFields
public import SHE.MixedPastDecayedWord
public import SHE.RelativeHistoryGeometry
public import SHE.ParentHeatFields
public import SHE.MixedPastActualMean
public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 650000

namespace SHE.MixedPastBaselineCurrentFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastBaselineCurrentFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastBaselineCurrentFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastBaselineCurrentFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastBaselineCurrentFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastBaselineCurrentFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastBaselineCurrentFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastBaselineCurrentFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastBaselineCurrentFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastBaselineCurrentFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v


open HistoryProductMeasure ScalarRootRelativeGeometry ProfileL2

open MixedPastBaselineSpatialEnergy MixedPastBaselineSpatialFields

local notation "Leg"=>MixedNativeMarkedBudgets.baseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Rzero"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)

def currentField (k : ℕ) (θ : ℝ) (z : ℝ≥0×Ω) : ℝ:=
  if v<z.1 ∧ z.1<b then ∫ h,Leg k θ z.1 z.2 h ∂historyMeasure Rzero haarAddCircle k else 0

/-- Genuine theta/current/sample Borel field of the literal canonical
baseline after ORIGINAL history averaging, with no random-reference
exceptional-set substitution. -/
theorem current_joint_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (fun z : ℝ×(ℝ≥0×Ω)=>currentField
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k z.1 z.2) := by
  have hh:=MixedNativeBaselineJointFields.history_average_joint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall haarAddCircle k
  have hmap : Measurable (fun z : ℝ×(ℝ≥0×Ω)=>((z.1,(z.2.1:ℝ)),z.2.2)):=
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd.fst)).prodMk measurable_snd.snd
  have hG : Measurable (fun z : ℝ×(ℝ≥0×Ω)=>∫ h,Leg k z.1 z.2.1 z.2.2 h ∂historyMeasure Rzero haarAddCircle k):=by
    convert! hh.comp hmap using 1
    funext z
    simp only [Function.comp_apply,Real.toNNReal_coe]
  have hset : MeasurableSet {z : ℝ×(ℝ≥0×Ω)|v<z.2.1 ∧ z.2.1<b}:=
    (measurableSet_lt (f:=fun _ : ℝ×(ℝ≥0×Ω)=>v)
      (g:=fun z=>z.2.1) measurable_const measurable_snd.fst).inter
      (measurableSet_lt (f:=fun z : ℝ×(ℝ≥0×Ω)=>z.2.1)
        (g:=fun _=>b) measurable_snd.fst measurable_const)
  exact hG.ite hset measurable_const

/-- There is no baseline derivative at depth zero, exactly rather than
by an estimate involving an artificial leading term. -/
theorem current_zero (θ : ℝ) (z : ℝ≥0×Ω) : currentField
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm 0 θ z=0 := by
  have hz (h : History HeatCircle 0) : Leg 0 θ z.1 z.2 h=0:=by
    unfold MixedNativeMarkedBudgets.baseline ControlledFamilyLegFubini.baseline
      ActualBaselineMarkFields.point PhysicalChainArrays.baselineMark
    split_ifs <;> simp only [Finset.univ_eq_empty,Finset.sum_empty,neg_zero]
  simp only [currentField,hz,integral_zero,ite_self]

end SHE.MixedPastBaselineCurrentFields
