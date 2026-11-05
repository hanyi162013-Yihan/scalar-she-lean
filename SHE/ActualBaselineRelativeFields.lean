module

public import SHE.ActualInterpolatedMeanFields
public import SHE.ActualBaselineMarkFields
public import SHE.ControlledScoreRates
public import SHE.ForestTranslation
public import SHE.FullResidualInterpolatedWeightedMoments
public import SHE.JointInterpolationFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace SHE.ActualBaselineRelativeFields
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  GaussianCoordinates ProjectedUncutWord PhysicalScoreChain PhysicalChainArrays GaussianConvolution
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry
  CoveredTerminalFactors CoveredTerminalMoments NativePhysicalWord
open scoped NNReal ENNReal BigOperators
local instance actualBaselineRelativeLocal11 : Fact (0<2*π) := ⟨by positivity⟩
local instance actualBaselineRelativeLocal12 : MeasurableSpace RealL2 := borel _
local instance actualBaselineRelativeLocal13 : BorelSpace RealL2 := ⟨rfl⟩
local instance actualBaselineRelativeLocal14 : MeasurableSpace CircleL2 := borel _
local instance actualBaselineRelativeLocal15 : BorelSpace CircleL2 := ⟨rfl⟩
local instance actualBaselineRelativeLocal16 : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance actualBaselineRelativeLocal17 : MeasurableSpace RealHaarInput := borel _
local instance actualBaselineRelativeLocal18 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance actualBaselineRelativeLocal19 : MeasurableSpace (Both RealHaarInput) := borel _
local instance actualBaselineRelativeLocal20 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P : CanonicalCovariance.ProfileParameters) (haP : SmoothCylinders.BoundedSmooth P.coefficient)
variable (θ : ℝ)
variable (L : CutoffWordLevel.Level
  (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) θ) HeatCircle 1)



open HistoryProductMeasure ActualMeanKernel ProfilePointwise ProfileStability ControlledScoreRates

def relativePoint (k : ℕ) (q : ℝ≥0) (t : Fin k→ℝ)
    (z : (Ω×HeatCircle)×(Fin k→HeatCircle)) : ℝ :=
  let p := separated k (z.1.2,t,fun i=>z.2 i+z.1.2)
  ActualBaselineMarkFields.point L (referenceProfile P Λ (embed u₀) (embed (v₀-u₀))) k q
    (ControlledBaselineAssignments.derivatives P haP Λ (embed u₀) (embed (v₀-u₀)) θ L k p)
    (FullResidualInterpolatedWeightedMoments.actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S P haP θ L k q z.1.1 p) p

theorem relative_point_measurable (hΛ : 0≤Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (q : ℝ≥0) (t : Fin k→ℝ) :
    Measurable (relativePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k q t) := by
  let p : (Ω×HeatCircle)×(Fin k→HeatCircle)→History HeatCircle k :=
    fun z=>separated k (z.1.2,t,fun i=>z.2 i+z.1.2)
  have hsites : Measurable (fun z : (Ω×HeatCircle)×(Fin k→HeatCircle)=>fun i=>z.2 i+z.1.2) :=
    Measurable.of_eval (fun i=>((measurable_pi_apply i).comp measurable_snd).add measurable_fst.snd)
  have hp : Measurable p := (separated_measurable k).comp
    (measurable_fst.snd.prodMk (measurable_const.prodMk hsites))
  have hM := ActualInterpolatedMeanFields.actual_mean_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S P haP θ L k q
  have hm : Measurable (fun z : (Ω×HeatCircle)×(Fin k→HeatCircle)=>
      FullResidualInterpolatedWeightedMoments.actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ v₀ S P haP θ L k q z.1.1 (p z)) := by
    convert! hM.comp (measurable_fst.fst.prodMk hp) using 1
  have hdb : Measurable (fun z : (Ω×HeatCircle)×(Fin k→HeatCircle)=>
      ControlledBaselineAssignments.derivatives P haP Λ (embed u₀) (embed (v₀-u₀)) θ L k (p z)) := by
    apply Measurable.of_eval
    intro j
    convert! (ControlledProfile.derivative_measurable P hΛ (embed u₀) (embed (v₀-u₀)) hsmallPoint).comp
      ((((lower_measurable L k j).comp hp).prodMk ((space_measurable k j).comp hp)).prodMk measurable_const) using 1
  exact ActualBaselineMarkFields.point_variable_measurable L
    (referenceProfile P Λ (embed u₀) (embed (v₀-u₀)))
    (referenceProfile_measurable P Λ (embed u₀) (embed (v₀-u₀))) k p hp
    (fun _=>q) measurable_const _ hm _ hdb

end SHE.ActualBaselineRelativeFields
