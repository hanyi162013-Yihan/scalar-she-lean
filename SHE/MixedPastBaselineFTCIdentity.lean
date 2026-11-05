module

public import SHE.MixedPastBaselineIdentity
public import SHE.ControlledFamilyBaselineLeg
public import SHE.ControlledFamilyLegFubini
public import SHE.MixedPastLiteralMean
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
set_option maxHeartbeats 2200000

namespace SHE.MixedPastBaselineFTCIdentity
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastBaselineFTCIdentity_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastBaselineFTCIdentity_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastBaselineFTCIdentity_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastBaselineFTCIdentity_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastBaselineFTCIdentity_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastBaselineFTCIdentity_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastBaselineFTCIdentity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastBaselineFTCIdentity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastBaselineFTCIdentity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v


local notation "Mean"=>MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Input"=>MixedPastOmittedMarkFields.leafInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Leaf"=>MixedPastOmittedMarkFields.leafMark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "LP"=>ControlledFamilyThreeLeg.leafPoint P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm

/-- The mean in the canonical three-leg FTC is exactly the native
random-past joint mean used by the literal conditional omitted words. -/
theorem mean_eq_meanField
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (k : ℕ) (h : History X k) (θ : ℝ) (q : ℝ≥0)
    (hq : (q:ℝ)<(carrier Zero k).terminal h) (ω : Ω) :
    ControlledFamilyActualTransfer.mean P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (U ω,Dir ω) k h q (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) θ=
      Mean k θ q ω h := by
  unfold ControlledFamilyActualTransfer.mean ControlledFamilyThreeLeg.center
  rw [ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (0,(U ω,Dir ω)) (0,(0,0)) k h]
  have he:=MixedPastLiteralMean.meanField_eq_jointMeanVector
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
    hages hrootStop k h θ q hq ω
  have hT : CoveredControlledLaw.targets Zero k h=(fun i=>((carrier Zero k).observations.observations h i).target):=rfl
  have hC : CoveredControlledLaw.centers Zero k h=(fun i=>((carrier Zero k).observations.observations h i).center):=rfl
  rw [hT,hC] at he
  exact he.symm


/-- On the genuine original current window the literal active
baseline leg is the negative finite sum of the actual correlated leaf
marks. There is no extra normalization and no altered baseline. -/
theorem active_baseline_eq_neg_sum
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (k : ℕ) (h : History X k) (θ : ℝ) (q : ℝ≥0) (hvq : v≤q) (ω : Ω) :
    ControlledFamilyLegFubini.baseline P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (U ω,Dir ω) k h q (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) θ=
      -(∑ j,Leaf k θ q h j ω) := by
  have ht:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (0,(U ω,Dir ω)) (0,(0,0)) k h
  have hvq' : (v:ℝ)≤(q:ℝ):=by exact_mod_cast hvq
  unfold ControlledFamilyLegFubini.baseline
  rw [ht]
  by_cases hq : (q:ℝ)<(carrier Zero k).terminal h
  · rw [ite_eq_left ⟨hvq',hq⟩,
      mean_eq_meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h θ q hq ω]
    exact MixedPastBaselineIdentity.canonical_point_eq_neg_sum_leaf_marks
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q h ω
  · have ha : ¬((v:ℝ)≤(q:ℝ) ∧ (q:ℝ)<(carrier Zero k).terminal h):=fun hh=>hq hh.2
    simp only [ite_eq_right ha,MixedPastOmittedMarkFields.leafMark,MixedPastOmittedMarkFields.activeAverage,
      ite_eq_right hq,mul_zero,Finset.sum_const_zero,neg_zero]

end SHE.MixedPastBaselineFTCIdentity
