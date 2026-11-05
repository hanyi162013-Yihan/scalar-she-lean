module

public import SHE.MixedPastOmittedMarkFields
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

namespace SHE.MixedPastBaselineIdentity
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastBaselineIdentity_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastBaselineIdentity_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastBaselineIdentity_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastBaselineIdentity_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastBaselineIdentity_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastBaselineIdentity_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastBaselineIdentity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastBaselineIdentity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastBaselineIdentity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

omit [IsProbabilityMeasure μ] in
/-- Literal pointwise baseline-mark identity, before every averaging.
The negative sign is the baseline FTC sign, and the normalization is
already included in each actual omitted average exactly once. -/
theorem point_eq_neg_sum_leaf_marks (k : ℕ) (θ : ℝ) (q : ℝ≥0) (h : History X k) (ω : Ω) :
    ActualBaselineMarkFields.point (Base (θ,(U ω,Dir ω))) (oldProfile P Λ v (U ω,Dir ω))
      k q (fun j=>Input k θ h j ω) (Mean k θ q ω h) h=
      -(∑ j,Leaf k θ q h j ω) := by
  have ht:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (θ,(U ω,Dir ω)) (0,(0,0)) k h
  unfold ActualBaselineMarkFields.point MixedPastOmittedMarkFields.leafMark
    MixedPastOmittedMarkFields.activeAverage
  rw [ht]
  by_cases hq : (q:ℝ)<(carrier Zero k).terminal h
  · simp only [ite_eq_left hq]
    unfold baselineMark MixedPastLiteralOmitted.average
    rfl
  · simp only [ite_eq_right hq,mul_zero,Finset.sum_const_zero,neg_zero]

omit [IsProbabilityMeasure μ] in
/-- Every actual canonical baseline derivative is the original native
leaf derivative used in the quantitative omitted-word estimate. This
uses input-independent original lower times, without changing the full
profile or the erased leaf age. -/
theorem baseline_derivative_eq_leaf_input (k : ℕ) (θ : ℝ) (h : History X k) (j : Fin k) (ω : Ω) :
    ControlledFiniteWord.baselineDerivatives P Λ (U ω) (Dir ω) (LP (U ω,Dir ω) k h) j θ=
      Input k θ h j ω := by
  unfold ControlledFiniteWord.baselineDerivatives ControlledFamilyThreeLeg.leafPoint ControlledFamilyThreeLeg.lo
    MixedPastOmittedMarkFields.leafInput
  rw [ControlledThetaPhysicalGeometry.lower_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
    (0,(U ω,Dir ω)) (0,(0,0)) k h]

omit [IsProbabilityMeasure μ] in
/-- The actual canonical full-baseline point equals the finite sum of
literal leaf marks, with every original leaf multiplier restored. -/
theorem canonical_point_eq_neg_sum_leaf_marks (k : ℕ) (θ : ℝ) (q : ℝ≥0) (h : History X k) (ω : Ω) :
    ActualBaselineMarkFields.point (Base (θ,(U ω,Dir ω))) (oldProfile P Λ v (U ω,Dir ω)) k q
      (fun j=>ControlledFiniteWord.baselineDerivatives P Λ (U ω) (Dir ω) (LP (U ω,Dir ω) k h) j θ)
      (Mean k θ q ω h) h=-(∑ j,Leaf k θ q h j ω) := by
  have hd : (fun j=>ControlledFiniteWord.baselineDerivatives P Λ (U ω) (Dir ω)
      (LP (U ω,Dir ω) k h) j θ)=(fun j=>Input k θ h j ω):=
    funext (fun j=>baseline_derivative_eq_leaf_input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k θ h j ω)
  rw [hd]
  exact point_eq_neg_sum_leaf_marks 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q h ω

end SHE.MixedPastBaselineIdentity
