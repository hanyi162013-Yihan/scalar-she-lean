module

public import SHE.MixedPastLiteralPoint
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastLiteralMean
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralMean_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralMean_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralMean_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralMean_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralMean_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralMean_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
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


local instance mixedPastLiteralMean_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralMean_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastLiteralMean_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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


/-- The entire conditional mean path used in the sharp literal kernel
is exactly the actual physical joint mean path from the carrier FTC.
No covered stop changes an original damper in the main native geometry. -/
theorem meanField_eq_jointMeanVector
    (hages : ∀ x i,(Z.observations x i).stop ≤ (Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop ≤ (b:ℝ))
    (k : ℕ) (h : History X k) (θ : ℝ) (q : ℝ≥0)
    (hq : (q:ℝ)<(carrier Zero k).terminal h) (ω : Ω) :
    MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q ω h=
    ControlledJointWeightedWord.jointMeanVector
      (fun i=>((carrier Zero k).observations.observations h i).stop)
      (targets Zero k h) (fun i=>NativeHeatSpan.unitCenter (centers Zero k h i)) q Λ
      (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) θ := by
  have hgap (i) : (q:ℝ)-(v:ℝ)<targets Zero k h i-(v:ℝ):=
    sub_lt_sub_right (carrier_targets_after Zero h hages hq i) _
  have hh:=MixedPastActualMean.mean_eq_jointMeanVector
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q
    (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h) hgap ω
  have hs (i) : stops Zero k h i=((carrier Zero k).observations.observations h i).stop:=
    min_eq_left (CarrierStopBounds.stop_le_initial Zero hrootStop k h i)
  simpa only [sub_add_cancel,hs,MixedPastLiteralPoint.meanField] using hh

/-- At theta one this is the literal actually observed recursive state. -/
theorem meanField_one_eq_state
    (hages : ∀ x i,(Z.observations x i).stop ≤ (Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop ≤ (b:ℝ))
    (k : ℕ) (h : History X k) (q : ℝ≥0)
    (hq : (q:ℝ)<(carrier Zero k).terminal h) (ω : Ω) :
    MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k 1 q ω h=
    JointWordAnalytic.state (carrier Zero k) Λ
      (MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalState
      (MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalState
      (MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField
      (MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField h ω q := by
  exact MixedPastActualMean.mean_one_eq_state 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    Zero hrootStop k h v q (carrier_targets_after Zero h hages hq) ω

end SHE.MixedPastLiteralMean
