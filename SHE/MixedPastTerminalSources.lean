module

public import SHE.MixedPastTerminalPairedFields
public import SHE.JointCurrentDifference
public import SHE.ControlledThetaRelativeWord
public import SHE.ControlledThetaRelativeDerivative
public import SHE.ControlledTerminalPairedFields
public import SHE.JointHistoryFields
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

namespace SHE.MixedPastTerminalSources
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralPoint_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralPoint_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralPoint_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralPoint_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralPoint_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralPoint_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastLiteralPoint_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralPoint_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastLiteralPoint_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

local notation "DataU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "DataV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S


open MixedPastTerminalPairedFields
local notation "Cur"=>current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "UU"=>Function.uncurry S.first
local notation "VV"=>Function.uncurry S.second

def source (k:ℕ) (choices:List (Fin k×Fin (k+1))) (ν χ:ℝ) (i:Fin (k+1))
    (h:History X k) (ω:Ω):ℝ:=
  PairedAssignedTelescope.sources P choices (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i))
    (Cur true k h ω) (Cur false k h ω)
    (baseline (Base (1,(U ω,Dir ω))) k h) (baseline (Base (0,(U ω,Dir ω))) k h) ν χ i

theorem current_true_native (k:ℕ) (h:History X k) (ω:Ω):
    Cur true k h ω=JointCurrentDifference.state Λ UU VV
      ((carrier Zero k).observations.observations h) ((carrier Zero k).terminal h) ω:=rfl

theorem current_false_native (k:ℕ) (h:History X k) (ω:Ω):
    Cur false k h ω=JointCurrentDifference.state Λ UU UU
      ((carrier Zero k).observations.observations h) ((carrier Zero k).terminal h) ω:=rfl

/-- The actual extracted root source is a clipped TRUE current
Hilbert input, retaining original stop damping and original target age. -/
theorem root_source_le (hΛ:0≤Λ) (k:ℕ) (h:History X k) (ω:Ω)
    (choices:List (Fin k×Fin (k+1))) {ν χ:ℝ} (hν:0≤ν) (hχ:0≤χ):
    source 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
      k choices ν χ 0 h ω≤
      ν^χ*|NativeCurrentSourceEnergy.value
        (fun ω=>S.first (((carrier Zero k).terminal h).toNNReal) ω)
        (fun ω=>S.second (((carrier Zero k).terminal h).toNNReal) ω)
        (targets Zero k h (rootSelector k (fun i=>i) 0)-(carrier Zero k).terminal h)
        (ω,centers Zero k h (rootSelector k (fun i=>i) 0))|^χ:=by
  unfold source
  simp only [PairedAssignedTelescope.sources,Fin.cases_zero]
  rw [current_true_native,current_false_native]
  exact JointCurrentDifference.root_source_le Λ hΛ UU VV _ _ ω _ hν hχ ((carrier Zero k).stops_after h _)

theorem baseline_relative (p:Inputs) (η:ℝ) (k:ℕ) (h:History X k) (j:Fin k):
    baseline (Base (η,p)) k h j=
      profile P Λ p.1 p.2 (η,(targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ),
        centers Zero k h (leafIndex k (fun i=>i) j))):=by
  have hh:=ControlledThetaRelativeWord.baseline_relative P haP Λ v b hvb Z htarget hstop F hF hFm (η,p) k h j
  rw [ControlledThetaRelativeDerivative.targets_eq P haP Λ v b hvb Z htarget hstop F hF hFm
    (η,p) (0,(0,0)) k h,ControlledThetaRelativeDerivative.centers_eq P haP Λ v b hvb Z htarget hstop F hF hFm
    (η,p) (0,(0,0)) k h] at hh
  exact hh

/-- The whole own-baseline rough source splits into the TRUE current
input and a PAST profile difference. Its complementary rough-block age
remains in the normalized-slot amplitude. -/
theorem rough_source_le (hΛ:0≤Λ) (k:ℕ) (h:History X k) (ω:Ω)
    (choices:List (Fin k×Fin (k+1))) {ν χ:ℝ} (hχ:0≤χ) (j:Fin k):
    source 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
      k choices ν χ j.succ h ω≤
      max 1 (P.holder^(χ/P.exponent))*|NativeCurrentSourceEnergy.value
        (fun ω=>S.first (((carrier Zero k).terminal h).toNNReal) ω)
        (fun ω=>S.second (((carrier Zero k).terminal h).toNNReal) ω)
        (targets Zero k h (leafIndex k (fun i=>i) j)-(carrier Zero k).terminal h)
        (ω,centers Zero k h (leafIndex k (fun i=>i) j))|^χ+
      |profile P Λ (U ω) (Dir ω) (1,(targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ),
          centers Zero k h (leafIndex k (fun i=>i) j)))-
        profile P Λ (U ω) (Dir ω) (0,(targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ),
          centers Zero k h (leafIndex k (fun i=>i) j)))|^(χ/P.exponent):=by
  unfold source
  simp only [PairedAssignedTelescope.sources,Fin.cases_succ]
  rw [current_true_native,current_false_native]
  have hh:=JointCurrentDifference.rough_source_le P Λ hΛ UU VV
    ((carrier Zero k).observations.observations h) ((carrier Zero k).terminal h) ω
    choices j.succ (leafIndex k (fun i=>i) j) hχ ((carrier Zero k).stops_after h _)
    (baseline (Base (1,(U ω,Dir ω))) k h j) (baseline (Base (0,(U ω,Dir ω))) k h j)
  rw [baseline_relative,baseline_relative] at hh ⊢
  convert! hh using 1

end SHE.MixedPastTerminalSources
