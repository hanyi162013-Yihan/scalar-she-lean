module

public import SHE.ControlledFiniteCovarianceMassRelative
public import SHE.MixedPastTerminalCovarianceFields
public import SHE.MixedPastTerminalCovarianceEnvelope
public import SHE.MixedPastTerminalFiniteCovariance
public import SHE.MixedPastTerminalPairedIdentity
public import SHE.MixedPastTerminalPairedFields
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

namespace SHE.MixedPastTerminalCovarianceMassNative
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

local notation "Cur" => MixedPastTerminalPairedFields.current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mark" => ControlledFiniteCovarianceFields.point P haP Λ v b hvb Z htarget hstop F hF hFm

local notation "Mean" => MixedPastTerminalFiniteCovariance.terminalMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Point" => MixedPastTerminalFiniteCovariance.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "Mass"=>MixedPastTerminalCovarianceFields.mass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- The genuine physical changing-history mass equals EXACTLY the native
conditional input mass, with signed1−0 direction and actual convex law.
This common event allows random past substitution before any moment. -/
theorem mass_native_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ (k+1),
      ∀q:ℝ≥0,(v:ℝ)≤(q:ℝ) → (q:ℝ)=(carrier Zero k).nodeTime h → ∀ζ:ℝ,∀ω:Ω,
      Mass (k+1) ζ h ω=MixedPastConvexScoreMass.value
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v
        (Fin.cons ((q:ℝ)-(v:ℝ)) (fun j=>stops Zero k h.1 j-(v:ℝ)))
        (Fin.cons ((q:ℝ)-(v:ℝ)) (fun j=>targets Zero k h.1 j-(v:ℝ)))
        (Fin.cons h.2.2 (centers Zero k h.1)) ((q:ℝ)-(v:ℝ))
        (fun j=>lower Zero (k+1) h j-(v:ℝ)) (fun j=>upper Zero (k+1) h j-(v:ℝ))
        1 0 (1-ζ) ω:=by
  filter_upwards [ControlledFiniteCovarianceMassRelative.mass_relative_ae
    P haP Λ v b hvb Z htarget hstop F hF hFm hages ρ (k+1)] with h hh
  intro q hvq hqt ζ ω
  have hterminal:(carrier Zero (k+1)).terminal h=(q:ℝ):=hqt.symm
  have hsrel:(fun j=>stops Zero (k+1) h j-(v:ℝ))=
      Fin.cons ((q:ℝ)-(v:ℝ)) (fun j=>stops Zero k h.1 j-(v:ℝ)):=by
    rw [TerminalSuccessorGeometry.stops_succ,←hqt]
    funext j
    exact Fin.cases rfl (fun _=>rfl) j
  have htrel:(fun j=>targets Zero (k+1) h j-(v:ℝ))=
      Fin.cons ((q:ℝ)-(v:ℝ)) (fun j=>targets Zero k h.1 j-(v:ℝ)):=by
    rw [TerminalSuccessorGeometry.targets_succ,←hqt]
    funext j
    exact Fin.cases rfl (fun _=>rfl) j
  have hx:=TerminalSuccessorGeometry.centers_succ Zero k h
  have he:=hh (1,(U ω,Dir ω)) (q:ℝ) hvq (by rw [hterminal]) 0 1 ζ
  dsimp only at he
  change ControlledFiniteCovarianceMass.mass P haP Λ v b hvb Z htarget hstop F hF hFm
    (1,(U ω,Dir ω)) (k+1) h ((carrier Zero (k+1)).terminal h) 0 1 ζ=_
  rw [hterminal]
  simpa only [MixedPastConvexScoreMass.value,StoppedRandomScoreMass.mass,
    BoundedThetaRelativeSecondScore.covariance,MixedPastTerminalCovarianceEnvelope.profile_reversal,
    hsrel,htrel,hx] using he

end SHE.MixedPastTerminalCovarianceMassNative
