module

public import SHE.MixedPastTerminalPairedFields
public import SHE.ControlledTerminalPairedRelative
public import SHE.TerminalSuccessorGeometry
public import SHE.MixedPastTerminalState
public import SHE.MixedPastTerminalFirstState
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

namespace SHE.MixedPastTerminalPairedIdentity
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

/-- The two actual terminal states are EXACTLY the positive-age old
observations appended to the actual newest U or V point. No Gaussian
current-state identification is used. -/
theorem current_eq_terminal_mean
    (hrootstop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (second:Bool) (k:ℕ) (h:History X (k+1)) (q:ℝ≥0)
    (hqt:(q:ℝ)=(carrier Zero k).nodeTime h)
    (hgap:∀i,(q:ℝ)<((carrier Zero k).observations.observations h.1 i).target) (ω:Ω):
    current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm second (k+1) h ω=
    MixedPastTerminalData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (if second then 1 else 0) v q
      (fun i=>stops Zero k h.1 i-(v:ℝ)) (fun i=>targets Zero k h.1 i-(v:ℝ))
      (centers Zero k h.1) h.2.2 ω:=by
  have hs:∀x i,((Zero).observations.observations x i).stop≤(Zero).terminal x:=hrootstop
  cases second
  · convert! (MixedPastTerminalFirstState.mean_zero_eq_terminal_first_state
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Zero hs k h v q hqt hgap ω).symm using 1
  · convert! (MixedPastTerminalState.mean_one_eq_terminal_state
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Zero hs k h v q hqt hgap ω).symm using 1

/-- A single ORIGINAL history event identifies the literal random-past
terminal paired slot with the normalized conditional-moment fibre.
The newest actual rough coordinate stays outside the future law. -/
theorem point_relative_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ (k+1),
    ∀q:ℝ≥0,(q:ℝ)=(carrier Zero k).nodeTime h →
    (∀i,(q:ℝ)<((carrier Zero k).observations.observations h.1 i).target) →
    ∀choices:List (Fin (k+1)×Fin (k+2)),∀ν χ:ℝ,∀i:Fin (k+2),∀ω:Ω,
      point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm (k+1) choices ν χ i h ω=
      PairedAssignedTelescope.averageSlot P Λ (U ω) (Dir ω) 0 1 0 ((q:ℝ)-(v:ℝ))
        (Fin.cons ((q:ℝ)-(v:ℝ)) (fun j=>stops Zero k h.1 j-(v:ℝ)))
        (Fin.cons ((q:ℝ)-(v:ℝ)) (fun j=>targets Zero k h.1 j-(v:ℝ)))
        (Fin.cons h.2.2 (centers Zero k h.1))
        (fun j=>lower Zero (k+1) h j-(v:ℝ)) (fun j=>upper Zero (k+1) h j-(v:ℝ))
        (directions Zero ((carrier Zero (k+1)).observations.observations h) (k+1) h) choices
        (F (rootParameter (k+1) h)) (rootSelector (k+1) (fun j=>j)) (leafIndex (k+1) (fun j=>j))
        (MixedPastTerminalData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          1 v q (fun j=>stops Zero k h.1 j-(v:ℝ)) (fun j=>targets Zero k h.1 j-(v:ℝ))
          (centers Zero k h.1) h.2.2 ω)
        (MixedPastTerminalData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          0 v q (fun j=>stops Zero k h.1 j-(v:ℝ)) (fun j=>targets Zero k h.1 j-(v:ℝ))
          (centers Zero k h.1) h.2.2 ω) ν χ i:=by
  filter_upwards [ControlledTerminalPairedFields.relative_all_parameters_ae
    P haP Λ v b hvb Z htarget hstop F hF hFm hages ρ (k+1)] with h hh
  intro q hqt hgap choices ν χ i ω
  have he:=hh (U ω,Dir ω)
    (current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm true (k+1) h ω)
    (current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm false (k+1) h ω) choices ν χ i
  have hn:=current_eq_terminal_mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hrootstop true k h q hqt hgap ω
  have ho:=current_eq_terminal_mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hrootstop false k h q hqt hgap ω
  have hs:=TerminalSuccessorGeometry.stops_succ Zero k h
  have ht:=TerminalSuccessorGeometry.targets_succ Zero k h
  have hx:=TerminalSuccessorGeometry.centers_succ Zero k h
  have hsrel:(fun j=>stops Zero (k+1) h j-(v:ℝ))=
      Fin.cons ((q:ℝ)-(v:ℝ)) (fun j=>stops Zero k h.1 j-(v:ℝ)):=by
    rw [hs,←hqt]
    funext j
    exact Fin.cases rfl (fun _=>rfl) j
  have htrel:(fun j=>targets Zero (k+1) h j-(v:ℝ))=
      Fin.cons ((q:ℝ)-(v:ℝ)) (fun j=>targets Zero k h.1 j-(v:ℝ)):=by
    rw [ht,←hqt]
    funext j
    exact Fin.cases rfl (fun _=>rfl) j
  have hterminal:(carrier Zero (k+1)).terminal h=(q:ℝ):=hqt.symm
  dsimp only [point]
  rw [he,hn,ho,hterminal,hsrel,htrel,hx]
  rfl

end SHE.MixedPastTerminalPairedIdentity
