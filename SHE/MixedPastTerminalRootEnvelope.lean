module

public import SHE.MixedPastTerminalPairedFields
public import SHE.MixedPastLiteralRootSlot
public import SHE.TerminalConditionalGeometry
public import SHE.PairedTerminalTimeFields
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
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastTerminalRootEnvelope
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


open GaussianAssignmentBlocks OldIntervalCovariance ControlledOldIntervals
variable (k:ℕ) (h:History X (k+1)) (q:ℝ≥0)
local notation "sig" => (fun i:Fin (1+k)=>stops Zero k h.1 i-(v:ℝ))
local notation "tgt" => (fun i:Fin (1+k)=>targets Zero k h.1 i-(v:ℝ))
local notation "ctr" => centers Zero k h.1
local notation "lo" => (fun j:Fin (k+1)=>lower Zero (k+1) h j-(v:ℝ))
local notation "hi" => (fun j:Fin (k+1)=>upper Zero (k+1) h j-(v:ℝ))
local notation "sT" => (Fin.cons ((q:ℝ)-(v:ℝ)) tgt : Fin (1+(k+1))→ℝ)
local notation "sSig" => (Fin.cons ((q:ℝ)-(v:ℝ)) sig : Fin (1+(k+1))→ℝ)
local notation "g" => (rootSelector (n:=1) (k+1) (fun j:Fin (1+(k+1))=>j))
local notation "leaf" => (leafIndex (n:=1) (k+1) (fun j:Fin (1+(k+1))=>j))
local notation "at" => TerminalSuccessorGeometry.atSpace h
local notation "DD" => (fun x=>directions Zero ((carrier Zero (k+1)).observations.observations (at x)) (k+1) (at x))
local notation "MM" => (fun θ x=>MixedPastTerminalData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q sig tgt ctr x)
local notation "AA" => (fun x ω=>familyCovariance sSig sT (Fin.cons x ctr) (referenceProfile P Λ (U ω) (Dir ω)) lo hi)

include hIJ₀ hIJ₁ in
/-- The literal terminal ROOT-paired slot has a true conditional moment
with the positive old score forest extracted ONCE. Every unchanged rough
leaf and every original root clip remains in the deterministic factor. -/
theorem conditional_root
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ)
    (hvq:v<q) (hqH:q≤H) (hspan:(q:ℝ)-(v:ℝ)≤1)
    (hpkt:TerminalConditionalGeometry.Packet ((q:ℝ)-(v:ℝ)) P.horizon sig tgt lo hi leaf)
    (choices:List (Fin (k+1)×Fin (k+2))) (hnd:(choices.map Prod.fst).Nodup)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχ1:χ≤1)
    (hjet:∀j,j≤(block choices 0).length+1→∀z,
      ‖iteratedFDeriv ℝ j (F (rootParameter (k+1) h)) z‖≤A0*ν^j)
    (order:ℕ) (horder:0<order) (B0:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (K:HeatCircle→ℝ) (hK:∀x,0≤K x)
    (hframe:∀ᵐ x:HeatCircle ∂haarAddCircle,∀ω:Ω,
      (∀j,DD x j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (AA x ω j)).range) ∧
      |∏j,MeasurableGaussianScores.scoreVariance (AA x ω j) (DD x j)|≤K x)
    (hrep:∀ᵐ x:HeatCircle ∂haarAddCircle,∀ω:Ω,
      point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm (k+1) choices ν χ 0 (at x) ω=
      PairedAssignedTelescope.averageSlot P Λ (U ω) (Dir ω) 0 1 0 ((q:ℝ)-(v:ℝ))
        sSig sT (Fin.cons x ctr) lo hi (DD x) choices (F (rootParameter (k+1) h)) g leaf
        (MM 1 x ω) (MM 0 x ω) ν χ 0):
    ∀ᵐ x:HeatCircle ∂haarAddCircle,∀A:Set Ω,MeasurableSet[𝓕 v] A →
      Integrable (fun ω=>|point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm (k+1) choices ν χ 0 (at x) ω|^(2*order)) (μ.restrict A) ∧
      (∫ω in A,|point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm (k+1) choices ν χ 0 (at x) ω|^(2*order) ∂μ)≤
      NoFreshAssignedMoments.constant P (k+1) (k+1) choices order
        (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (order*((k+1)+2)) B0 κ M)^P.exponent)*
        (K x*|PairedTerminalTimeFields.factor P lo hi (fun j=>sT (leaf j)) choices χ A0 ν 0|)^(2*order)*μ.real A:=by
  let chosen:=fun j:Fin (k+1)=>MinimumGapChoice.blockChoice lo hi choices j.succ
  have hc:∀j hh,chosen j hh∈block choices j.succ:=fun j hh=>MinimumGapChoice.blockChoice_mem _ _ _ _ _
  have hh:=MixedPastLiteralRootSlot.conditional_root_slot
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    P hlocal hΛ v q hvq hqH hspan sig tgt ctr hpkt.stop_pos hpkt.stop_le_one hpkt.ages hpkt.target_after
    lo hi hpkt.lower hpkt.intervals hpkt.stops hpkt.disjoint DD g leaf hpkt.native hpkt.leaf_age
    choices hnd chosen hc (F (rootParameter (k+1) h)) ((hF.smooth _).continuous.measurable)
    hA0 hν hχ hχ1 ((hF.smooth _).of_le (by simp)) hjet order horder B0 hBDG
  filter_upwards [hh,hframe,hrep] with x hx hfx hrx
  have hD:∀ω j,DD x j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (AA x ω j)).range:=fun ω j=>(hfx ω).1 j
  let Q:=PairedTerminalTimeFields.factor P lo hi (fun j=>sT (leaf j)) choices χ A0 ν 0
  have hQ:Q=(2*VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1)*
      ∏j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (sT (leaf j)) (chosen j):=by
    unfold Q PairedTerminalTimeFields.factor MixedPastWordMoments.factor
    simp only [Fin.cases_zero]
    ring
  have hm:∀ᵐ ω ∂μ,|(∏j,MeasurableGaussianScores.scoreVariance (AA x ω j) (DD x j))*
      (2*VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1)*
      ∏j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (sT (leaf j)) (chosen j)|≤K x*|Q|:=by
    apply ae_of_all
    intro ω
    rw [mul_assoc,←hQ,abs_mul]
    exact mul_le_mul_of_nonneg_right (hfx ω).2 (abs_nonneg Q)
  have hout:=hx hD (K x*|Q|) (mul_nonneg (hK x) (abs_nonneg Q)) hm
  intro A hA
  have hs:=hout A hA
  simpa only [←hrx] using hs

end SHE.MixedPastTerminalRootEnvelope
