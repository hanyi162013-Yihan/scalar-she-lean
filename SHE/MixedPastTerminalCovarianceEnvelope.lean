module

public import SHE.MixedPastTerminalFiniteCovariance
public import SHE.MixedPastTerminalFiniteCovarianceRelative
public import SHE.MixedPastTerminalConvexCovariance
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

namespace SHE.MixedPastTerminalCovarianceEnvelope
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

local notation "Point" => MixedPastTerminalFiniteCovariance.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Reversing the two endpoints and the interpolation parameter keeps
the true future coefficient unchanged. The signed direction stays1−0. -/
theorem profile_reversal (u d:CircleL2) (ζ:ℝ):
    BoundedWindowDecomposition.convexProfile P Λ u d 1 0 (1-ζ)=
      BoundedWindowDecomposition.convexProfile P Λ u d 0 1 ζ:=by
  funext z
  unfold BoundedWindowDecomposition.convexProfile
  ring

/-- Complete native covariance input, with every original old score and
rough leaf. Reversed parameterization is exactly the actual0→1 future law. -/
def nativeInput (ζ:ℝ) (x:HeatCircle) (ω:Ω):ℝ:=
  let c:=BoundedWindowDecomposition.convexProfile P Λ (U ω) (Dir ω) 1 0 (1-ζ)
  let e:=fun z=>ControlledProfile.profile P Λ (U ω) (Dir ω) (1,z)-
    ControlledProfile.profile P Λ (U ω) (Dir ω) (0,z)
  (1/2:ℝ)*∫z,e z*BoundedCompleteGaussianWord.value P Λ (U ω) (Dir ω) c 1 ((q:ℝ)-(v:ℝ))
    sSig sT (Fin.cons x ctr) lo hi (MM 1 x ω) true (DD x)
    (StoppedGaussianFeatures.stoppedRow sSig sT (Fin.cons x ctr) z) g leaf (F (rootParameter (k+1) h))
      ∂StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))

local notation "Native" => nativeInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k h q
local notation "Mass" => (fun ζ x=>MixedPastConvexScoreMass.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v sSig sT (Fin.cons x ctr)
    ((q:ℝ)-(v:ℝ)) lo hi 1 0 (1-ζ))

include hIJ₀ hIJ₁ in
/-- Actual finite terminal covariance point has the genuine native
conditional even-moment estimate. Original geometry, old score forest,
current offset packet and finite-profile mass moments are retained.
The pointwise mass stays inside expectation for sharp spatial energy. -/
theorem conditional_input
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ)
    (hvq:v<q) (hqH:q≤H) (hspan:(q:ℝ)-(v:ℝ)≤1)
    (hpkt:TerminalConditionalGeometry.Packet ((q:ℝ)-(v:ℝ)) P.horizon sig tgt lo hi leaf)
    {ζ:ℝ} (hζ:0≤ζ) (hζ1:ζ≤1)
    {A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν)
    (hjet:∀j,j≤k+1→∀z,‖iteratedFDeriv ℝ j (F (rootParameter (k+1) h)) z‖≤A0*ν^j)
    (order:ℕ) (horder:0<order) (B0:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (K:HeatCircle→ℝ) (hK:∀x,0≤K x)
    (hframe:∀ᵐx:HeatCircle ∂haarAddCircle,∀ω:Ω,
      (∀j,DD x j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (AA x ω j)).range) ∧
      |∏j,MeasurableGaussianScores.scoreVariance (AA x ω j) (DD x j)|≤K x)
    (hrep:∀ᵐx:HeatCircle ∂haarAddCircle,∀ω:Ω,Point (k+1) 1 0 1 ζ (at x) ω=Native ζ x ω):
    ∀ᵐx:HeatCircle ∂haarAddCircle,
      Integrable (fun ω=>|Point (k+1) 1 0 1 ζ (at x) ω|^(2*order)) μ ∧
      (∫ω,|Point (k+1) 1 0 1 ζ (at x) ω|^(2*order) ∂μ)≤
        MixedPastWordMoments.momentConstant P (k+1) (k+1) order
          (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (order*((k+1)+2)) B0 κ M)^P.exponent)*
        (K x*MixedPastWordMoments.total (d:=1) P lo hi (fun j=>sT (leaf j)) A0 ν/2)^(2*order)*
          (∫ω,(Mass ζ x ω)^(2*order) ∂μ):=by
  have hm:=MixedPastTerminalConvexCovariance.input_moment (r:=k+1)
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ 1 P hlocal hΛ (by norm_num)
    v q hvq hqH hspan sig tgt ctr hpkt.stop_pos hpkt.stop_le_one hpkt.ages hpkt.target_after
    leaf hpkt.native hpkt.leaf_age order horder B0 hBDG 1 0
      (ζ:=1-ζ) (by linarith) (by linarith)
  filter_upwards [hm,hframe,hrep] with x hx hf hr
  have hs (j:Fin (k+1)) (i:Fin (1+k+1)):sSig i≤lo j ∨ hi j≤sSig i :=
    Fin.cases (Or.inl (hpkt.lower j)) (fun l=>hpkt.stops j l) i
  have hh:=hx lo hi hpkt.lower hpkt.intervals hs hpkt.disjoint (DD x)
    (fun ω j=>(hf ω).1 j) g (F (rootParameter (k+1) h)) (hF.smooth _).continuous.measurable
    A0 ν hA0 hν ((hF.smooth _).of_le (by simp)) hjet (K x) (hK x) (fun ω=>(hf ω).2)
  simp_rw [hr]
  exact hh

end SHE.MixedPastTerminalCovarianceEnvelope
