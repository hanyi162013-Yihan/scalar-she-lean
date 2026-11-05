module

public import SHE.MixedPastMeanAverage
public import SHE.MixedPastBaselineFTCIdentity
public import SHE.ActualMeanKernelCongruence
public import SHE.NativeKernelCongruence

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option quotPrecheck false

namespace SHE.CanonicalPastMeanInput
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance canonicalPastMeanInput_realSigma : MeasurableSpace RealL2 := borel _
local instance canonicalPastMeanInput_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance canonicalPastMeanInput_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance canonicalPastMeanInput_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance canonicalPastMeanInput_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance canonicalPastMeanInput_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance canonicalPastMeanInput_circleSigma : MeasurableSpace CircleL2 := borel _
local instance canonicalPastMeanInput_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance canonicalPastMeanInput_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open NativeRandomKernel NormalizedKernelSplit QuarterSpatialEvent
local notation "Ref" => (fun a : ℝ×Inputs=>referenceData P P.coefficient haP Λ a.1 v b hvb a.2)


/-- The canonical FTC Gaussian mean in the literal native Hilbert
mean input, with the actual random past and current difference. -/
def canonicalInput (k : ℕ) (θ : ℝ) (q : ℝ≥0) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (t : Fin k→ℝ) (ω : Ω) : CircleL2 :=
  familyMeanInput Ref Base (fun _ : Unit=>(θ,(U ω,Dir ω))) k mass ρ hmass hρ
    (fun _=>Λ) (fun _=>(q:ℝ))
    (fun _ h=>ControlledFamilyActualTransfer.mean P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (U ω,Dir ω) k h q (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) θ)
    (fun _=>t) (fun _=>S.second q ω-S.first q ω) ()

/-- The canonical FTC input and the exact full-future conditional-law
input used in the quantitative theorem coincide. Equality of means is
needed only on the genuine active Gaussian window. -/
theorem canonicalInput_eq
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (k : ℕ) (θ : ℝ) (q : ℝ≥0) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (t : Fin k→ℝ) (ω : Ω) :
    canonicalInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q mass ρ hmass hρ t ω=
    MixedPastMeanInputEnergy.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q mass ρ hmass hρ t ω := by
  let a : ℝ×Inputs:=(θ,(U ω,Dir ω))
  let m : History HeatCircle k→WordRecursion.State (1+k):=fun h=>
    ControlledFamilyActualTransfer.mean P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (U ω,Dir ω) k h q (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) θ
  have hm (h : History HeatCircle k) (hq : (q:ℝ)<(carrier (Base a) k).terminal h) : m h=Mean k θ q ω h := by
    have ht:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
      Z htarget hstop F hF hFm a (0,(0,0)) k h
    rw [ht] at hq
    exact MixedPastBaselineFTCIdentity.mean_eq_meanField
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h θ q hq ω
  let G:=familyWeightedField Ref Base (fun _ : Unit=>a) k (fun _=>Λ) (fun _=>(q:ℝ)) (fun _=>(q:ℝ))
    (fun _=>m) (fun _=>t)
  have hop : integralOperator G ()=
      integralOperator (MixedPastKernelFields.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q q t) ω := by
    apply NativeKernelCongruence.operator_congr
    intro y x
    exact weightedSpatial_mean_congr (Base a) k Λ q q m (Mean k θ q ω) hm t y x
  unfold canonicalInput familyMeanInput MixedPastMeanInputEnergy.input
  change OneInputOperator.besselHalf mass ρ hmass hρ (integralOperator G () (embed (S.second q ω-S.first q ω)))=_
  rw [hop]

theorem old_average_eq
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (k : ℕ) (θ : ℝ) (q : ℝ≥0) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (ν : Measure (Fin k→ℝ)) (ω : Ω) :
    (∫ t,canonicalInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q mass ρ hmass hρ t ω ∂ν)=
    MixedPastMeanFields.average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k ν θ q mass ρ hmass hρ ω := by
  apply integral_congr_ae
  filter_upwards [] with t
  exact canonicalInput_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k θ q mass ρ hmass hρ t ω

end SHE.CanonicalPastMeanInput

