module

public import SHE.MixedCanonicalUncutGradientKernel
public import SHE.ControlledNormalizedNoiseBounds
public import SHE.ControlledReferenceCutoffBounds
public import SHE.NativeWeightedTerminalCap
public import SHE.CutoffUncutComparison
public import SHE.MixedNoiseTestScaling
public import SHE.MixedCanonicalGradientHeat
public import SHE.NativeVariableTerminalCap
public import SHE.MixedCanonicalGradientAverage
public import SHE.TerminalItoRawLimit
public import SHE.WeightedHistoryL2Limit
public import SHE.RecursiveHeatGradientContinuity
public import SHE.NativeRowTargetContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option quotPrecheck false
namespace SHE.MixedCanonicalUncutGradientLimit
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic GaussianItoTest ControlledProfile ControlledReferenceLevel
open Filter Topology
open scoped ENNReal NNReal
local instance mixedCanonicalUncutGradientKernel_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedCanonicalUncutGradientKernel_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedCanonicalUncutGradientKernel_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedCanonicalUncutGradientKernel_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedCanonicalUncutGradientKernel_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedCanonicalUncutGradientKernel_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedCanonicalUncutGradientKernel_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedCanonicalUncutGradientKernel_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedCanonicalUncutGradientKernel_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

open ControlledProfile ControlledReferenceLevel
variable (P : CanonicalCovariance.ProfileParameters) (hAs : SmoothCylinders.BoundedSmooth (fun z => κ+aV z))
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : SmoothCylinders.BoundedSmooth F)
local notation "Base" => ControlledReferenceLevel.level P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF
local notation "L" => (fun δ:ℝ=>fun hδ:0<δ=>ControlledReferenceRecursiveBounds.level P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ)

local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (hΛ:0≤Λ) (hbH:b≤H)

variable (k:ℕ)
local notation "Held"=>PredictablePastParameter.held v pastParameter (0,0)

local notation "Carrier" => (fun p:Inputs=>CutoffCarriers.carrier (Base p) k)
local notation "NL" => (fun p:Inputs=>UncutWordEvaluation.normalizedLevel (Base p) k)
local notation "Obs" => (Carrier (0,0)).observations.observations
local notation "Terminal" => (Carrier (0,0)).terminal
local notation "Mean"=>MixedCanonicalGradientKernel.mean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF 1 zero_lt_one 0 k
local notation "Cut" => (fun δ:ℝ=>fun hδ:0<δ=>MixedCanonicalGradientKernel.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF δ hδ 0 k)
local notation "W" => UncutSmoothWords.weight (Base (0,0)) k

local notation "Raw"=>MixedCanonicalUncutGradientKernel.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF k
local notation "Noise"=>MixedCanonicalUncutGradientKernel.noise
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF k
local notation "CutNoise"=>(fun δ:ℝ=>fun hδ:0<δ=>fun z:CutoffWordHistories.History Unit k×Ω=>
  MixedJointPastExpectedLevel.noiseVersion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (L δ hδ (pastParameter z.2) 0 k) z.1 z.2)

def cutoffSequence (m:ℕ):ℝ:=1/((m:ℝ)+1)
theorem cutoffSequence_pos(m:ℕ):0<cutoffSequence m:=by unfold cutoffSequence;positivity
theorem cutoffSequence_tendsto:Tendsto cutoffSequence atTop (𝓝[>] (0:ℝ)):=by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ),Eventually.of_forall cutoffSequence_pos⟩

include hsmall hΛ in
/-- Genuine history × predictable measurability of the full uncut
kernel, obtained from exact cutoff identities on every history. -/
theorem raw_predictable:
    @Measurable (CutoffWordHistories.History Unit k×(ℝ≥0×Ω)) (Both RealHaarInput)
      ((inferInstance:MeasurableSpace (CutoffWordHistories.History Unit k)).prod 𝓕.predictable)
      inferInstance Raw:=by
  letI:MeasurableSpace (CutoffWordHistories.History Unit k×(ℝ≥0×Ω)):=
    (inferInstance:MeasurableSpace (CutoffWordHistories.History Unit k)).prod 𝓕.predictable
  apply measurable_of_tendsto_metrizable
    (f:=fun m=>Cut (cutoffSequence m) (cutoffSequence_pos m))
    (fun m=>MixedCanonicalGradientKernel.raw_predictable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF (cutoffSequence m) (cutoffSequence_pos m) hsmall hΛ 0 k)
  rw [tendsto_pi_nhds]
  intro z
  obtain ⟨η,hη,heq⟩:=MixedCanonicalUncutGradientKernel.raw_eventually_eq
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF k z
  apply tendsto_const_nhds.congr'
  filter_upwards [cutoffSequence_tendsto.eventually ((eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds)] with m hm
  exact (heq _ (cutoffSequence_pos m) hm).symm

include hsmall hΛ in
theorem noise_measurable:Measurable Noise:=by
  apply measurable_of_tendsto_metrizable
    (f:=fun m=>CutNoise (cutoffSequence m) (cutoffSequence_pos m))
    (fun m=>MixedCanonicalGradientAverage.noise_joint_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF (cutoffSequence m) (cutoffSequence_pos m) hsmall hΛ 0 k)
  rw [tendsto_pi_nhds]
  intro z
  obtain ⟨η,hη,heq⟩:=MixedCanonicalUncutGradientKernel.noise_eventually_eq
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF k z
  apply tendsto_const_nhds.congr'
  filter_upwards [cutoffSequence_tendsto.eventually ((eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds)] with m hm
  exact (heq _ (cutoffSequence_pos m) hm).symm

end SHE.MixedCanonicalUncutGradientLimit
