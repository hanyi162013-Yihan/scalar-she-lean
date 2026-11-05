module

public import SHE.MixedCanonicalGradientKernel
public import SHE.TerminalItoRawAverage

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
set_option quotPrecheck false
namespace SHE.MixedCanonicalGradientAverage
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic GaussianItoTest ControlledProfile ControlledReferenceLevel
open scoped ENNReal NNReal
local instance mixedCanonicalGradientAverage_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedCanonicalGradientAverage_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedCanonicalGradientAverage_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedCanonicalGradientAverage_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedCanonicalGradientAverage_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedCanonicalGradientAverage_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedCanonicalGradientAverage_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedCanonicalGradientAverage_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedCanonicalGradientAverage_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedCanonicalGradientAverage_circleSecondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
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
variable (δ : ℝ) (hδ : 0<δ)
local notation "L" => ControlledReferenceRecursiveBounds.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ

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
variable (ε:ℝ≥0)(hε:0<(ε:ℝ))(hgap:∀i,(ε:ℝ)≤(Z i).target-(b:ℝ))
variable (k:ℕ)
local notation "Obs"=>((L (0,0) ε k).observations.observations)
local notation "Terminal"=>((L (0,0) ε k).terminal)
local notation "Held"=>PredictablePastParameter.held v pastParameter (0,0)

local notation "Raw"=>MixedCanonicalGradientKernel.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF δ hδ ε k
local notation "Noise"=>fun z:CutoffWordHistories.History Unit k×Ω=>
  MixedJointPastExpectedLevel.noiseVersion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L (pastParameter z.2) ε k) z.1 z.2

include hsmall hΛ in
/-- The actual random-reference finite noise is jointly Borel over its
original history and the original sample space. -/
theorem noise_joint_measurable:Measurable Noise:=by
  let K:=fun (p:Inputs)(z:CutoffWordHistories.History Unit k×Ω)=>
    MixedJointPastExpectedLevel.noiseVersion
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) z.1 z.2
  have hc(z:CutoffWordHistories.History Unit k×Ω):Continuous (fun p=>K p z):=
    ControlledReferenceRecursiveResidualContinuity.continuous_residual
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k z.1 z.2
  have hm(p:Inputs):Measurable (K p):=
    MixedJointPastExpectedLevel.noiseVersion_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k)
  have hK:=measurable_uncurry_of_continuous_of_measurable hc hm
  have hu:Measurable pastParameter:=
    (MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).measurable.mono (𝓕.le v) le_rfl
  have hh:=hK.comp ((hu.comp measurable_snd).prodMk measurable_id)
  exact hh

include hIJ₀ hIJ₁ hnull hbH hsmall hΛ hε hgap in
/-- The exact original-history average of the literal physical gradient
kernel is the SAME original Ito input of the actual averaged finite
recursive noise. There is no hidden choice of an averaged kernel. -/
theorem original_average_input (hJ:StandardFiniteIto.Universal 𝓕 μ H J)
    (hlocal:StandardTerminalPastLocality J)
    (ν:Measure (CutoffWordHistories.History Unit k)) [IsFiniteMeasure ν]:
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>∫h,Raw (h,z) ∂ν) ∧
      J.integral input=ᵐ[μ] fun ω=>∫h,Noise (h,ω) ∂ν:=by
  obtain ⟨D,hD,hd⟩:=MixedCanonicalGradientKernel.raw_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hΛ ε hε hgap k
  obtain ⟨B,hB,hb⟩:=ControlledReferenceRecursiveResidualBounds.uniform_piece_bounds
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hΛ k
  apply TerminalItoRawAverage.bounded_average 𝓕 μ H J ν Raw
    (MixedCanonicalGradientKernel.raw_predictable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k) hD
    (fun h z=>hd (h,z)) Noise
    (noise_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k) hB
    (fun h ω=>(hb (pastParameter ω) ε h ω).2.2.2.2)
  intro h
  exact MixedCanonicalGradientKernel.original_section_input
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall J hIJ₀ hIJ₁ hnull hΛ hbH ε hε hgap k hJ hlocal h

end SHE.MixedCanonicalGradientAverage
