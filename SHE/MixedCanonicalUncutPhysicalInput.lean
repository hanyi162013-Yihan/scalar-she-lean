module

public import SHE.ScalarRootUncutPhysicalInput
public import SHE.MixedCanonicalPhysicalSections
public import SHE.PastParameterRawLimit
public import SHE.MixedCanonicalUncutOriginalNoise
public import SHE.ControlledReferenceFamilyResidual
public import SHE.PastParameterOriginalIto
public import SHE.PastItoLimitWitness
public import SHE.HistoryMeasureGeometry

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedCanonicalUncutPhysicalInput
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open GaussianItoTest
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedCanonicalUncutPhysicalInput_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

open ControlledProfile ControlledReferenceLevel
variable (P : CanonicalCovariance.ProfileParameters) (hAs : SmoothCylinders.BoundedSmooth (fun z => κ+aV z))
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformSmooth.UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : HeatCircle×WordRecursion.State 1 => F q.1 q.2))


local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

open Filter Topology
local notation "Base" => ControlledReferenceFamilyLevel.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm

open CutoffWordHistories
local notation "LS" => ControlledReferenceFamilySections.leafSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "RS" => ControlledReferenceFamilySections.referenceSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "MS" => ControlledReferenceFamilySections.markSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm

local notation "K" => ControlledReferenceFamilyResidual.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "N" => (fun p:Inputs=>MixedUncutSampleExpansion.noiseMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p))

local notation "R₀"=>referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)
local notation "Raw"=>(fun k p=>MixedUncutPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k)

theorem residual_difference (hΛ:0≤Λ)(ν:Measure HeatCircle)[IsFiniteMeasure ν]
    (k:ℕ)(p:Inputs)(ω:Ω):
    K ν (k+1) p ω-K ν k p ω=
      ∫h,MixedUncutNoiseL2.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (Base p) k h ω ∂historyMeasure R₀ ν k:=by
  have hs:=MixedCanonicalUncutOriginalNoise.residual_eq_noise_sum
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ ν (k+1) p ω
  have hk:=MixedCanonicalUncutOriginalNoise.residual_eq_noise_sum
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ ν k p ω
  have hm:historyMeasure (referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb p) ν k=historyMeasure R₀ ν k:=
    HistoryMeasureGeometry.historyMeasure_eq (R:=referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb p)
      (Q:=R₀) rfl rfl ν k
  rw [Finset.sum_range_succ] at hs
  rw [hs,hk]
  simp only [add_sub_cancel_left,MixedUncutSampleExpansion.noiseMass,hm]

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hrootStop:∀x,(Z.observations x 0).stop=(b:ℝ))
variable (hrootTarget:∀x,(Z.observations x 0).target=(b:ℝ))
variable (hcenter:∀x,(Z.observations x 0).center=x)

include hsmall hIJ₀ hIJ₁ hrootStop hrootTarget hcenter in
/-- The actual F_v-random canonical reference has the literal uncut
physical gradient as its SAME-J input. The initial root heat gap is
zero, and both recursive cutoffs have been removed at each fixed depth. -/
theorem original_input (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hlocal:StandardTerminalPastLocality J)
    (hΛ:0≤Λ)(hbH:b≤H)(hb1:(b:ℝ)≤1)(hvb':v<b)
    (ν:Measure HeatCircle)[IsFiniteMeasure ν](c:ℝ≥0)
    (hν:ν≤(c:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle))(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H]
        (fun z=>∫h,Raw k (pastParameter z.2) (h,z) ∂historyMeasure R₀ ν k) ∧
      J.integral input=ᵐ[μ] fun ω=>
        ∫h,MixedUncutNoiseL2.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (Base (pastParameter ω)) k h ω ∂historyMeasure R₀ ν k:=by
  let g:=fun p:Inputs=>fun z:ℝ≥0×Ω=>∫h,Raw k p (h,z) ∂historyMeasure R₀ ν k
  let out:=fun p:Inputs=>fun ω=>K ν (k+1) p ω-K ν k p ω
  have hc:∀ᵐz∂energyMeasure μ H,Continuous (fun p=>g p z):=
    MixedCanonicalPhysicalSections.average_parameter_continuous
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall k hΛ hbH hb1 ν
  have hz(p:Inputs)(z:ℝ≥0×Ω)(hq:z.1≤v):g p z=0:=by
    apply integral_eq_zero_of_ae
    filter_upwards with h
    have hn:¬((referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb p).base<(z.1:ℝ) ∧
      (z.1:ℝ)<(UncutWordEvaluation.normalizedLevel (Base p) k).terminal h):=by
      intro ht
      have hle:(z.1:ℝ)≤(v:ℝ):=by exact_mod_cast hq
      exact (not_lt_of_ge hle) ht.1
    simp only [MixedUncutPhysicalGradient.raw,MixedLevelPhysicalGradient.raw,ite_eq_right hn,smul_zero,Pi.zero_apply]
  have hm(d:ℕ)(p:Inputs):Measurable (K ν d p):=
    ControlledReferenceFamilyResidual.residual_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm ν d p
  have hco(d:ℕ)(ω:Ω):Continuous (fun p:Inputs=>K ν d p ω):=
    ControlledReferenceFamilyResidual.residual_continuous
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ ν d ω
  obtain ⟨C₁,hC₁,hB₁⟩:=ControlledReferenceFamilyResidual.residual_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ ν (k+1)
  obtain ⟨C₀,hC₀,hB₀⟩:=ControlledReferenceFamilyResidual.residual_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ ν k
  have hbound(p:Inputs)(ω:Ω):‖out p ω‖≤C₁+C₀:=
    (norm_sub_le _ _).trans (add_le_add (hB₁ p ω) (hB₀ p ω))
  have hrep(p:Inputs):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] g p ∧ J.integral input=ᵐ[μ] out p:=by
    have hh:=ScalarRootUncutPhysicalInput.original_input
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) J hIJ₀ hIJ₁
      (b:ℝ) (fun _=>rfl) hrootStop hrootTarget hcenter
      (by exact_mod_cast hvb') ν c hν hnull hJ hΛ rfl (by exact_mod_cast hbH) hb1 k
    have hmeasure:historyMeasure (referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb p) ν k=historyMeasure R₀ ν k:=
      HistoryMeasureGeometry.historyMeasure_eq (R:=referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb p)
        (Q:=R₀) rfl rfl ν k
    obtain ⟨input,hi,hout⟩:=hh
    refine ⟨input,?_,?_⟩
    · simpa only [g,hmeasure] using hi
    · filter_upwards [hout] with ω hω
      change J.integral input ω=K ν (k+1) p ω-K ν k p ω
      rw [residual_difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF hFm hΛ ν k p ω]
      simpa only [hmeasure] using hω
  obtain ⟨input,hi,hout⟩:=PastParameterRawLimit.original_input 𝓕 μ H v J hlocal g hc hz out
    (fun p=>(hm (k+1) p).sub (hm k p)) (fun ω=>(hco (k+1) ω).sub (hco k ω))
    (add_nonneg hC₁ hC₀) hbound hrep
    (MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v)
  refine ⟨input,hi,?_⟩
  filter_upwards [hout] with ω hω
  exact hω.trans (residual_difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ ν k (pastParameter ω) ω)

end SHE.MixedCanonicalUncutPhysicalInput
