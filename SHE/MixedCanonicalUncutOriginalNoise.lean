module

public import SHE.ScalarRootUncutOriginalNoise
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

namespace SHE.MixedCanonicalUncutOriginalNoise
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
local instance mixedCanonicalUncutOriginalNoise_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
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

/-- The literal whole canonical finite residual is the complete sum of
the uncut physical stochastic leaves, before any expectation. -/
theorem residual_eq_noise_sum (hΛ:0≤Λ) (ν:Measure HeatCircle) [IsFiniteMeasure ν]
    (depth:ℕ) (p:Inputs) (ω:Ω):
    K ν depth p ω=∑k∈Finset.range depth,N p ν k ω:=by
  have he:=MixedUncutSampleExpansion.finite_expansion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) hΛ ν depth ω
  have hmeasure(k:ℕ):historyMeasure (referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb p) ν k=
      historyMeasure (referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)) ν k:=
    HistoryMeasureGeometry.historyMeasure_eq
      (R:=referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb p)
      (Q:=referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)) rfl rfl ν k
  unfold ControlledReferenceFamilyResidual.residual ControlledReferenceFamilySections.leafSection
    ControlledReferenceFamilySections.referenceSection ControlledReferenceFamilySections.markSection
  simp_rw [←hmeasure]
  change MixedUncutSampleExpansion.leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) ν 0 ω-
    (∑k∈Finset.range depth,MixedUncutSampleExpansion.referenceMass
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) ν k ω)-
    (∑k∈Finset.range depth,MixedUncutSampleExpansion.markMass
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) ν k ω)-
    MixedUncutSampleExpansion.leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) ν depth ω=_
  linarith only [he]

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hrootStop:∀x,(Z.observations x 0).stop=(b:ℝ))
variable (hrootTarget:∀x,(Z.observations x 0).target=(b:ℝ))
variable (hcenter:∀x,(Z.observations x 0).center=x)

include hIJ₀ hIJ₁ hrootStop hrootTarget hcenter in
/-- Every fixed member of the genuine uncut canonical finite family
has a SAME-J witness supported after the original past time. -/
theorem fixed_residual_post_input (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hΛ:0≤Λ) (hbH:b≤H) (hvb':v<b)
    (ν:Measure HeatCircle) [IsFiniteMeasure ν] (c:ℝ≥0)
    (hν:ν≤(c:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle)) (depth:ℕ) (p:Inputs):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral (PastItoInputs.post 𝓕 μ H v input)=ᵐ[μ] K ν depth p:=by
  have hex(k:ℕ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral (PastItoInputs.post 𝓕 μ H v input)=ᵐ[μ] N p ν k:=by
    have hh:=ScalarRootUncutOriginalNoise.original_post_input
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) J hIJ₀ hIJ₁
      (b:ℝ) (fun _=>rfl) hrootStop hrootTarget hcenter
      (by exact_mod_cast hvb') ν c hν hnull hJ hΛ rfl (by exact_mod_cast hbH) k
    change ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral (PastItoInputs.post 𝓕 μ H v input)=ᵐ[μ] fun ω=>
        ∫h,MixedUncutNoiseL2.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (Base p) k h ω ∂historyMeasure (referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb p) ν k
    simpa only [ControlledReferenceLevel.referenceData,Real.toNNReal_coe] using hh
  choose input hi using hex
  refine ⟨∑k∈Finset.range depth,input k,?_⟩
  have hs:J.integral (PastItoInputs.post 𝓕 μ H v (∑k∈Finset.range depth,input k))=
      ∑k∈Finset.range depth,J.integral (PastItoInputs.post 𝓕 μ H v (input k)):=
    map_sum (J.integral.toLinearMap.comp (PastItoClosedRange.projection
      (C:=Both RealHaarInput) 𝓕 μ H v).toLinearMap) input (Finset.range depth)
  have ha:=Lp.coeFn_fun_finsetSum (Finset.range depth)
    (fun k=>J.integral (PastItoInputs.post 𝓕 μ H v (input k)))
  rw [←hs] at ha
  filter_upwards [ae_all_iff.mpr hi,ha] with ω hω hsum
  rw [hsum,residual_eq_noise_sum 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ ν depth p ω]
  exact Finset.sum_congr rfl (fun k _=>hω k)

include hIJ₀ hIJ₁ hrootStop hrootTarget hcenter hsmall in
/-- Actual F_v-random reference substitution is performed on the entire
finite uncut residual using finite simple past approximation and strong
Ito closed range. No fixed-reference theorem is evaluated on an
input-dependent exceptional event. The root heat gap is zero. -/
theorem random_residual_original_input (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hlocal:StandardTerminalPastLocality J)
    (hΛ:0≤Λ) (hbH:b≤H) (hvb':v<b)
    (ν:Measure HeatCircle) [IsFiniteMeasure ν] (c:ℝ≥0)
    (hν:ν≤(c:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle)) (depth:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] fun ω=>K ν depth (pastParameter ω) ω:=by
  obtain ⟨C,hC,hCb⟩:=ControlledReferenceFamilyResidual.residual_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hΛ ν depth
  exact PastParameterOriginalIto.random_input 𝓕 μ H v J hlocal (K ν depth)
    (ControlledReferenceFamilyResidual.residual_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF hFm ν depth)
    (ControlledReferenceFamilyResidual.residual_continuous
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ ν depth)
    hC hCb
    (fixed_residual_post_input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
        hnull hJ hΛ hbH hvb' ν c hν depth)
    (MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v)

end SHE.MixedCanonicalUncutOriginalNoise

