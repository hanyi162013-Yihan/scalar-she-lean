module

public import SHE.ScalarRootUncutPhysicalInput
public import SHE.PastParameterRawLimit
public import SHE.ParameterSmoothContinuity
public import SHE.ControlledReferenceFamilyResidual
public import SHE.PastParameterOriginalIto
public import SHE.PastItoLimitWitness
public import SHE.HistoryMeasureGeometry
public import SHE.RootSectionAverage
public import SHE.NativeBesselFiniteIdentity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedCanonicalPhysicalGradient
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
local instance mixedCanonicalRootFields_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
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
local notation "NL"=>(fun p k=>UncutWordEvaluation.normalizedLevel (Base p) k)

include hsmall S in
/-- Actual full-reserve uncut gradients depend continuously on the
past states, including zero root gap and singular collision covariance. -/
theorem normalized_gradient_continuous(hΛ:0≤Λ)(k:ℕ)(h:History HeatCircle k)(t:ℝ):
    Continuous (fun q:Inputs×WordRecursion.State (1+k)=>
      fderiv ℝ (GaussianItoTest.backward ((NL q.1 k).window h) ((NL q.1 k).test h) t) q.2):=by
  have hFs:=CutoffWordLevel.uniform_reindex
    (ControlledReferenceFamilyBounds.normalized_uniform P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z htarget hstop F hF hFm k) (fun p:Inputs=>(p,h))
  have hFn:=ControlledReferenceFamilyContinuity.normalized_continuous
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k h
  have hA:=ControlledReferenceFamilyBackward.window_path_continuous
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k h t
  obtain ⟨C,hC,hCb⟩:=hFs.norm_bound
  have hc:=GaussianParameterContinuity.continuous_average
    (fun p:Inputs=>(NL p k).test h) hFn hCb
    (fun p:Inputs=>((NL p k).window h).path t) hA
  have hs:=hFs.average
    (fun p:Inputs=>ProbabilityTheory.multivariateGaussian 0 (((NL p k).window h).path t).val)
    (fun _=>inferInstance)
  obtain ⟨B,hB,hBb⟩:=hs.fderiv.fderiv.norm_bound
  exact ParameterSmoothContinuity.continuous_fderiv _ hc
    (fun p=>(hs.smooth p).of_le (by simp)) hB hBb

variable(k:ℕ)
local notation "Raw"=>(fun p:Inputs=>MixedUncutPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k)

include hsmall in
/-- Every literal native uncut physical input is continuous in the
actual past reference parameters, BEFORE the original history average. -/
theorem raw_parameter_continuous(hΛ:0≤Λ)(z:History HeatCircle k×(ℝ≥0×Ω)):
    Continuous (fun p:Inputs=>Raw p z):=by
  have ho(p:Inputs):(NL p k).observations.observations z.1=(NL (0,0) k).observations.observations z.1:=
    ControlledReferenceFamilyBounds.carrier_observations_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z htarget hstop F hF hFm p (0,0) k z.1
  have ht(p:Inputs):(NL p k).terminal z.1=(NL (0,0) k).terminal z.1:=
    ControlledReferenceFamilyBounds.carrier_terminal_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z htarget hstop F hF hFm p (0,0) k z.1
  have hw(p:Inputs):UncutSmoothWords.weight (Base p) k z.1=UncutSmoothWords.weight (Base (0,0)) k z.1:=
    ControlledReferenceFamilyBounds.weight_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z htarget hstop F hF hFm p (0,0) k z.1
  let y:=MixedLevelPhysicalGradient.mean
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL (0,0) k) z
  have hy(p:Inputs):MixedLevelPhysicalGradient.mean
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL p k) z=y:=by
    unfold MixedLevelPhysicalGradient.mean
    rw [ho]
    rfl
  have hbase(p:Inputs):(referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb p).base=(v:ℝ):=rfl
  by_cases hz:(v:ℝ)<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<(NL (0,0) k).terminal z.1
  · have hg:=(normalized_gradient_continuous
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k z.1 (z.2.1:ℝ)).comp
        (continuous_id.prodMk (continuous_const (y:=y)))
    have hs:=continuous_finsetSum Finset.univ (fun i:Fin (1+k)=>fun _=>
      (hg.clm_apply (continuous_const (y:=EuclideanSpace.basisFun (Fin (1+k)) ℝ i))).smul
        (continuous_const (y:=MixedNativeJointPhysicalRows.physicalRow
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          ((NL (0,0) k).observations.observations z.1) z.2 i)))
    convert hs.const_smul (UncutSmoothWords.weight (Base (0,0)) k z.1) using 1
    funext p
    simp only [MixedUncutPhysicalGradient.raw,MixedLevelPhysicalGradient.raw,ht,ho,hw,hy,hbase]
    rw [if_pos hz]
    rfl
  · have he:(fun p:Inputs=>Raw p z)=fun _=>0:=by
      funext p
      simp only [MixedUncutPhysicalGradient.raw,MixedLevelPhysicalGradient.raw,ht,hbase,if_neg hz,smul_zero]
    rw [he]
    exact continuous_const

end SHE.MixedCanonicalPhysicalGradient
