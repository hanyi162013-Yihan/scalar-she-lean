module

public import SHE.MixedCanonicalPhysicalGradient
public import SHE.NativeWeightedTerminalCap
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

namespace SHE.MixedCanonicalPhysicalSections
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

variable(k:ℕ)
local notation "Raw"=>(fun p:Inputs=>MixedUncutPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k)
local notation "R₀"=>ControlledReferenceLevel.referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)
local notation "W"=>UncutSmoothWords.weight (Base (0,0)) k

/-- A single genuine original-history/current-energy L1 envelope
controls the literal native uncut raw gradient for ALL past inputs. -/
theorem uniform_integrable_bound(hΛ:0≤Λ)(hbH:b≤H)(hb1:(b:ℝ)≤1)
    (ν:Measure HeatCircle)[IsFiniteMeasure ν]:
    let σ:=historyMeasure R₀ ν k
    ∃B:History HeatCircle k×(ℝ≥0×Ω)→ℝ,
      Integrable B (σ.prod (energyMeasure μ H)) ∧ ∀p z,‖Raw p z‖≤B z:=by
  intro σ
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  have hWi:Integrable W σ:=UncutHistoryMass.weight_integrable (Base (0,0)) ν k
  have hJ:=ControlledReferenceFamilyBounds.normalized_uniform
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm k
  obtain ⟨C₀,hC₀,hB₀⟩:=hJ.norm_bound
  obtain ⟨C,hC,hB₁⟩:=hJ.fderiv.norm_bound
  have hg(p:Inputs)(h:History HeatCircle k)(t:ℝ)(y:WordRecursion.State (1+k)):
      ‖fderiv ℝ (GaussianItoTest.backward ((NL p k).window h) ((NL p k).test h) t) y‖≤C:=
    BackwardRegularity.gaussian_state_gradient_bound _
      (((NL p k).test_uniform.smooth h).of_le (by simp)) (hB₀ (p,h)) (hB₁ (p,h)) y
  let N:ℝ:=((1+k:ℕ):ℝ)*C
  have hN:0≤N:=by dsimp only [N];positivity
  let T:History HeatCircle k→ℝ:=(NL (0,0) k).terminal
  let cap:=fun z:History HeatCircle k×(ℝ≥0×Ω)=>
    if (z.2.1:ℝ)<T z.1 then NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ)) else 0
  let B:=fun z=>N*(W z.1+W z.1*cap z)
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hm:0≤κ+10*M:=by positivity
  have hi:Integrable (fun z:History HeatCircle k×(ℝ≥0×Ω)=>W z.1*cap z) (σ.prod (energyMeasure μ H)):=
    NativeWeightedTerminalCap.integrable σ μ H T (NL (0,0) k).terminal_measurable
      (fun h=>v.2.trans ((NL (0,0) k).terminal_base h))
      (fun h=>((NL (0,0) k).terminal_horizon h).trans (by exact_mod_cast hbH))
      (fun h=>((NL (0,0) k).terminal_horizon h).trans hb1) hm
      W (UncutSmoothWords.weight_measurable _ _) (UncutSmoothWords.weight_nonneg _ _) hWi
  refine ⟨B,((hWi.comp_fst (energyMeasure μ H)).add hi).const_mul N,?_⟩
  intro p z
  have ht:(NL p k).terminal z.1=T z.1:=
    ControlledReferenceFamilyBounds.carrier_terminal_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z htarget hstop F hF hFm p (0,0) k z.1
  have hw:UncutSmoothWords.weight (Base p) k z.1=W z.1:=
    ControlledReferenceFamilyBounds.weight_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z htarget hstop F hF hFm p (0,0) k z.1
  have hw0:0≤W z.1:=UncutSmoothWords.weight_nonneg _ _ _
  have hbase:(referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb p).base=(v:ℝ):=rfl
  by_cases hz:(v:ℝ)<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<T z.1
  · have hzp:(referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb p).base<(z.2.1:ℝ) ∧
        (z.2.1:ℝ)<(NL p k).terminal z.1:=by rwa [hbase,ht]
    have hn:=MixedLevelGradientBounds.norm_le_terminal_cap
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL p k) hΛ hC (hg p) z hzp
    rw [ht] at hn
    have hcap:=NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hz.2)
    have hs:Real.sqrt (NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ)))≤
        1+NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ)):=by
      nlinarith [Real.sq_sqrt hcap,sq_nonneg (Real.sqrt (NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ)))-1)]
    change ‖UncutSmoothWords.weight (Base p) k z.1 •
      MixedLevelPhysicalGradient.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL p k) z‖ ≤ B z
    rw [norm_smul,hw,Real.norm_eq_abs,abs_of_nonneg hw0]
    apply (mul_le_mul_of_nonneg_left hn hw0).trans
    dsimp only [B,cap,N]
    rw [ite_eq_left hz.2]
    nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hw0 hN)]
  · have hB:0≤B z:=by
      dsimp only [B,cap]
      apply mul_nonneg hN
      apply add_nonneg hw0
      apply mul_nonneg hw0
      split_ifs with hq
      · exact NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hq)
      · norm_num
    simpa only [MixedUncutPhysicalGradient.raw,MixedLevelPhysicalGradient.raw,hbase,ht,ite_eq_right hz,smul_zero,norm_zero] using hB

include hsmall in
/-- One original energy event supports continuous past-parameter
substitution AFTER the full singular old-history integration. -/
theorem average_parameter_continuous(hΛ:0≤Λ)(hbH:b≤H)(hb1:(b:ℝ)≤1)
    (ν:Measure HeatCircle)[IsFiniteMeasure ν]:
    ∀ᵐz∂energyMeasure μ H,Continuous (fun p:Inputs=>∫h,Raw p (h,z) ∂historyMeasure R₀ ν k):=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  let σ:=historyMeasure R₀ ν k
  obtain ⟨B,hBi,hB⟩:=uniform_integrable_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm k hΛ hbH hb1 ν
  have hm(p:Inputs):Measurable (Raw p):=by
    have hh:=MixedUncutPhysicalGradient.raw_predictable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k
    have hmap:@Measurable (History HeatCircle k×(ℝ≥0×Ω)) (History HeatCircle k×(ℝ≥0×Ω)) inferInstance
        ((inferInstance:MeasurableSpace (History HeatCircle k)).prod 𝓕.predictable) id:=
      measurable_fst.prodMk (measurable_snd.mono le_rfl (predictable_le_product 𝓕))
    exact hh.comp hmap
  filter_upwards [hBi.prod_left_ae] with z hz
  rw [continuous_iff_continuousAt]
  intro p
  exact tendsto_integral_filter_of_dominated_convergence (μ:=σ) (fun h=>B (h,z))
    (Eventually.of_forall (fun p'=>(hm p').comp (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable))
    (Eventually.of_forall (fun p'=>Eventually.of_forall (fun h=>hB p' (h,z)))) hz
    (Eventually.of_forall (fun h=>(MixedCanonicalPhysicalGradient.raw_parameter_continuous
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall k hΛ (h,z)).continuousAt.tendsto))

end SHE.MixedCanonicalPhysicalSections
