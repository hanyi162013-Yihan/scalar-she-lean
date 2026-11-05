module

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
namespace SHE.MixedCanonicalGradientHeatAverage
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic GaussianItoTest ControlledProfile ControlledReferenceLevel
open Filter Topology
open scoped ENNReal NNReal
local instance mixedCanonicalGradientHeatAverage_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedCanonicalGradientHeatAverage_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedCanonicalGradientHeatAverage_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedCanonicalGradientHeatAverage_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedCanonicalGradientHeatAverage_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedCanonicalGradientHeatAverage_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedCanonicalGradientHeatAverage_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedCanonicalGradientHeatAverage_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedCanonicalGradientHeatAverage_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

variable (k:ℕ)
local notation "Obs" => (fun ε:ℝ≥0=>((L (0,0) ε k).observations.observations))
local notation "Terminal" => (fun ε:ℝ≥0=>((L (0,0) ε k).terminal))
local notation "Held"=>PredictablePastParameter.held v pastParameter (0,0)

local notation "Raw" => (fun ε:ℝ≥0=>MixedCanonicalGradientKernel.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF δ hδ ε k)
local notation "Mean" => (fun ε:ℝ≥0=>MixedCanonicalGradientKernel.mean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF δ hδ ε k)

include hΛ hbH in
/-- The literal finite-k input has one integrable original-history/time
majorant independent of epsilon, including at singular terminal faces. -/
theorem uniform_integrable_bound (hb1:(b:ℝ)≤1)
    (ν:Measure (CutoffWordHistories.History Unit k))[IsFiniteMeasure ν]:
    ∃B:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)→ℝ,
      Integrable B (ν.prod (energyMeasure μ H)) ∧ ∀ε z,‖Raw ε z‖≤B z:=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨C,hC,hCb⟩:=ControlledRecursiveGradientRows.gradient_bound P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF δ hδ k
  let N:ℝ:=(n+k)*C
  have hN:0≤N:=by dsimp only [N];positivity
  let T:=fun h:CutoffWordHistories.History Unit k=>(L (0,0) 0 k).terminal h
  let cap:=fun z:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)=>
    if (z.2.1:ℝ)<T z.1 then NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ)) else 0
  let B:=fun z=>N*(1+cap z)
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hm:0≤κ+10*M:=by positivity
  have hT0(h:CutoffWordHistories.History Unit k):0≤T h:=v.2.trans ((L (0,0) 0 k).terminal_base h)
  have hTb(h:CutoffWordHistories.History Unit k):T h≤(b:ℝ):=(L (0,0) 0 k).terminal_horizon h
  have hi:Integrable cap (ν.prod (energyMeasure μ H)):=
    NativeVariableTerminalCap.integrable ν μ H T (L (0,0) 0 k).terminal_measurable hT0
      (fun h=>(hTb h).trans (by exact_mod_cast hbH)) (fun h=>(hTb h).trans hb1) hm
  refine ⟨B,((integrable_const 1).add hi).const_mul N,?_⟩
  intro ε z
  have hterm:(L (0,0) ε k).terminal z.1=T z.1:=
    ControlledReferenceRecursiveBounds.terminal_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z htarget hstop F hF δ hδ (0,0) (0,0) ε 0 k z.1
  by_cases hz:(v:ℝ)<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<(L (0,0) ε k).terminal z.1
  · have hq:(z.2.1:ℝ)<T z.1:=by have hh:=hz.2; rwa [hterm] at hh
    have hcap:=NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hq)
    have hrow(i:Fin (n+k)):
        ‖MixedNativeJointPhysicalRows.physicalRow
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S ((L (0,0) ε k).observations.observations z.1) z.2 i‖≤
            Real.sqrt (NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ))):=by
      apply (Real.le_sqrt (norm_nonneg _) hcap).mpr
      apply MixedNativePhysicalRowBound.row_bound_uniform
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S ((L (0,0) ε k).observations.observations z.1)
        hΛ z.2.1 (sub_pos.mpr hq)
      · intro i
        have hg:=(L (0,0) ε k).targets_after z.1 i
        rw [hterm] at hg
        linarith
      · intro i
        exact hz.2.le.trans ((L (0,0) ε k).stops_after z.1 i)
      · exact le_rfl
    have hn:‖Raw ε z‖≤N*Real.sqrt (NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ))):=by
      dsimp only
      rw [MixedCanonicalGradientKernel.raw,ite_eq_left hz]
      calc
        _≤∑i:Fin (n+k),‖
          (fderiv ℝ (GaussianItoTest.backward ((L (Held z.2) ε k).window z.1)
            ((L (Held z.2) ε k).test z.1) (z.2.1:ℝ)) (Mean ε z)
              (EuclideanSpace.basisFun (Fin (n+k)) ℝ i)) •
            MixedNativeJointPhysicalRows.physicalRow
              𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S ((L (0,0) ε k).observations.observations z.1) z.2 i‖:=norm_sum_le _ _
        _≤∑_:Fin (n+k),C*Real.sqrt (NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ))):=by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_smul]
          have hgrad:= (fderiv ℝ (GaussianItoTest.backward ((L (Held z.2) ε k).window z.1)
            ((L (Held z.2) ε k).test z.1) (z.2.1:ℝ)) (Mean ε z)).le_opNorm
              (EuclideanSpace.basisFun (Fin (n+k)) ℝ i)
          rw [(EuclideanSpace.basisFun (Fin (n+k)) ℝ).orthonormal.norm_eq_one,mul_one] at hgrad
          exact mul_le_mul (hgrad.trans (hCb _ _ _ _ _)) (hrow i) (norm_nonneg _) hC
        _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];dsimp only [N];push_cast;ring
    refine hn.trans ?_
    dsimp only [B,cap]
    rw [ite_eq_left hq]
    apply mul_le_mul_of_nonneg_left _ hN
    nlinarith [Real.sq_sqrt hcap,sq_nonneg (Real.sqrt (NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ)))-1)]
  · dsimp only
    rw [MixedCanonicalGradientKernel.raw,ite_eq_right hz,norm_zero]
    apply mul_nonneg hN
    dsimp only [cap]
    split_ifs with hq
    · exact add_nonneg zero_le_one (NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hq))
    · norm_num

include hsmall hΛ hbH in
/-- Original-history averaging commutes with the genuine epsilon-zero
limit of the complete predictable kernel on one current/sample event. -/
theorem average_tendsto (hb1:(b:ℝ)≤1)
    (ν:Measure (CutoffWordHistories.History Unit k))[IsFiniteMeasure ν]
    (e:ℕ→ℝ≥0)(he:Filter.Tendsto e Filter.atTop (𝓝 0)):
    ∀ᵐz∂energyMeasure μ H,Filter.Tendsto (fun m=>∫h,Raw (e m) (h,z) ∂ν)
      Filter.atTop (𝓝 (∫h,Raw 0 (h,z) ∂ν)):=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨B,hBi,hB⟩:=uniform_integrable_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hΛ hbH k hb1 ν
  have hraw(ε:ℝ≥0):Measurable (Raw ε):=by
    have hh:=MixedCanonicalGradientKernel.raw_predictable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k
    have hmap:@Measurable (CutoffWordHistories.History Unit k×(ℝ≥0×Ω))
        (CutoffWordHistories.History Unit k×(ℝ≥0×Ω)) inferInstance
        ((inferInstance:MeasurableSpace (CutoffWordHistories.History Unit k)).prod 𝓕.predictable) id:=
      measurable_fst.prodMk (measurable_snd.mono le_rfl (predictable_le_product 𝓕))
    exact hh.comp hmap
  filter_upwards [hBi.prod_left_ae] with z hz
  apply tendsto_integral_filter_of_dominated_convergence (μ:=ν) (fun h=>B (h,z))
    (Filter.Eventually.of_forall (fun m=>(hraw (e m)).comp
      (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun m=>Filter.Eventually.of_forall (fun h=>hB (e m) (h,z)))) hz
  exact Filter.Eventually.of_forall (fun h=>
    (MixedCanonicalGradientHeat.raw_continuous
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ k (h,z)).continuousAt.tendsto.comp he)

end SHE.MixedCanonicalGradientHeatAverage
