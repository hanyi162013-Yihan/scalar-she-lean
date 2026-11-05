module

public import SHE.MixedLevelPhysicalGradient
public import SHE.MixedRootGradientContinuity
public import SHE.MixedLevelGradientBounds
public import SHE.NativeVariableTerminalCap
public import SHE.MixedCanonicalGradientKernel
public import SHE.TerminalItoRawAverage
public import SHE.RootHeatGradientContinuity
public import SHE.MixedHeatNoiseL2Limit
public import SHE.RootMixedNoiseL2Limit
public import SHE.TerminalItoClosedLimit
public import SHE.TerminalItoAverageWitness
public import SHE.MixedJointIntegratedLevel
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.MixedRootGradientLimit
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
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} {n : ℕ} (L : Level R P n)
local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (δ:ℝ)(hδ:0<δ)(k:ℕ)
local notation "Q"=>RootHeatBounds.level L δ hδ
local notation "Obs"=>(fun ε:ℝ≥0=>(Q ε k).observations.observations)
local notation "Terminal"=>(fun ε:ℝ≥0=>(Q ε k).terminal)
local notation "Mean"=>(fun ε:ℝ≥0=>MixedLevelPhysicalGradient.mean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Q ε k))
local notation "Raw"=>(fun ε:ℝ≥0=>MixedLevelPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Q ε k))

open Filter Topology
/-- A genuine original history/energy integrable cap, uniform through
root zero heat and all recursively moving observation heat ages. -/
theorem uniform_integrable_bound(hΛ:0≤Λ)(hh:R.horizon≤(H:ℝ))(hh1:R.horizon≤1)
    (ν:Measure (CutoffWordHistories.History P k))[IsFiniteMeasure ν]:
    ∃B:CutoffWordHistories.History P k×(ℝ≥0×Ω)→ℝ,
      Integrable B (ν.prod (energyMeasure μ H)) ∧ ∀ε z,‖Raw ε z‖≤B z:=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨C₀,hC₀,hB₀⟩:=(RootHeatBounds.test_uniform L δ hδ k).norm_bound
  obtain ⟨C,hC,hB₁⟩:=(RootHeatBounds.test_uniform L δ hδ k).fderiv.norm_bound
  have hg(ε:ℝ≥0)(p:CutoffWordHistories.History P k)(t:ℝ)(z:WordRecursion.State (n+k)):
      ‖fderiv ℝ (GaussianItoTest.backward ((Q ε k).window p) ((Q ε k).test p) t) z‖≤C:=
    BackwardRegularity.gaussian_state_gradient_bound _
      (((Q ε k).test_uniform.smooth p).of_le (by simp)) (hB₀ (ε,p)) (hB₁ (ε,p)) z
  let N:ℝ:=((n+k:ℕ):ℝ)*C
  have hN:0≤N:=by dsimp only [N];positivity
  let T:=Terminal 0
  let cap:=fun z:CutoffWordHistories.History P k×(ℝ≥0×Ω)=>
    if (z.2.1:ℝ)<T z.1 then NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ)) else 0
  let B:=fun z=>N*(1+cap z)
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hm:0≤κ+10*M:=by positivity
  have hT0(p:CutoffWordHistories.History P k):0≤T p:=R.base_nonneg.trans ((Q 0 k).terminal_base p)
  have hi:Integrable cap (ν.prod (energyMeasure μ H)):=
    NativeVariableTerminalCap.integrable ν μ H T (Q 0 k).terminal_measurable hT0
      (fun p=>((Q 0 k).terminal_horizon p).trans hh)
      (fun p=>((Q 0 k).terminal_horizon p).trans hh1) hm
  refine ⟨B,((integrable_const 1).add hi).const_mul N,?_⟩
  intro ε z
  have ht:(Q ε k).terminal z.1=T z.1:=RootHeatBounds.terminal_eq L δ hδ ε 0 k z.1
  by_cases hz:R.base<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<(Q ε k).terminal z.1
  · have hq:(z.2.1:ℝ)<T z.1:=by have hq:=hz.2;rwa [ht] at hq
    have hcap:=NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hq)
    have hn:=MixedLevelGradientBounds.norm_le_terminal_cap
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Q ε k) hΛ hC (hg ε) z hz
    rw [ht] at hn
    apply hn.trans
    dsimp only [B,cap,N]
    rw [ite_eq_left hq]
    apply mul_le_mul_of_nonneg_left _ hN
    nlinarith [Real.sq_sqrt hcap,sq_nonneg (Real.sqrt (NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ)))-1)]
  · dsimp only
    rw [MixedLevelPhysicalGradient.raw,ite_eq_right hz,norm_zero]
    apply mul_nonneg hN
    dsimp only [cap]
    split_ifs with hq
    · exact add_nonneg zero_le_one (NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hq))
    · norm_num

/-- The literal averaged physical input reaches zero original root
heat on one genuine original current/sample event. -/
theorem average_tendsto(hΛ:0≤Λ)(hh:R.horizon≤(H:ℝ))(hh1:R.horizon≤1)
    (ν:Measure (CutoffWordHistories.History P k))[IsFiniteMeasure ν]
    (e:ℕ→ℝ≥0)(he:Tendsto e atTop (𝓝 0)):
    ∀ᵐz∂energyMeasure μ H,Tendsto (fun m=>∫p,Raw (e m) (p,z) ∂ν)
      atTop (𝓝 (∫p,Raw 0 (p,z) ∂ν)):=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨B,hBi,hB⟩:=uniform_integrable_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ k hΛ hh hh1 ν
  have hm(ε:ℝ≥0):Measurable (Raw ε):=by
    have h:=MixedLevelPhysicalGradient.raw_predictable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Q ε k)
    have hmap:@Measurable (CutoffWordHistories.History P k×(ℝ≥0×Ω))
        (CutoffWordHistories.History P k×(ℝ≥0×Ω)) inferInstance
        ((inferInstance:MeasurableSpace (CutoffWordHistories.History P k)).prod 𝓕.predictable) id:=
      measurable_fst.prodMk (measurable_snd.mono le_rfl (predictable_le_product 𝓕))
    exact h.comp hmap
  filter_upwards [hBi.prod_left_ae] with z hz
  apply tendsto_integral_of_dominated_convergence (μ:=ν) (fun p=>B (p,z))
    (fun m=>(hm (e m)).comp (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable)
    hz (fun m=>Eventually.of_forall (fun p=>hB _ _))
  exact Eventually.of_forall (fun p=>
    (MixedRootGradientContinuity.raw_continuous
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ k (p,z)).continuousAt.tendsto.comp he)

end SHE.MixedRootGradientLimit
