module

public import SHE.MixedLevelOriginalAverage
public import SHE.MixedUncutPhysicalGradient
public import SHE.MixedCanonicalUncutGradientLimit
public import SHE.MixedUncutNoiseL2
public import SHE.MixedLevelGradientBounds
public import SHE.NativeWeightedTerminalCap
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

namespace SHE.MixedUncutPhysicalLimit
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
variable {Ω P : Type} [MeasurableSpace Ω] [MeasurableSpace P]
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

open Classical CutoffWordHistories CutoffCarriers
variable (k:ℕ)
local notation "NL"=>UncutWordEvaluation.normalizedLevel L k
local notation "W"=>UncutSmoothWords.weight L k
local notation "Cut"=>(fun δ:ℝ=>fun hδ:0<δ=>MixedLevelPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (RecursiveHeatBounds.level L δ hδ 0 k))

open Filter Topology
local notation "Raw"=>MixedUncutPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k
local notation "d"=>MixedCanonicalUncutGradientLimit.cutoffSequence
local notation "dp"=>MixedCanonicalUncutGradientLimit.cutoffSequence_pos
local notation "dt"=>MixedCanonicalUncutGradientLimit.cutoffSequence_tendsto

/-- The true uncut history weight times the singular terminal cap is
integrable before averaging. Both root gap0 and delta0 are allowed. -/
theorem uniform_integrable_bound(hΛ:0≤Λ)(hh:R.horizon≤(H:ℝ))(hh1:R.horizon≤1)
    (ν:Measure (History P k))[IsFiniteMeasure ν](hWi:Integrable W ν):
    ∃B:History P k×(ℝ≥0×Ω)→ℝ,Integrable B (ν.prod (energyMeasure μ H)) ∧
      (∀z,‖Raw z‖≤B z) ∧ ∀δ hδ z,‖Cut δ hδ z‖≤B z:=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨C,hC,hCb⟩:=MixedLevelGradientBounds.gradient_bound NL
  let N:ℝ:=((n+k:ℕ):ℝ)*C
  have hN:0≤N:=by dsimp only [N];positivity
  let T:=(NL).terminal
  let cap:=fun z:History P k×(ℝ≥0×Ω)=>
    if (z.2.1:ℝ)<T z.1 then NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ)) else 0
  let B:=fun z=>N*(W z.1+W z.1*cap z)
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hm:0≤κ+10*M:=by positivity
  have hi:Integrable (fun z:History P k×(ℝ≥0×Ω)=>W z.1*cap z) (ν.prod (energyMeasure μ H)):=
    NativeWeightedTerminalCap.integrable ν μ H T (NL).terminal_measurable
      (fun p=>R.base_nonneg.trans ((NL).terminal_base p))
      (fun p=>((NL).terminal_horizon p).trans hh) (fun p=>((NL).terminal_horizon p).trans hh1) hm
      W (UncutSmoothWords.weight_measurable L k) (UncutSmoothWords.weight_nonneg L k) hWi
  have hb(z:History P k×(ℝ≥0×Ω)):‖Raw z‖≤B z:=by
    have hw:0≤W z.1:=UncutSmoothWords.weight_nonneg L k z.1
    by_cases hz:R.base<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<T z.1
    · have hn:=MixedLevelGradientBounds.norm_le_terminal_cap
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S NL hΛ hC hCb z hz
      have hcap:=NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hz.2)
      have hs:Real.sqrt (NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ)))≤
          1+NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ)):=by
        nlinarith [Real.sq_sqrt hcap,sq_nonneg (Real.sqrt (NativeObservationCaps.cap (κ+10*M) (T z.1-(z.2.1:ℝ)))-1)]
      rw [MixedUncutPhysicalGradient.raw,norm_smul,Real.norm_eq_abs,abs_of_nonneg hw]
      apply (mul_le_mul_of_nonneg_left hn hw).trans
      dsimp only [B,cap,N]
      rw [ite_eq_left hz.2]
      nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hw hN)]
    · have hB:0≤B z:=by
        dsimp only [B,cap]
        apply mul_nonneg hN
        apply add_nonneg hw
        apply mul_nonneg hw
        split_ifs with hq
        · exact NativeObservationCaps.cap_nonneg hm (sub_pos.mpr hq)
        · norm_num
      have hz':¬(R.base<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<(NL).terminal z.1):=hz
      simpa only [MixedUncutPhysicalGradient.raw,MixedLevelPhysicalGradient.raw,ite_eq_right hz',smul_zero,norm_zero] using hB
  refine ⟨B,((hWi.comp_fst (energyMeasure μ H)).add hi).const_mul N,hb,?_⟩
  intro δ hδ z
  rw [MixedUncutPhysicalGradient.cutoff_eq
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k δ hδ z]
  split_ifs
  · exact hb z
  · exact (norm_zero).le.trans ((norm_nonneg (Raw z)).trans (hb z))

theorem average_tendsto(hΛ:0≤Λ)(hh:R.horizon≤(H:ℝ))(hh1:R.horizon≤1)
    (ν:Measure (History P k))[IsFiniteMeasure ν](hWi:Integrable W ν):
    ∀ᵐz∂energyMeasure μ H,Tendsto (fun m=>∫p,Cut (d m) (dp m) (p,z) ∂ν)
      atTop (𝓝 (∫p,Raw (p,z) ∂ν)):=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  obtain ⟨B,hBi,hG,hB⟩:=uniform_integrable_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k hΛ hh hh1 ν hWi
  have hm(m:ℕ):Measurable (Cut (d m) (dp m)):=by
    have h:=MixedLevelPhysicalGradient.raw_predictable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (RecursiveHeatBounds.level L (d m) (dp m) 0 k)
    have hmap:@Measurable (History P k×(ℝ≥0×Ω)) (History P k×(ℝ≥0×Ω)) inferInstance
        ((inferInstance:MeasurableSpace (History P k)).prod 𝓕.predictable) id:=
      measurable_fst.prodMk (measurable_snd.mono le_rfl (predictable_le_product 𝓕))
    exact h.comp hmap
  filter_upwards [hBi.prod_left_ae] with z hz
  apply tendsto_integral_of_dominated_convergence (μ:=ν) (fun p=>B (p,z))
    (fun m=>(hm m).comp (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable)
    hz (fun m=>Eventually.of_forall (fun p=>hB _ _ _))
  exact Eventually.of_forall (fun p=>by
    obtain ⟨η,hη,heq⟩:=MixedUncutPhysicalGradient.eventually_eq
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k (p,z)
    apply tendsto_const_nhds.congr'
    filter_upwards [(dt).eventually ((eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds)] with m hm
    exact (heq _ (dp m) hm).symm)

end SHE.MixedUncutPhysicalLimit
