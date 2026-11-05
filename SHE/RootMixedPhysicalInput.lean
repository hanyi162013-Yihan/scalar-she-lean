module

public import SHE.MixedLevelPhysicalAverage
public import SHE.MixedRootGradientLimit
public import SHE.TerminalItoRawLimit
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

namespace SHE.RootMixedPhysicalInput
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

local notation "D" => MixedJointLevelData.state 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

theorem state_eq_value (p : P) (b q : ℝ≥0)
    (hgap : ∀ i,(b:ℝ)<(L.observations.observations p i).target) (hqb : q≤b) (ω : Ω) :
    D p ω (q:ℝ)=MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (L.observations.observations p) b q ω :=
  MixedNativeJointHistory.evaluate_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (L.observations.observations p) b q hgap hqb ω

variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))


open RootHeatBounds Filter Topology CutoffWordHistories

include hIJ₀ hIJ₁ in
/-- With the original scalar root heat gap allowed to be ZERO, the
actual full finite recursive noise remains the SAME original J integral.
The needed root limit is analytic and proved for the actual scalar root;
no root noise/gap theorem is added as an external stochastic input. -/
theorem original_input (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hΛ:0≤Λ)
    (hA:R.totalVariance=(fun z=>κ+aV z)) (hh:R.horizon≤(H:ℝ))
    (hh1:R.horizon≤1)(δ:ℝ) (hδ:0<δ) (ν:Measure P) [IsFiniteMeasure ν]
    (hstart:∀p,R.base<L.terminal p)
    (hroot:RootMixedZeroHeatExpectation.RootConverges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S L δ hδ ν)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>∫p,MixedLevelPhysicalGradient.raw
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ 0 k) (p,z) ∂historyMeasure R ν k) ∧
      J.integral input=ᵐ[μ] fun ω=>∫p,MixedJointIntegratedLevel.noiseVersion
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ 0 k) p ω
          ∂historyMeasure R ν k:=by
  let σ:=historyMeasure R ν k
  let raw:=fun ε:ℝ≥0=>MixedLevelPhysicalGradient.raw
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k)
  let noise:=fun ε:ℝ≥0=>fun z:History P k×Ω=>MixedJointIntegratedLevel.noiseVersion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k) z.1 z.2
  let field:=fun ε:ℝ≥0=>fun ω=>∫p,noise ε (p,ω) ∂σ
  have hnm(ε:ℝ≥0):Measurable (noise ε):=MixedJointIntegratedLevel.noiseVersion_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k)
  have hfm(ε:ℝ≥0):Measurable (field ε):=(hnm ε).stronglyMeasurable.integral_prod_left'.measurable
  have hni(ε:ℝ≥0)(ω:Ω):Integrable (fun p=>noise ε (p,ω)) σ:=by
    obtain ⟨B,_,hB⟩:=MixedJointIntegratedLevel.uniform_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k) hΛ
    exact (integrable_const B).mono' ((hnm ε).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall (fun p=>(hB p ω).2.2.2.2))
  obtain ⟨B,_,hB⟩:=MixedJointIntegratedLevel.uniform_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ 0 k) hΛ
  have hg:MemLp (field 0) 2 μ:=MemLp.of_bound (hfm 0).aestronglyMeasurable _
    (Eventually.of_forall (fun ω=>norm_integral_le_of_norm_le_const
      (μ:=σ) (Eventually.of_forall (fun p=>(hB p ω).2.2.2.2))))
  let e:ℕ→ℝ≥0:=fun m=>(1/((m:ℝ)+1)).toNNReal
  have heq(m:ℕ):(e m:ℝ)=1/((m:ℝ)+1):=Real.coe_toNNReal _ (by positivity)
  have hep(m:ℕ):0<(e m:ℝ):=by rw [heq];positivity
  have het:Tendsto (fun m=>(e m:ℝ)) atTop (𝓝[>] (0:ℝ)):=by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall hep⟩
    simpa only [heq] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hetNN:Tendsto e atTop (𝓝 0):=by
    have ht:=continuous_real_toNNReal.continuousAt.tendsto.comp (het.mono_right nhdsWithin_le_nhds)
    simpa only [Function.comp_def,Real.toNNReal_coe,Real.toNNReal_zero] using ht
  have hex(m:ℕ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>∫p,raw (e m) (p,z) ∂σ) ∧
      J.integral input=ᵐ[μ] field (e m):=by
    have hgr:=RootHeatBounds.level_gap L δ hδ (e m) k
    exact MixedLevelPhysicalAverage.original_input
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ (e m) k) J hIJ₀ hIJ₁
      hnull hJ hΛ hA hh (hep m) hgr σ
  choose input hraw hinput using hex
  have hlim:Tendsto (fun m=>∫ω,‖field (e m) ω-field 0 ω‖^2 ∂μ) atTop (𝓝 0):=by
    have ht:=(RootMixedNoiseL2Limit.noise_limit
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ hΛ ν hstart hroot k).2.comp het
    convert! ht using 1
    funext m
    apply integral_congr_ae
    filter_upwards with ω
    have hi:=integral_sub (hni (e m) ω) (hni 0 ω)
    try simp only [Pi.sub_apply] at hi
    simp only [Real.toNNReal_coe]
    rw [hi]
  exact TerminalItoRawLimit.original_input 𝓕 μ H J input (fun m=>field (e m)) (field 0) hg hinput hlim
    (fun m z=>∫p,raw (e m) (p,z) ∂σ) (fun z=>∫p,raw 0 (p,z) ∂σ) hraw
    (MixedRootGradientLimit.average_tendsto
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ k hΛ hh hh1 σ e hetNN)


end SHE.RootMixedPhysicalInput
