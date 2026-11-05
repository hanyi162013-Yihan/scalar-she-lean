module

public import SHE.ScalarRootPhysicalInput
public import SHE.MixedUncutPhysicalLimit
public import SHE.ScalarRootUncutOriginalNoise
public import SHE.UncutRootHilbert
public import SHE.NativeScalarFourierWeight
public import SHE.UncutRootFields
public import SHE.RootMixedOriginalNoise
public import SHE.ScalarRootFiniteExpansion
public import SHE.MixedUncutSampleExpansion
public import SHE.MixedUncutNoiseL2
public import SHE.MixedHeatNoiseL2Limit
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

namespace SHE.ScalarRootUncutPhysicalInput
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
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} (L : Level R HeatCircle 1)
local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

local notation "D" => MixedJointLevelData.state 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

theorem state_eq_value (p : HeatCircle) (b q : ℝ≥0)
    (hgap : ∀ i,(b:ℝ)<(L.observations.observations p i).target) (hqb : q≤b) (ω : Ω) :
    D p ω (q:ℝ)=MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (L.observations.observations p) b q ω :=
  MixedNativeJointHistory.evaluate_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (L.observations.observations p) b q hgap hqb ω

variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))


open RecursiveHeatBounds Filter Topology CutoffWordHistories


variable (T:ℝ)(hterm:∀x,L.terminal x=T)
variable (hstop:∀x,(L.observations.observations x 0).stop=T)
variable (htarget:∀x,(L.observations.observations x 0).target=T)
variable (hcenter:∀x,(L.observations.observations x 0).center=x)(hT:R.base<T)
variable (ν:Measure HeatCircle) [IsFiniteMeasure ν]
variable (c:ℝ≥0) (hν:ν≤(c:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle))

include hIJ₀ hIJ₁ hterm hstop htarget hcenter hT hν in
/-- After BOTH recursive cutoffs have been removed, the literal full
uncut physical noise still is a predictable L2 integral of the SAME J.
Every depth is fixed and finite; the ORIGINAL scalar root has ZERO
heat gap. No root-limit or root-noise premise remains. -/
theorem original_input (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hΛ:0≤Λ)
    (hA:R.totalVariance=(fun z=>κ+aV z)) (hh:R.horizon≤(H:ℝ))(hh1:R.horizon≤1)
    (k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>∫p,MixedUncutPhysicalGradient.raw
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k (p,z) ∂historyMeasure R ν k) ∧
      J.integral input=ᵐ[μ]
      fun ω=>∫p,MixedUncutNoiseL2.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k p ω
        ∂historyMeasure R ν k:=by
  let σ:=historyMeasure R ν k
  let W:=UncutSmoothWords.weight L k
  have hW:Integrable W σ:=UncutHistoryMass.weight_integrable L ν k
  let raw:=fun z:History HeatCircle k×Ω=>MixedUncutNoiseL2.value
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k z.1 z.2
  let cut:=fun δ:ℝ=>fun z:History HeatCircle k×Ω=>MixedUncutNoiseL2.cutoff
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ k z.1 z.2
  let field:=fun δ:ℝ=>fun ω=>∫p,cut δ (p,ω) ∂σ
  let G:=fun ω=>∫p,raw (p,ω) ∂σ
  obtain ⟨C,hC,hCb⟩:=MixedUncutNoiseL2.bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ k
  have hrm:Measurable raw:=MixedUncutNoiseL2.value_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k
  have hcm(δ:ℝ):Measurable (cut δ):=by
    by_cases hδ:0<δ
    · simpa only [cut,MixedUncutNoiseL2.cutoff,dite_eq_left hδ] using
        MixedJointIntegratedLevel.noiseVersion_measurable
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ 0 k)
    · simp only [cut,MixedUncutNoiseL2.cutoff,dite_eq_right hδ]
      exact measurable_const
  have hcb(δ:ℝ)(p:History HeatCircle k)(ω:Ω):‖cut δ (p,ω)‖≤C*W p:=by
    by_cases hδ:0<δ
    · change ‖MixedUncutNoiseL2.cutoff 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ k p ω‖≤_
      rw [MixedUncutNoiseL2.cutoff_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hδ]
      split_ifs
      · exact hCb p ω
      · exact (norm_zero).le.trans (mul_nonneg hC (UncutSmoothWords.weight_nonneg L k p))
    · simp only [cut,MixedUncutNoiseL2.cutoff,dite_eq_right hδ,norm_zero]
      exact mul_nonneg hC (UncutSmoothWords.weight_nonneg L k p)
  have hri(ω:Ω):Integrable (fun p=>raw (p,ω)) σ:=
    (hW.const_mul C).mono' (hrm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall (fun p=>hCb p ω))
  have hci(δ:ℝ)(ω:Ω):Integrable (fun p=>cut δ (p,ω)) σ:=
    (hW.const_mul C).mono' ((hcm δ).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall (fun p=>hcb δ p ω))
  have hg:MemLp G 2 μ:=by
    have hgm:Measurable G:=hrm.stronglyMeasurable.integral_prod_left'.measurable
    apply MemLp.of_bound hgm.aestronglyMeasurable (C*(∫p,W p ∂σ))
    filter_upwards with ω
    have hb:=norm_integral_le_of_norm_le (hW.const_mul C) (Eventually.of_forall (fun p=>hCb p ω))
    simpa only [integral_const_mul] using hb
  let e:ℕ→ℝ:=fun m=>1/((m:ℝ)+1)
  have hep(m:ℕ):0<e m:=by dsimp [e];positivity
  have het:Tendsto e atTop (𝓝[>] (0:ℝ)):=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall hep⟩
  have hex(m:ℕ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>∫p,MixedLevelPhysicalGradient.raw
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L (e m) (hep m) 0 k) (p,z) ∂σ) ∧
      J.integral input=ᵐ[μ] field (e m):=by
    have hx:=ScalarRootPhysicalInput.original_input
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L J hIJ₀ hIJ₁
      T hterm hstop htarget hcenter hT ν c hν hnull hJ hΛ hA hh hh1 (e m) (hep m) k
    simpa only [field,cut,MixedUncutNoiseL2.cutoff,dite_eq_left (hep m),RootHeatBounds.level_zero] using hx
  choose input hraw hinput using hex
  have hlim:Tendsto (fun m=>∫ω,‖field (e m) ω-G ω‖^2 ∂μ) atTop (𝓝 0):=by
    have ht:=(MixedUncutNoiseL2.averaged_limit
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ ν k).2.comp het
    convert! ht using 1
    funext m
    apply integral_congr_ae
    filter_upwards with ω
    have he:=integral_sub (hci (e m) ω) (hri ω)
    try simp only [Pi.sub_apply] at he
    rw [he]
  apply TerminalItoRawLimit.original_input 𝓕 μ H J input (fun m=>field (e m)) G hg hinput hlim
    (fun m z=>∫p,MixedLevelPhysicalGradient.raw
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L (e m) (hep m) 0 k) (p,z) ∂σ)
    (fun z=>∫p,MixedUncutPhysicalGradient.raw
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k (p,z) ∂σ) hraw
  simpa only [e,MixedCanonicalUncutGradientLimit.cutoffSequence] using
    MixedUncutPhysicalLimit.average_tendsto
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k hΛ hh hh1 σ hW


end SHE.ScalarRootUncutPhysicalInput
