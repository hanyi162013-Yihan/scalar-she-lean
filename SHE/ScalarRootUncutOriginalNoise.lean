module

public import SHE.MixedZeroHeatOriginalNoise
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

namespace SHE.ScalarRootUncutOriginalNoise
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

include hterm hstop htarget hcenter hν in
/-- Bounded Fourier root densities inherit the actual zero-gap heat limit
from the original Haar root; this is measure domination, not a new
regularity premise. -/
theorem root_converges (δ:ℝ)(hδ:0<δ):
    RootMixedZeroHeatExpectation.RootConverges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ ν:=by
  let f:=fun ε:ℝ=>fun q:History HeatCircle 0×Ω=>
    |RootJointHeatLeafLimit.leaf L δ hδ dU dV Λ ε.toNNReal 0 q.1 q.2-
      RootJointHeatLeafLimit.leaf L δ hδ dU dV Λ 0 0 q.1 q.2|
  let σ:Measure (History HeatCircle 0×Ω):=AddCircle.haarAddCircle.prod μ
  have ht:=ScalarRootFiniteExpansion.root_converges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S L T hterm hstop htarget hcenter δ hδ
  change Tendsto (fun ε=>∫q,f ε q ∂σ) (𝓝[>] (0:ℝ)) (𝓝 0) at ht
  obtain ⟨B,hB,hBb⟩:=(RootHeatBounds.test_uniform L δ hδ 0).norm_bound
  have hi(ε:ℝ):Integrable (f ε) σ:=by
    have hm:=((RootJointHeatLeafLimit.leaf_measurable L δ hδ dU dV Λ ε.toNNReal 0).sub
      (RootJointHeatLeafLimit.leaf_measurable L δ hδ dU dV Λ 0 0)).norm
    apply (integrable_const (2*B)).mono' hm.aestronglyMeasurable
    filter_upwards with q
    change ‖|_|‖≤_
    rw [Real.norm_eq_abs,abs_abs]
    exact (abs_sub _ _).trans (by
      have h1:|RootJointHeatLeafLimit.leaf L δ hδ dU dV Λ ε.toNNReal 0 q.1 q.2|≤B:=hBb (ε.toNNReal,q.1) _
      have h0:|RootJointHeatLeafLimit.leaf L δ hδ dU dV Λ 0 0 q.1 q.2|≤B:=hBb ((0:ℝ≥0),q.1) _
      linarith)
  have hprod:ν.prod μ≤(c:ℝ≥0∞) • σ:=by
    simpa only [Measure.prod_smul_left,σ] using Measure.prod_mono hν (le_refl μ)
  unfold RootMixedZeroHeatExpectation.RootConverges
  change Tendsto (fun ε=>∫q,f ε q ∂ν.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0)
  apply squeeze_zero (fun ε=>integral_nonneg (fun q=>abs_nonneg _))
    (fun ε=>?_ ) (by simpa using ht.const_mul (c:ℝ))
  have hh:=integral_mono_measure hprod (Eventually.of_forall (fun q=>abs_nonneg _))
    ((hi ε).smul_measure (by finiteness : (c:ℝ≥0∞)≠∞))
  rw [integral_smul_measure,ENNReal.coe_toReal,smul_eq_mul] at hh
  convert! hh using 1

include hIJ₀ hIJ₁ hterm hstop htarget hcenter hT hν in
/-- After BOTH recursive cutoffs have been removed, the literal full
uncut physical noise still is a predictable L2 integral of the SAME J.
Every depth is fixed and finite; the ORIGINAL scalar root has ZERO
heat gap. No root-limit or root-noise premise remains. -/
theorem original_input (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hΛ:0≤Λ)
    (hA:R.totalVariance=(fun z=>κ+aV z)) (hh:R.horizon≤(H:ℝ))
    (k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ]
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
  have hex(m:ℕ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ] field (e m):=by
    have hr:=root_converges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S L T hterm hstop htarget hcenter ν c hν (e m) (hep m)
    have hx:=RootMixedOriginalNoise.original_input
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L J hIJ₀ hIJ₁
      hnull hJ hΛ hA hh (e m) (hep m) ν (fun x=>by rw [hterm x];exact hT) hr k
    simpa only [field,cut,MixedUncutNoiseL2.cutoff,dite_eq_left (hep m),RootHeatBounds.level_zero] using hx
  choose input hinput using hex
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
  exact TerminalItoClosedLimit.original_input 𝓕 μ H J input (fun m=>field (e m)) G hg hinput hlim

include hIJ₀ hIJ₁ hterm hstop htarget hcenter hT hν in
/-- Post-v support remains after BOTH recursive cutoffs have been removed, the literal full
uncut physical noise still is a predictable L2 integral of the SAME J.
Every depth is fixed and finite; the ORIGINAL scalar root has ZERO
heat gap. No root-limit or root-noise premise remains. -/
theorem original_post_input (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hΛ:0≤Λ)
    (hA:R.totalVariance=(fun z=>κ+aV z)) (hh:R.horizon≤(H:ℝ))
    (k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral (PastItoInputs.post 𝓕 μ H R.base.toNNReal input)=ᵐ[μ]
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
  have hex(m:ℕ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral (PastItoInputs.post 𝓕 μ H R.base.toNNReal input)=ᵐ[μ] field (e m):=by
    have hr:=root_converges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S L T hterm hstop htarget hcenter ν c hν (e m) (hep m)
    have hx:=RootMixedOriginalNoise.original_post_input
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L J hIJ₀ hIJ₁
      hnull hJ hΛ hA hh (e m) (hep m) ν (fun x=>by rw [hterm x];exact hT) hr k
    simpa only [field,cut,MixedUncutNoiseL2.cutoff,dite_eq_left (hep m),RootHeatBounds.level_zero] using hx
  choose input hinput using hex
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
  exact PastItoLimitWitness.original_post_limit 𝓕 μ H R.base.toNNReal J input (fun m=>field (e m)) G hg hinput hlim

include hIJ₀ hIJ₁ hterm hstop htarget hcenter hT hν in
/-- The actual scalar root, with ZERO initial heat gap and BOTH recursive
cutoffs removed, has a finite stochastic telescope on the SAME original
J. Every full mixed-coefficient mark and terminal leaf remains. -/
theorem finite_expansion (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hΛ:0≤Λ)
    (hA:R.totalVariance=(fun z=>κ+aV z)) (hh:R.horizon≤(H:ℝ))
:
    ∃input:ℕ→Process (E:=Both RealHaarInput) 𝓕 μ H,
      (∀k,J.integral (input k)=ᵐ[μ]
        MixedUncutSampleExpansion.noiseMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν k) ∧
      ∀depth,∀ᵐω∂μ,
        MixedUncutSampleExpansion.leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν 0 ω=
          (∑k∈Finset.range depth,MixedUncutSampleExpansion.referenceMass
            𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν k ω)+
          J.integral (∑k∈Finset.range depth,input k) ω+
          (∑k∈Finset.range depth,MixedUncutSampleExpansion.markMass
            𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν k ω)+
          MixedUncutSampleExpansion.leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν depth ω:=by
  have hex(k:ℕ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ]
      MixedUncutSampleExpansion.noiseMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν k:=
    original_input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L J hIJ₀ hIJ₁
      T hterm hstop htarget hcenter hT ν c hν hnull hJ hΛ hA hh k
  choose input hi using hex
  refine ⟨input,hi,fun depth=>?_⟩
  have hs:J.integral (∑k∈Finset.range depth,input k)=∑k∈Finset.range depth,J.integral (input k):=by
    exact map_sum J.integral (fun k=>input k) (Finset.range depth)
  have ha:=Lp.coeFn_fun_finsetSum (Finset.range depth) (fun k=>J.integral (input k))
  rw [←hs] at ha
  filter_upwards [ae_all_iff.mpr hi,ha] with ω hω hsum
  have hsum':J.integral (∑k∈Finset.range depth,input k) ω=
      ∑k∈Finset.range depth,MixedUncutSampleExpansion.noiseMass
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L ν k ω:=by
    rw [hsum]
    exact Finset.sum_congr rfl (fun k _=>hω k)
  rw [hsum']
  exact MixedUncutSampleExpansion.finite_expansion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ ν depth ω


include hIJ₀ hIJ₁ hterm hstop htarget hcenter hT in
/-- The genuine zero-gap uncut noise tested against a nonnegative bounded
root density is an integral of the same original J. -/
theorem original_input_density (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hΛ:0≤Λ)
    (hA:R.totalVariance=(fun z=>κ+aV z))(hh:R.horizon≤(H:ℝ))
    (g:HeatCircle→ℝ)(hg:Measurable g)(B:ℝ≥0)
    (hg0:∀x,0≤g x)(hgB:∀x,g x≤B)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ]
      fun ω=>∫x:HeatCircle,g x*UncutRootFields.field
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L 2 k (ω,x) ∂AddCircle.haarAddCircle:=by
  let η:Measure HeatCircle:=AddCircle.haarAddCircle.withDensity (fun x=>ENNReal.ofReal (g x))
  have hη:η≤(B:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle):=by
    calc
      _≤AddCircle.haarAddCircle.withDensity (fun _ : HeatCircle=>(B:ℝ≥0∞)):=
        withDensity_mono (ae_of_all _ (fun x=>by
          simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hgB x)))
      _=_:=withDensity_const _
  haveI:IsFiniteMeasure ((B:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle)):=
    (AddCircle.haarAddCircle:Measure HeatCircle).smul_finite ENNReal.coe_ne_top
  haveI:IsFiniteMeasure η:=isFiniteMeasure_of_le ((B:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle)) hη
  obtain ⟨input,hi⟩:=original_input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S L J hIJ₀ hIJ₁ T hterm hstop htarget hcenter hT η B hη hnull hJ hΛ hA hh k
  refine ⟨input,hi.trans ?_⟩
  filter_upwards with ω
  obtain ⟨C,hC,hCb⟩:=MixedUncutNoiseL2.bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ k
  have hrm:=MixedUncutNoiseL2.value_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k
  let F:=fun z:Ω×History HeatCircle k=>MixedUncutNoiseL2.value
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k z.2 z.1
  have hiF:Integrable (fun p=>F (ω,p)) (historyMeasure R η k):=
    ((UncutHistoryMass.weight_integrable L η k).const_mul C).mono'
      (hrm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_of_all _ (fun p=>hCb p ω))
  rw [RootSectionAverage.integral_history R η k F ω hiF]
  rw [show η=AddCircle.haarAddCircle.withDensity (fun x=>ENNReal.ofReal (g x)) from rfl,
    integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
      (ae_of_all _ (fun _=>ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  simp only [ENNReal.toReal_ofReal (hg0 x),smul_eq_mul]
  rfl

include hIJ₀ hIJ₁ hterm hstop htarget hcenter hT in
/-- All bounded real Fourier tests of the actual uncut scalar root noise
retain the original stochastic integral after both cutoff limits. -/
theorem original_input_weighted (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hΛ:0≤Λ)
    (hA:R.totalVariance=(fun z=>κ+aV z))(hh:R.horizon≤(H:ℝ))
    (g:HeatCircle→ℝ)(hg:Measurable g)(B:ℝ≥0)(hgB:∀x,‖g x‖≤B)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ]
      fun ω=>∫x:HeatCircle,g x*UncutRootFields.field
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L 2 k (ω,x) ∂AddCircle.haarAddCircle:=by
  let gp:=fun x:HeatCircle=>max (g x) 0
  let gn:=fun x:HeatCircle=>max (-g x) 0
  have hgp:Measurable gp:=hg.max measurable_const
  have hgn:Measurable gn:=hg.neg.max measurable_const
  have hgpB(x:HeatCircle):gp x≤B:=max_le ((le_abs_self _).trans (hgB x)) B.2
  have hgnB(x:HeatCircle):gn x≤B:=max_le ((neg_le_abs _).trans (hgB x)) B.2
  obtain ⟨ip,hip⟩:=original_input_density 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
    J hIJ₀ hIJ₁ T hterm hstop htarget hcenter hT hnull hJ hΛ hA hh gp hgp B
      (fun x=>le_max_right _ _) hgpB k
  obtain ⟨ineg,hin⟩:=original_input_density 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
    J hIJ₀ hIJ₁ T hterm hstop htarget hcenter hT hnull hJ hΛ hA hh gn hgn B
      (fun x=>le_max_right _ _) hgnB k
  refine ⟨ip-ineg,?_⟩
  have hs:J.integral (ip-ineg)=J.integral ip-J.integral ineg:=map_sub J.integral ip ineg
  have ha:=Lp.coeFn_sub (J.integral ip) (J.integral ineg)
  rw [←hs] at ha
  filter_upwards [hip,hin,ha] with ω hp hn hhω
  rw [hhω,Pi.sub_apply,hp,hn]
  obtain ⟨C,hC,hCb⟩:=UncutRootFields.field_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ k
  let Y:=fun x:HeatCircle=>UncutRootFields.field
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L 2 k (ω,x)
  have hYm:Measurable Y:=(UncutRootFields.field_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L 2 k).comp
      (measurable_const.prodMk measurable_id)
  have hiY:Integrable Y AddCircle.haarAddCircle:=
    (integrable_const C).mono' hYm.aestronglyMeasurable (ae_of_all _ (fun x=>hCb 2 (ω,x)))
  have hipY:Integrable (fun x=>gp x*Y x) AddCircle.haarAddCircle:=
    hiY.bdd_mul (c:=(B:ℝ)) hgp.aestronglyMeasurable (ae_of_all _ (fun x=>by
      have hh:0≤gp x:=le_max_right _ _
      rw [Real.norm_eq_abs,abs_of_nonneg hh]
      exact hgpB x))
  have hinY:Integrable (fun x=>gn x*Y x) AddCircle.haarAddCircle:=
    hiY.bdd_mul (c:=(B:ℝ)) hgn.aestronglyMeasurable (ae_of_all _ (fun x=>by
      have hh:0≤gn x:=le_max_right _ _
      rw [Real.norm_eq_abs,abs_of_nonneg hh]
      exact hgnB x))
  rw [←integral_sub hipY hinY]
  apply integral_congr_ae
  filter_upwards with x
  change gp x*Y x-gn x*Y x=g x*Y x
  rw [←sub_mul]
  congr 1
  dsimp only [gp,gn]
  by_cases hx:0≤g x
  · rw [max_eq_left hx,max_eq_right (neg_nonpos.mpr hx)];ring
  · have hx':g x≤0:=le_of_not_ge hx
    rw [max_eq_right hx',max_eq_left (neg_nonneg.mpr hx')];ring

include hIJ₀ hIJ₁ hterm hstop htarget hcenter hT in
/-- Exact real Fourier coordinate, with no remaining root heat-gap or
recursive-cutoff premise, on the original stochastic integral. -/
theorem original_input_fourier (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hΛ:0≤Λ)
    (hA:R.totalVariance=(fun z=>κ+aV z))(hh:R.horizon≤(H:ℝ))
    (w:ℝ)(a:ℂ→L[ℝ]ℝ)(l:ℤ)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ]
      fun ω=>w*a (fourierCoeff (fun x:HeatCircle=>(UncutRootFields.field
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L 2 k (ω,x):ℂ)) l):=by
  obtain ⟨input,hi⟩:=original_input_weighted 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
    J hIJ₀ hIJ₁ T hterm hstop htarget hcenter hT hnull hJ hΛ hA hh
      (NativeScalarFourierWeight.value w a l) (NativeScalarFourierWeight.measurable w a l)
      ⟨‖w‖*‖a‖,mul_nonneg (norm_nonneg _) (norm_nonneg _)⟩
      (NativeScalarFourierWeight.bound w a l) k
  refine ⟨input,hi.trans (ae_of_all _ (fun ω=>?_))⟩
  obtain ⟨C,hC,hCb⟩:=UncutRootFields.field_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ k
  have hm:Measurable (fun x:HeatCircle=>UncutRootFields.field
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L 2 k (ω,x)):=
    (UncutRootFields.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L 2 k).comp
      (measurable_const.prodMk measurable_id)
  exact NativeScalarFourierWeight.integral _
    ((integrable_const C).mono' hm.aestronglyMeasurable (ae_of_all _ (fun x=>hCb 2 (ω,x)))) w a l

include hIJ₀ hIJ₁ hterm hstop htarget hcenter hT in
/-- The spatial Bessel Hilbert noise in the uncut finite telescope has
ALL Fourier coordinates given by the SAME original J, on one sample
event. This identifies the genuine field, not a surrogate energy bound. -/
theorem hilbert_noise_coefficients (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hΛ:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
    (hA:R.totalVariance=(fun z=>κ+aV z))(hh:R.horizon≤(H:ℝ))(k:ℕ):
    ∃inputR inputI:ℤ→Process (E:=Both RealHaarInput) 𝓕 μ H,∀ᵐω∂μ,∀l:ℤ,
      J.integral (inputR l) ω=(fourierCoeff (UncutRootHilbert.value
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ hρ 2 k ω) l).re ∧
      J.integral (inputI l) ω=(fourierCoeff (UncutRootHilbert.value
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ hρ 2 k ω) l).im:=by
  let w:=fun l:ℤ=>(Λ+(l:ℝ)^2)^(-ρ/2)
  have hexR(l:ℤ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ]
      fun ω=>w l*Complex.re (fourierCoeff (fun x:HeatCircle=>(UncutRootFields.field
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L 2 k (ω,x):ℂ)) l):=
    original_input_fourier 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
      J hIJ₀ hIJ₁ T hterm hstop htarget hcenter hT hnull hJ (zero_le_one.trans hΛ) hA hh
        (w l) Complex.reCLM l k
  have hexI(l:ℤ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,J.integral input=ᵐ[μ]
      fun ω=>w l*Complex.im (fourierCoeff (fun x:HeatCircle=>(UncutRootFields.field
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L 2 k (ω,x):ℂ)) l):=
    original_input_fourier 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
      J hIJ₀ hIJ₁ T hterm hstop htarget hcenter hT hnull hJ (zero_le_one.trans hΛ) hA hh
        (w l) Complex.imCLM l k
  choose inputR hR using hexR
  choose inputI hI using hexI
  refine ⟨inputR,inputI,?_⟩
  let F:=fun z:Ω×HeatCircle=>(UncutRootFields.field
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L 2 k z:ℂ)
  have hF:Measurable F:=Complex.continuous_ofReal.measurable.comp
    (UncutRootFields.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L 2 k)
  have hp(ω:Ω):MeasurableL2FieldAE.squareMass AddCircle.haarAddCircle F ω<∞:=
    (MeasurableL2FieldAE.section_memLp_iff AddCircle.haarAddCircle F hF ω).mp
      (UncutRootHilbert.section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ 2 k ω)
  filter_upwards [ae_all_iff.mpr hR,ae_all_iff.mpr hI] with ω hr hi l
  have hc:=NativeBesselFieldAE.coefficients Λ ρ hΛ hρ F hF ω (hp ω) l
  change fourierCoeff (UncutRootHilbert.value
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hΛ hρ 2 k ω) l=
      (w l:ℂ)*fourierCoeff (fun x=>F (ω,x)) l at hc
  constructor
  · rw [hc,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact hr l
  · rw [hc,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    exact hi l

end SHE.ScalarRootUncutOriginalNoise
