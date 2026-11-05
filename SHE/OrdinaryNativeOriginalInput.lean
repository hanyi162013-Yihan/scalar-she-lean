module
public import SHE.OrdinaryRootOriginalInput
public import SHE.OrdinaryNativeRootLevel
public import SHE.OrdinaryUncutNoise

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryNativeOriginalInput
open Set Filter MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  CutoffWordLevel CutoffWordHistories IntegratedPhysicalStep OrthogonalItoChannels Topology
open scoped NNReal ENNReal
local instance ordinaryNativeOriginalInput_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryNativeOriginalInput_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryNativeOriginalInput_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryNativeOriginalInput_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryNativeOriginalInput_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryNativeOriginalInput_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryNativeOriginalInput_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance ordinaryNativeOriginalInput_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryNativeOriginalInput_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable {R:ReferenceData}(L:Level R HeatCircle 1)
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable (T:ℝ)(hterm:∀x,L.terminal x=T)
variable (hstop:∀x,(L.observations.observations x 0).stop=T)
variable (htarget:∀x,(L.observations.observations x 0).target=T)
variable (hcenter:∀x,(L.observations.observations x 0).center=x)
variable (ν:Measure HeatCircle)[IsFiniteMeasure ν]
variable (c:ℝ≥0)(hν:ν≤(c:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle))

include hterm hstop htarget hcenter hν in
/-- Bounded root densities retain native heat convergence. In
particular root Fourier and bounded localization tests are allowed. -/
theorem root_converges (δ:ℝ)(hδ:0<δ):OrdinaryRootHeatLevel.RootConverges L δ hδ m ν:=by
  let f:=fun ε:ℝ=>fun z:History HeatCircle 0×Ω=>
    |RootJointHeatLeafLimit.leaf L δ hδ m.wordState m.wordState 0 ε.toNNReal 0 z.1 z.2-
      RootJointHeatLeafLimit.leaf L δ hδ m.wordState m.wordState 0 0 0 z.1 z.2|
  let σ:Measure (History HeatCircle 0×Ω):=AddCircle.haarAddCircle.prod μ
  have ht:=OrdinaryNativeRootLevel.root_converges L m T hterm hstop htarget hcenter δ hδ
  change Tendsto (fun ε=>∫z,f ε z ∂σ) (𝓝[>] (0:ℝ)) (𝓝 0) at ht
  obtain ⟨B,hB,hBb⟩:=(RootHeatBounds.test_uniform L δ hδ 0).norm_bound
  have hi(ε:ℝ):Integrable (f ε) σ:=by
    have hm:=((RootJointHeatLeafLimit.leaf_measurable L δ hδ m.wordState m.wordState 0 ε.toNNReal 0).sub
      (RootJointHeatLeafLimit.leaf_measurable L δ hδ m.wordState m.wordState 0 0 0)).norm
    apply (integrable_const (2*B)).mono' hm.aestronglyMeasurable
    filter_upwards with z
    change ‖|_|‖≤_
    rw [Real.norm_eq_abs,abs_abs]
    exact (abs_sub _ _).trans (by
      have h1:|RootJointHeatLeafLimit.leaf L δ hδ m.wordState m.wordState 0 ε.toNNReal 0 z.1 z.2|≤B:=hBb (ε.toNNReal,z.1) _
      have h0:|RootJointHeatLeafLimit.leaf L δ hδ m.wordState m.wordState 0 0 0 z.1 z.2|≤B:=hBb ((0:ℝ≥0),z.1) _
      linarith)
  have hprod:ν.prod μ≤(c:ℝ≥0∞) • σ:=by
    simpa only [Measure.prod_smul_left,σ] using Measure.prod_mono hν (le_refl μ)
  change Tendsto (fun ε=>∫z,f ε z ∂ν.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0)
  apply squeeze_zero (fun ε=>integral_nonneg (fun z=>abs_nonneg _))
    (fun ε=>?_) (by simpa using ht.const_mul (c:ℝ))
  have hh:=integral_mono_measure hprod (Eventually.of_forall (fun z=>abs_nonneg _))
    ((hi ε).smul_measure (by finiteness:(c:ℝ≥0∞)≠∞))
  rw [integral_smul_measure,ENNReal.coe_toReal,smul_eq_mul] at hh
  convert! hh using 1

include hterm hstop htarget hcenter hν in
/-- Original-J input after BOTH recursive cutoffs and the native root
heat gap have been removed, for the actual rough ordinary-U bracket.
The reference member is still fixed before sample substitution. -/
theorem original_post_input (hlocal:StandardTerminalPastLocality m.scalarIto)
    (v:ℝ≥0)(hbase:R.base=(v:ℝ))(hh:R.horizon≤(H:ℝ))(hstart:R.base<T)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      m.scalarIto.integral (PastItoInputs.post 𝓕 μ H v input)=ᵐ[μ]
        fun ω=>∫p,OrdinaryUncutNoise.value m L k p ω ∂historyMeasure R ν k:=by
  let σ:=historyMeasure R ν k
  let W:=UncutSmoothWords.weight L k
  have hW:Integrable W σ:=UncutHistoryMass.weight_integrable L ν k
  let raw:=fun z:History HeatCircle k×Ω=>OrdinaryUncutNoise.value m L k z.1 z.2
  let cut:=fun δ:ℝ=>fun z:History HeatCircle k×Ω=>OrdinaryUncutNoise.cutoff m L δ k z.1 z.2
  let field:=fun δ:ℝ=>fun ω=>∫p,cut δ (p,ω) ∂σ
  let G:=fun ω=>∫p,raw (p,ω) ∂σ
  obtain ⟨C,hC,hCb⟩:=OrdinaryUncutNoise.bound m L k
  have hrm:Measurable raw:=OrdinaryUncutNoise.value_measurable m L k
  have hcm(δ:ℝ):Measurable (cut δ):=by
    by_cases hδ:0<δ
    · simpa only [cut,OrdinaryUncutNoise.cutoff,dif_pos hδ] using
        OrdinaryUncutNoise.version_measurable m (RecursiveHeatBounds.level L δ hδ 0 k)
    · simp only [cut,OrdinaryUncutNoise.cutoff,dif_neg hδ]
      exact measurable_const
  have hcb(δ:ℝ)(p:History HeatCircle k)(ω:Ω):‖cut δ (p,ω)‖≤C*W p:=by
    by_cases hδ:0<δ
    · change ‖OrdinaryUncutNoise.cutoff m L δ k p ω‖≤_
      rw [OrdinaryUncutNoise.cutoff_eq m L hδ]
      split_ifs
      · exact hCb p ω
      · exact (norm_zero).le.trans (mul_nonneg hC (UncutSmoothWords.weight_nonneg L k p))
    · simp only [cut,OrdinaryUncutNoise.cutoff,dif_neg hδ,norm_zero]
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
  let e:ℕ→ℝ:=fun j=>1/((j:ℝ)+1)
  have hep(j:ℕ):0<e j:=by dsimp [e];positivity
  have het:Tendsto e atTop (𝓝[>] (0:ℝ)):=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall hep⟩
  have hex(j:ℕ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      m.scalarIto.integral (PastItoInputs.post 𝓕 μ H v input)=ᵐ[μ] field (e j):=by
    have hr:=root_converges L m T hterm hstop htarget hcenter ν c hν (e j) (hep j)
    have hx:=OrdinaryRootOriginalInput.original_post_input L m hlocal v hbase hh (e j) (hep j) ν
      (fun x=>by rw [hterm];exact hstart) hr k
    simpa only [field,cut,OrdinaryUncutNoise.cutoff,OrdinaryUncutNoise.version,
      dif_pos (hep j),OrdinaryRootHeatLevel.data,RootHeatBounds.level_zero,
      OrdinaryModelLevelIto.data,OrdinaryLevelOriginalNoise.data,σ] using hx
  choose input hinput using hex
  have hlim:Tendsto (fun j=>∫ω,‖field (e j) ω-G ω‖^2 ∂μ) atTop (𝓝 0):=by
    have ht:=(OrdinaryUncutNoise.averaged_limit m L ν k).2.comp het
    convert! ht using 1
    funext j
    apply integral_congr_ae
    filter_upwards with ω
    have he:=integral_sub (hci (e j) ω) (hri ω)
    try simp only [Pi.sub_apply] at he
    rw [he]
  exact PastItoLimitWitness.original_post_limit 𝓕 μ H v m.scalarIto input (fun j=>field (e j)) G hg hinput hlim

end SHE.OrdinaryNativeOriginalInput
