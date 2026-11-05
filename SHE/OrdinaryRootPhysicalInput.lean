module
public import SHE.OrdinaryPhysicalAverage
public import SHE.OrdinaryRootGradientLimit
public import SHE.OrdinaryRootNoiseL2
public import SHE.TerminalItoRawLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryRootPhysicalInput
open Set Filter MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  CutoffWordLevel CutoffWordHistories IntegratedPhysicalStep OrthogonalItoChannels Topology
open scoped NNReal ENNReal
local instance ordinaryRootPhysicalInput_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryRootPhysicalInput_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryRootPhysicalInput_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryRootPhysicalInput_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryRootPhysicalInput_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryRootPhysicalInput_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance ordinaryRootPhysicalInput_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryRootPhysicalInput_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {Y Ω:Type}[MeasurableSpace Y][MeasurableSpace Ω]
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)

/-- Native zero-root-heat closure retains the literal original
ordinary-U gradient input, including the actual rough bracket. -/
theorem original_input (hh:R.horizon≤(H:ℝ))(hh1:R.horizon≤1)(δ:ℝ)(hδ:0<δ)
    (ν:Measure Y)[IsFiniteMeasure ν](hstart:∀p,R.base<L.terminal p)
    (hroot:OrdinaryRootHeatLevel.RootConverges L δ hδ m ν)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>∫p,OrdinaryPhysicalGradient.raw m
        (RootHeatBounds.level L δ hδ 0 k) (p,z) ∂historyMeasure R ν k) ∧
      m.scalarIto.integral input=ᵐ[μ] fun ω=>∫p,OrdinaryUncutNoise.version m
        (RootHeatBounds.level L δ hδ 0 k) p ω ∂historyMeasure R ν k:=by
  let σ:=historyMeasure R ν k
  let Q:=RootHeatBounds.level L δ hδ
  let raw:=fun ε:ℝ≥0=>OrdinaryPhysicalGradient.raw m (Q ε k)
  let noise:=fun ε:ℝ≥0=>fun z:History Y k×Ω=>OrdinaryUncutNoise.version m (Q ε k) z.1 z.2
  let field:=fun ε:ℝ≥0=>fun ω=>∫p,noise ε (p,ω) ∂σ
  have hnm(ε:ℝ≥0):Measurable (noise ε):=OrdinaryUncutNoise.version_measurable m (Q ε k)
  have hfm(ε:ℝ≥0):Measurable (field ε):=(hnm ε).stronglyMeasurable.integral_prod_left'.measurable
  have hni(ε:ℝ≥0)(ω:Ω):Integrable (fun p=>noise ε (p,ω)) σ:=by
    obtain ⟨B,_,hB⟩:=OrdinaryUncutNoise.version_bound m (Q ε k)
    exact (integrable_const B).mono' ((hnm ε).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall (fun p=>hB p ω))
  obtain ⟨B,_,hB⟩:=OrdinaryUncutNoise.version_bound m (Q 0 k)
  have hg:MemLp (field 0) 2 μ:=MemLp.of_bound (hfm 0).aestronglyMeasurable _
    (Eventually.of_forall (fun ω=>norm_integral_le_of_norm_le_const
      (μ:=σ) (Eventually.of_forall (fun p=>hB p ω))))
  let e:ℕ→ℝ≥0:=fun j=>(1/((j:ℝ)+1)).toNNReal
  have heq(j:ℕ):(e j:ℝ)=1/((j:ℝ)+1):=Real.coe_toNNReal _ (by positivity)
  have hep(j:ℕ):0<(e j:ℝ):=by rw [heq];positivity
  have het:Tendsto (fun j=>(e j:ℝ)) atTop (𝓝[>] (0:ℝ)):=by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall hep⟩
    simpa only [heq] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hetNN:Tendsto e atTop (𝓝 0):=by
    have ht:=continuous_real_toNNReal.continuousAt.tendsto.comp (het.mono_right nhdsWithin_le_nhds)
    simpa only [Function.comp_def,Real.toNNReal_coe,Real.toNNReal_zero] using ht
  have hex(j:ℕ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>∫p,raw (e j) (p,z) ∂σ) ∧
      m.scalarIto.integral input=ᵐ[μ] field (e j):=
    OrdinaryPhysicalAverage.original_input m (Q (e j) k) hh (hep j)
      (RootHeatBounds.level_gap L δ hδ (e j) k) σ
  choose input hraw hinput using hex
  have hlim:Tendsto (fun j=>∫ω,‖field (e j) ω-field 0 ω‖^2 ∂μ) atTop (𝓝 0):=by
    have ht:=(OrdinaryRootNoiseL2.noise_limit L δ hδ m ν hstart hroot k).2.comp het
    simp only [Function.comp_def,Real.toNNReal_coe] at ht
    change Tendsto (fun j=>∫ω,‖∫p,noise (e j) (p,ω)-noise 0 (p,ω) ∂σ‖^2 ∂μ) atTop (𝓝 0) at ht
    convert! ht using 1
    funext j
    apply integral_congr_ae
    filter_upwards with ω
    have hi:=integral_sub (hni (e j) ω) (hni 0 ω)
    try simp only [Pi.sub_apply] at hi
    rw [hi]
  exact TerminalItoRawLimit.original_input 𝓕 μ H m.scalarIto input (fun j=>field (e j)) (field 0) hg hinput hlim
    (fun j z=>∫p,raw (e j) (p,z) ∂σ) (fun z=>∫p,raw 0 (p,z) ∂σ) hraw
    (OrdinaryRootGradientLimit.average_tendsto m L δ hδ k hh hh1 σ e hetNN)

end SHE.OrdinaryRootPhysicalInput
