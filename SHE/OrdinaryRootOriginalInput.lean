module
public import SHE.OrdinaryOriginalAverage
public import SHE.OrdinaryRootNoiseL2

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryRootOriginalInput
open Set Filter MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  CutoffWordLevel CutoffWordHistories IntegratedPhysicalStep OrthogonalItoChannels Topology
open scoped NNReal
local instance ordinaryRootOriginalInput_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryRootOriginalInput_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryRootOriginalInput_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryRootOriginalInput_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryRootOriginalInput_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryRootOriginalInput_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance ordinaryRootOriginalInput_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryRootOriginalInput_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type}[MeasurableSpace P][MeasurableSpace Ω]
variable {R:ReferenceData}{n:ℕ}(L:Level R P n)
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)

/-- The genuine zero-root-heat ordinary-U noise retains the SAME
original full-horizon Ito driver and support strictly after v. -/
theorem original_post_input (hlocal:StandardTerminalPastLocality m.scalarIto)
    (v:ℝ≥0)(hbase:R.base=(v:ℝ))(hh:R.horizon≤(H:ℝ))
    (δ:ℝ)(hδ:0<δ)(ν:Measure P)[IsFiniteMeasure ν]
    (hstart:∀p,R.base<L.terminal p)(hroot:OrdinaryRootHeatLevel.RootConverges L δ hδ m ν)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      m.scalarIto.integral (PastItoInputs.post 𝓕 μ H v input)=ᵐ[μ]
        fun ω=>∫p,(OrdinaryRootHeatLevel.data L δ hδ m 0 k).noiseVersion p ω ∂historyMeasure R ν k:=by
  let σ:=historyMeasure R ν k
  let D:=fun ε:ℝ≥0=>OrdinaryRootHeatLevel.data L δ hδ m ε k
  let noise:=fun ε:ℝ≥0=>fun z:History P k×Ω=>(D ε).noiseVersion z.1 z.2
  let field:=fun ε:ℝ≥0=>fun ω=>∫p,noise ε (p,ω) ∂σ
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have ha:Measurable (fun z=>κ+a z):=measurable_const.add m.variance_measurable
  have hcap(z):|κ+a z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg m.additive_pos.le (m.lower_pos.le.trans (m.variance_bounds z).1))]
    exact add_le_add le_rfl (m.variance_bounds z).2
  have hD(ε:ℝ≥0):AnalyticConditions (D ε):=ActualVarianceLevel.analyticConditions
    (RootHeatBounds.level L δ hδ ε k) (fun z=>κ+a z) ha
    m.physicalState m.physicalState_measurable m.physicalField m.physicalField_measurable (fun _ _ _=>0)
    (add_nonneg m.additive_pos.le hM) hcap
  have hnm(ε:ℝ≥0):Measurable (noise ε):=
    (((hD ε).leaf_measurable.sub (hD ε).reference_measurable).sub (hD ε).remainder_measurable)
  have hfm(ε:ℝ≥0):Measurable (field ε):=(hnm ε).stronglyMeasurable.integral_prod_left'.measurable
  have hni(ε:ℝ≥0)(ω:Ω):Integrable (fun p=>noise ε (p,ω)) σ:=by
    obtain ⟨B,_,hB⟩:=uniform_level_bound (D ε) (hD ε)
    exact (integrable_const B).mono' ((hnm ε).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall (fun p=>(hB p ω).2.2.2))
  obtain ⟨B,_,hB⟩:=uniform_level_bound (D 0) (hD 0)
  have hg:MemLp (field 0) 2 μ:=MemLp.of_bound (hfm 0).aestronglyMeasurable _
    (Eventually.of_forall (fun ω=>norm_integral_le_of_norm_le_const
      (μ:=σ) (Eventually.of_forall (fun p=>(hB p ω).2.2.2))))
  let e:ℕ→ℝ≥0:=fun j=>(1/((j:ℝ)+1)).toNNReal
  have heq(j:ℕ):(e j:ℝ)=1/((j:ℝ)+1):=Real.coe_toNNReal _ (by positivity)
  have hep(j:ℕ):0<(e j:ℝ):=by rw [heq];positivity
  have het:Tendsto (fun j=>(e j:ℝ)) atTop (𝓝[>] (0:ℝ)):=by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall hep⟩
    simpa only [heq] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hex(j:ℕ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      m.scalarIto.integral (PastItoInputs.post 𝓕 μ H v input)=ᵐ[μ] field (e j):=
    OrdinaryOriginalAverage.original_post_input m (RootHeatBounds.level L δ hδ (e j) k) hlocal
      v hbase hh (hep j) (RootHeatBounds.level_gap L δ hδ (e j) k) σ
  choose input hinput using hex
  have hlim:Tendsto (fun j=>∫ω,‖field (e j) ω-field 0 ω‖^2 ∂μ) atTop (𝓝 0):=by
    have ht:=(OrdinaryRootNoiseL2.noise_limit L δ hδ m ν hstart hroot k).2.comp het
    convert! ht using 1
    funext j
    apply integral_congr_ae
    filter_upwards with ω
    have hi:=integral_sub (hni (e j) ω) (hni 0 ω)
    try simp only [Pi.sub_apply] at hi
    simp only [Real.toNNReal_coe]
    rw [hi]
  exact PastItoLimitWitness.original_post_limit 𝓕 μ H v m.scalarIto input (fun j=>field (e j)) (field 0) hg hinput hlim

end SHE.OrdinaryRootOriginalInput
