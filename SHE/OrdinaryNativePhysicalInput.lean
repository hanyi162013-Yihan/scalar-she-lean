module
public import SHE.OrdinaryNativeOriginalInput
public import SHE.OrdinaryRootPhysicalInput
public import SHE.OrdinaryUncutPhysicalLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryNativePhysicalInput
open Set Filter MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  CutoffWordLevel CutoffWordHistories IntegratedPhysicalStep OrthogonalItoChannels Topology
open scoped NNReal ENNReal
local instance ordinaryNativePhysicalInput_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryNativePhysicalInput_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryNativePhysicalInput_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryNativePhysicalInput_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryNativePhysicalInput_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryNativePhysicalInput_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryNativePhysicalInput_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance ordinaryNativePhysicalInput_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryNativePhysicalInput_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
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
/-- Literal native ordinary-U gradient input after BOTH recursive
cutoffs and the original zero root heat gap, on the SAME scalar J. -/
theorem original_input (hh:R.horizon≤(H:ℝ))(hh1:R.horizon≤1)(hstart:R.base<T)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H]
        (fun z=>∫p,OrdinaryUncutPhysicalGradient.raw m L k (p,z) ∂historyMeasure R ν k)∧
      m.scalarIto.integral input=ᵐ[μ]
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
      input=ᵐ[energyMeasure μ H] (fun z=>∫p,OrdinaryPhysicalGradient.raw m
        (RecursiveHeatBounds.level L (e j) (hep j) 0 k) (p,z) ∂σ)∧
      m.scalarIto.integral input=ᵐ[μ] field (e j):=by
    have hr:=OrdinaryNativeOriginalInput.root_converges L m T hterm hstop htarget hcenter ν c hν (e j) (hep j)
    have hx:=OrdinaryRootPhysicalInput.original_input L m hh hh1 (e j) (hep j) ν
      (fun x=>by rw [hterm];exact hstart) hr k
    simpa only [field,cut,OrdinaryUncutNoise.cutoff,dif_pos (hep j),RootHeatBounds.level_zero,σ] using hx
  choose input hraw hinput using hex
  have hlim:Tendsto (fun j=>∫ω,‖field (e j) ω-G ω‖^2 ∂μ) atTop (𝓝 0):=by
    have ht:=(OrdinaryUncutNoise.averaged_limit m L ν k).2.comp het
    convert! ht using 1
    funext j
    apply integral_congr_ae
    filter_upwards with ω
    have he:=integral_sub (hci (e j) ω) (hri ω)
    try simp only [Pi.sub_apply] at he
    rw [he]
  exact TerminalItoRawLimit.original_input 𝓕 μ H m.scalarIto input (fun j=>field (e j)) G hg hinput hlim
    (fun j z=>∫p,OrdinaryPhysicalGradient.raw m (RecursiveHeatBounds.level L (e j) (hep j) 0 k) (p,z) ∂σ)
    (fun z=>∫p,OrdinaryUncutPhysicalGradient.raw m L k (p,z) ∂σ) hraw
    (OrdinaryUncutPhysicalLimit.average_tendsto m L k hh hh1 σ hW e hep het)

end SHE.OrdinaryNativePhysicalInput
