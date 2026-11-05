module
public import SHE.OrdinaryRootHeatLevel
public import SHE.ActualRootRemainderL2
public import SHE.ScalarL2LimitAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryRootNoiseL2
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffWordAnalytic IntegratedPhysicalStep Topology
open scoped NNReal
local instance ordinaryRootNoiseL2_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryRootNoiseL2_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type}[MeasurableSpace P][MeasurableSpace Ω]
variable {R:ReferenceData}{n:ℕ}(L:Level R P n)(δ:ℝ)(hδ:0<δ)
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)

/-- Strong root-heat closure of the COMPLETE ordinary-U physical noise,
including its actual rough bracket remainder. -/
theorem noise_limit (ν:Measure P)[IsFiniteMeasure ν]
    (hstart:∀p,R.base<L.terminal p)(hroot:OrdinaryRootHeatLevel.RootConverges L δ hδ m ν)(k:ℕ):
    let E:=fun ε:ℝ=>fun ω=>∫p,
      (OrdinaryRootHeatLevel.data L δ hδ m ε.toNNReal k).noiseVersion p ω-
      (OrdinaryRootHeatLevel.data L δ hδ m 0 k).noiseVersion p ω ∂historyMeasure R ν k
    (∀ε,Integrable (fun ω=>‖E ε ω‖^2) μ) ∧
      Tendsto (fun ε=>∫ω,‖E ε ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
  intro E
  let σ:=historyMeasure R ν k
  let FL:=fun ε:ℝ≥0=>fun z:History P k×Ω=>(OrdinaryRootHeatLevel.data L δ hδ m ε k).leaf z.1 z.2
  let FR:=fun ε:ℝ≥0=>fun z:History P k×Ω=>(OrdinaryRootHeatLevel.data L δ hδ m ε k).reference z.1 z.2
  let FC:=fun ε:ℝ≥0=>fun z:History P k×Ω=>(OrdinaryRootHeatLevel.data L δ hδ m ε k).remainder z.1 z.2
  let error:=fun (F:ℝ≥0→History P k×Ω→ℝ)=>fun ε:ℝ=>fun ω=>∫p,F ε.toNNReal (p,ω)-F 0 (p,ω) ∂σ
  have hfmL(ε:ℝ≥0):Measurable (FL ε):=physical_leaf_measurable (RootHeatBounds.level L δ hδ ε k)
    m.physicalState_measurable m.physicalField_measurable (fun _ _ _=>0)
  have hfmR(ε:ℝ≥0):Measurable (FR ε):=physical_reference_measurable (RootHeatBounds.level L δ hδ ε k)
    m.physicalState_measurable m.physicalField_measurable (fun _ _ _=>0)
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have ha:Measurable (fun z=>κ+a z):=measurable_const.add m.variance_measurable
  have hAn:0≤κ+M:=add_nonneg m.additive_pos.le hM
  have hcap(z):|κ+a z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg m.additive_pos.le (m.lower_pos.le.trans (m.variance_bounds z).1))]
    exact add_le_add le_rfl (m.variance_bounds z).2
  have hfmC(ε:ℝ≥0):Measurable (FC ε):=ActualVarianceLevel.remainder_measurable
    (RootHeatBounds.level L δ hδ ε k) (fun z=>κ+a z) ha
    m.physicalState m.physicalState_measurable m.physicalField m.physicalField_measurable (fun _ _ _=>0)
  have hem (F:ℝ≥0→History P k×Ω→ℝ)(hm:∀ε,Measurable (F ε))(ε:ℝ):Measurable (error F ε):=
    ((((hm ε.toNNReal).sub (hm 0)).comp measurable_swap).stronglyMeasurable.integral_prod_right').measurable
  have avg (F:ℝ≥0→History P k×Ω→ℝ)(hm:∀ε,Measurable (F ε))
      (C:ℝ)(hC:0≤C)(hb:∀ε p ω,‖F ε (p,ω)‖≤C)
      (ht:Tendsto (fun ε:ℝ=>∫q,‖F ε.toNNReal q-F 0 q‖ ∂σ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0)):
      (∀ε,Integrable (fun ω=>‖error F ε ω‖^2) μ) ∧
        Tendsto (fun ε=>∫ω,‖error F ε ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0):=
    WeightedHistoryL2Limit.averaged_limit σ μ (fun ε:ℝ=>F ε.toNNReal) (F 0)
      (fun ε=>hm ε.toNNReal) (hm 0) (fun _=>1) (integrable_const 1) (fun _=>zero_le_one) hC
      (fun ε p ω=>by simpa only [mul_one] using hb ε.toNNReal p ω)
      (fun p ω=>by simpa only [mul_one] using hb 0 p ω) (𝓝[>] (0:ℝ)) ht
  obtain ⟨B,hB,hBb⟩:=(RootHeatBounds.test_uniform L δ hδ k).norm_bound
  have hbL:∀ε p ω,‖FL ε (p,ω)‖≤B:=fun ε p ω=>hBb (ε,p) _
  have hbR:∀ε p ω,‖FR ε (p,ω)‖≤B:=fun ε p ω=>GaussianSmooth.average_norm_bound _ (hBb (ε,p)) _
  have htL:Tendsto (fun ε:ℝ=>∫q,‖FL ε.toNNReal q-FL 0 q‖ ∂σ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    simpa only [FL,OrdinaryRootHeatLevel.leaf_eq,Real.norm_eq_abs] using
      RootJointHeatLeafLimit.integrated_leaf_difference_tendsto_zero L δ hδ m.wordState m.wordState 0 ν hroot k
  have htR:Tendsto (fun ε:ℝ=>∫q,‖FR ε.toNNReal q-FR 0 q‖ ∂σ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    simpa only [FR,OrdinaryRootHeatLevel.reference_eq,Real.norm_eq_abs] using
      RootJointReferenceLimit.integrated_reference_difference_tendsto_zero L δ hδ 0
        m.physicalState m.physicalState m.physicalField m.physicalField hstart
        m.physicalState_measurable m.physicalState_measurable m.physicalField_measurable m.physicalField_measurable ν μ k
  have hL:=avg FL hfmL B hB hbL htL
  have hR:=avg FR hfmR B hB hbR htR
  have hC:=ActualRootRemainderL2.averaged_limit L δ hδ (fun z=>κ+a z) ha hAn hcap
    m.physicalState m.physicalField m.physicalState_measurable m.physicalField_measurable ν μ k
  change (∀ε,Integrable (fun ω=>‖error FC ε ω‖^2) μ) ∧
    Tendsto (fun ε=>∫ω,‖error FC ε ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) at hC
  have hLR:=ScalarL2LimitAlgebra.sub μ (error FL) (error FR) (hem FL hfmL) (hem FR hfmR)
    hL.1 hR.1 (𝓝[>] (0:ℝ)) hL.2 hR.2
  have hfinal:=ScalarL2LimitAlgebra.sub μ (fun ε ω=>error FL ε ω-error FR ε ω) (error FC)
    (fun ε=>(hem FL hfmL ε).sub (hem FR hfmR ε)) (hem FC hfmC)
    hLR.1 hC.1 (𝓝[>] (0:ℝ)) hLR.2 hC.2
  obtain ⟨C,hCn,hCb⟩:=ActualRootRemainder.uniform_remainder_bound L δ hδ (fun z=>κ+a z) hAn hcap
    m.physicalState m.physicalField k
  have hparts(ε:ℝ≥0)(ω:Ω):Integrable (fun p=>FL ε (p,ω)) σ ∧
      Integrable (fun p=>FR ε (p,ω)) σ ∧ Integrable (fun p=>FC ε (p,ω)) σ:=by
    have hi(F:History P k×Ω→ℝ)(hm:Measurable F)(C:ℝ)(hb:∀p,‖F (p,ω)‖≤C):Integrable (fun p=>F (p,ω)) σ:=
      (integrable_const C).mono' (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable (Eventually.of_forall hb)
    exact ⟨hi _ (hfmL ε) B (fun p=>hbL ε p ω),hi _ (hfmR ε) B (fun p=>hbR ε p ω),
      hi _ (hfmC ε) C (fun p=>hCb ε p ω)⟩
  have he:E=fun ε ω=>error FL ε ω-error FR ε ω-error FC ε ω:=by
    funext ε ω
    obtain ⟨hl,hr,hc⟩:=hparts ε.toNNReal ω
    obtain ⟨hl0,hr0,hc0⟩:=hparts 0 ω
    have hh:E ε ω=∫p,(FL ε.toNNReal (p,ω)-FL 0 (p,ω))-
        (FR ε.toNNReal (p,ω)-FR 0 (p,ω))-(FC ε.toNNReal (p,ω)-FC 0 (p,ω)) ∂σ:=by
      apply integral_congr_ae
      filter_upwards with p
      dsimp only [LevelData.noiseVersion,FL,FR,FC]
      ring
    rw [hh]
    have hs1:=integral_sub (hl.sub hl0) (hr.sub hr0)
    have hs2:=integral_sub ((hl.sub hl0).sub (hr.sub hr0)) (hc.sub hc0)
    simp only [Pi.sub_apply] at hs1 hs2
    dsimp only [error]
    linarith only [hs1,hs2]
  rw [he]
  exact hfinal

end SHE.OrdinaryRootNoiseL2
