module
public import SHE.OrdinaryRootHeatLevel
public import SHE.OrdinaryUncutLevel
public import SHE.ScalarRootHeatLeaf

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.OrdinaryNativeRootLevel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffWordAnalytic IntegratedPhysicalStep Filter Topology
open scoped NNReal
local instance ordinaryNativeRootLevel_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryNativeRootLevel_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryNativeRootLevel_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable {R:ReferenceData}(L:Level R HeatCircle 1)
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable (T:ℝ)(hterm:∀x,L.terminal x=T)
variable (hstop:∀x,(L.observations.observations x 0).stop=T)
variable (htarget:∀x,(L.observations.observations x 0).target=T)
variable (hcenter:∀x,(L.observations.observations x 0).center=x)

include hterm hstop htarget hcenter in
/-- Native scalar representative convergence discharges the root heat
limit for the actual rough-coefficient process itself. -/
theorem root_converges (δ:ℝ)(hδ:0<δ):
    OrdinaryRootHeatLevel.RootConverges L δ hδ m AddCircle.haarAddCircle:=by
  change Tendsto (fun ε:ℝ=>∫z:HeatCircle×Ω,
    |JointWordAnalytic.leaf (RootHeatBounds.shift L ε.toNNReal) 0
        m.wordState.physicalState m.wordState.physicalState m.wordState.physicalField m.wordState.physicalField z.1 z.2-
      JointWordAnalytic.leaf (RootHeatBounds.shift L 0) 0
        m.wordState.physicalState m.wordState.physicalState m.wordState.physicalField m.wordState.physicalField z.1 z.2|
      ∂AddCircle.haarAddCircle.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0)
  have hs:RootHeatBounds.shift L 0=L:=by
    cases L
    simp only [RootHeatBounds.shift,NNReal.coe_zero,add_zero]
  rw [hs]
  exact ScalarRootHeatLeaf.integrated_root_difference_tendsto_zero L T hterm hstop htarget hcenter
    m.wordState m.wordState 0

include hterm hstop htarget hcenter in
/-- Actual ordinary-U finite level at zero root heat gap. The smooth
coefficient belongs only to the auxiliary words, not to the actual bracket. -/
theorem expected_zero_heat_level (δ:ℝ)(hδ:0<δ)
    (hlocal:StandardTerminalPastLocality m.scalarIto)
    (v:ℝ≥0)(hbase:R.base=(v:ℝ))(hh:R.horizon≤(H:ℝ))(hstart:R.base<T)(k:ℕ):
    OrdinaryZeroHeatLevel.leafMass L δ hδ m AddCircle.haarAddCircle 0 k=
      OrdinaryZeroHeatLevel.referenceMass L δ hδ m AddCircle.haarAddCircle 0 k+
      OrdinaryZeroHeatLevel.remainderMass L δ hδ m AddCircle.haarAddCircle 0 k:=by
  have he:=OrdinaryRootHeatLevel.expected_zero_root_level L δ hδ m hlocal v hbase hh
    (fun x=>by rw [hterm];exact hstart) AddCircle.haarAddCircle
    (root_converges L m T hterm hstop htarget hcenter δ hδ) k
  simpa only [OrdinaryRootHeatLevel.leafMass,OrdinaryRootHeatLevel.referenceMass,
    OrdinaryRootHeatLevel.remainderMass,OrdinaryRootHeatLevel.data,RootHeatBounds.level_zero,
    OrdinaryZeroHeatLevel.leafMass,OrdinaryZeroHeatLevel.referenceMass,OrdinaryZeroHeatLevel.remainderMass,
    OrdinaryZeroHeatLevel.data] using he

include hterm hstop htarget hcenter in
/-- Every recursive cutoff and the original native root heat gap are
removed in the genuine ordinary-U expected level identity. -/
theorem expected_uncut_level (hlocal:StandardTerminalPastLocality m.scalarIto)
    (v:ℝ≥0)(hbase:R.base=(v:ℝ))(hh:R.horizon≤(H:ℝ))(hstart:R.base<T)(k:ℕ):
    OrdinaryUncutLevel.leafMass L m AddCircle.haarAddCircle k=
      OrdinaryUncutLevel.referenceMass L m AddCircle.haarAddCircle k+
      OrdinaryUncutLevel.remainderMass L m AddCircle.haarAddCircle k:=by
  let ν:Measure HeatCircle:=AddCircle.haarAddCircle
  let U:=m.physicalState
  let X:=m.physicalField
  let Leaf:=fun δ:ℝ=>∫z:History HeatCircle k×Ω,JointUncutEvaluationLimit.cutoffLeaf L 0 U U X X δ k z.1 z.2
    ∂(historyMeasure R ν k).prod μ
  let Ref:=fun δ:ℝ=>∫z:History HeatCircle k×Ω,JointUncutEvaluationLimit.cutoffReference L 0 U U X X δ k z.1 z.2
    ∂(historyMeasure R ν k).prod μ
  let Rem:=fun δ:ℝ=>∫z:History HeatCircle k×Ω,ActualUncutRemainder.cutoff L (fun x=>κ+a x) U X δ k z.1 z.2
    ∂(historyMeasure R ν k).prod μ
  have hl:Tendsto Leaf (𝓝[>] (0:ℝ)) (𝓝 (OrdinaryUncutLevel.leafMass L m ν k)):=by
    have ht:=JointUncutEvaluationLimit.leaf_integral_tendsto L 0 U U X X
      m.physicalState_measurable m.physicalState_measurable m.physicalField_measurable m.physicalField_measurable ν μ k
    convert! ht using 1
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun z=>(OrdinaryJointSelf.uncutLeaf L 0 U X k z.1 z.2).symm)
  have hr:Tendsto Ref (𝓝[>] (0:ℝ)) (𝓝 (OrdinaryUncutLevel.referenceMass L m ν k)):=
    JointUncutEvaluationLimit.reference_integral_tendsto L 0 U U X X
      m.physicalState_measurable m.physicalState_measurable m.physicalField_measurable m.physicalField_measurable ν μ k
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have ha:Measurable (fun z=>κ+a z):=measurable_const.add m.variance_measurable
  have hb(z):|κ+a z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg m.additive_pos.le (m.lower_pos.le.trans (m.variance_bounds z).1))]
    exact add_le_add le_rfl (m.variance_bounds z).2
  have hm:Tendsto Rem (𝓝[>] (0:ℝ)) (𝓝 (OrdinaryUncutLevel.remainderMass L m ν k)):=
    ActualUncutRemainder.integral_tendsto L (fun z=>κ+a z) ha (add_nonneg m.additive_pos.le hM) hb U X
      m.physicalState_measurable m.physicalField_measurable ν μ k
  have he:∀ᶠδ:ℝ in 𝓝[>] (0:ℝ),Leaf δ=Ref δ+Rem δ:=by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0<δ at hδ
    have hh':=expected_zero_heat_level L m T hterm hstop htarget hcenter δ hδ hlocal v hbase hh hstart k
    have hl':Leaf δ=OrdinaryZeroHeatLevel.leafMass L δ hδ m ν 0 k:=by
      apply integral_congr_ae
      filter_upwards with z
      rw [JointUncutEvaluationLimit.cutoffLeaf,dif_pos hδ]
      unfold JointWordAnalytic.leaf
      rw [OrdinaryJointSelf.state]
      rfl
    have hr':Ref δ=OrdinaryZeroHeatLevel.referenceMass L δ hδ m ν 0 k:=by
      apply integral_congr_ae
      filter_upwards with z
      rw [JointUncutEvaluationLimit.cutoffReference,dif_pos hδ,OrdinaryJointSelf.reference]
      rfl
    have hm':Rem δ=OrdinaryZeroHeatLevel.remainderMass L δ hδ m ν 0 k:=by
      apply integral_congr_ae
      filter_upwards with z
      rw [ActualUncutRemainder.cutoff,dif_pos hδ]
      rfl
    rw [hl',hr',hm']
    exact hh'
  exact tendsto_nhds_unique hl ((hr.add hm).congr' (he.mono (fun _ h=>h.symm)))

end SHE.OrdinaryNativeRootLevel
