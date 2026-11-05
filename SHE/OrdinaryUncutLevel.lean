module
public import SHE.OrdinaryJointSelf
public import SHE.OrdinaryZeroHeatLevel
public import SHE.JointUncutEvaluationLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.OrdinaryUncutLevel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  RecursiveHeatBounds CutoffWordAnalytic IntegratedPhysicalStep Filter Topology
open scoped NNReal
local instance ordinaryUncutLevel_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryUncutLevel_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type}[MeasurableSpace P][MeasurableSpace Ω]
variable {R:ReferenceData}{n:ℕ}(L:Level R P n)
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)

def leafMass (ν:Measure P)(k:ℕ):ℝ:=
  ∫z:History P k×Ω,UncutWordEvaluation.leaf L m.physicalState m.physicalField k z.1 z.2
    ∂(historyMeasure R ν k).prod μ
def referenceMass (ν:Measure P)(k:ℕ):ℝ:=
  ∫z:History P k×Ω,JointUncutWordEvaluation.reference L 0 m.physicalState m.physicalState
    m.physicalField m.physicalField k z.1 z.2 ∂(historyMeasure R ν k).prod μ
def remainderMass (ν:Measure P)(k:ℕ):ℝ:=
  ∫z:History P k×Ω,ActualUncutRemainder.value L (fun x=>κ+a x) m.physicalState m.physicalField k z.1 z.2
    ∂(historyMeasure R ν k).prod μ

/-- All recursive time cutoffs are removed in the actual ordinary-U
level identity. Only the initial positive root heat gap is retained;
the bracket coefficient remains merely measurable throughout. -/
theorem expected_uncut_level (hlocal:StandardTerminalPastLocality m.scalarIto)
    (v:ℝ≥0)(hbase:R.base=(v:ℝ))(hh:R.horizon≤(H:ℝ))
    (ν:Measure P)[IsFiniteMeasure ν]{η:ℝ}(hη:0<η)(hgap:HeatCutoffHistories.Gap L η)(k:ℕ):
    leafMass L m ν k=referenceMass L m ν k+remainderMass L m ν k:=by
  let U:=m.physicalState
  let X:=m.physicalField
  let Leaf:=fun δ:ℝ=>∫z:History P k×Ω,JointUncutEvaluationLimit.cutoffLeaf L 0 U U X X δ k z.1 z.2
    ∂(historyMeasure R ν k).prod μ
  let Ref:=fun δ:ℝ=>∫z:History P k×Ω,JointUncutEvaluationLimit.cutoffReference L 0 U U X X δ k z.1 z.2
    ∂(historyMeasure R ν k).prod μ
  let Rem:=fun δ:ℝ=>∫z:History P k×Ω,ActualUncutRemainder.cutoff L (fun x=>κ+a x) U X δ k z.1 z.2
    ∂(historyMeasure R ν k).prod μ
  have hl:Tendsto Leaf (𝓝[>] (0:ℝ)) (𝓝 (leafMass L m ν k)):=by
    have ht:=JointUncutEvaluationLimit.leaf_integral_tendsto L 0 U U X X
      m.physicalState_measurable m.physicalState_measurable m.physicalField_measurable m.physicalField_measurable ν μ k
    convert! ht using 1
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun z=>(OrdinaryJointSelf.uncutLeaf L 0 U X k z.1 z.2).symm)
  have hr:Tendsto Ref (𝓝[>] (0:ℝ)) (𝓝 (referenceMass L m ν k)):=
    JointUncutEvaluationLimit.reference_integral_tendsto L 0 U U X X
      m.physicalState_measurable m.physicalState_measurable m.physicalField_measurable m.physicalField_measurable ν μ k
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have ha:Measurable (fun z=>κ+a z):=measurable_const.add m.variance_measurable
  have hb(z):|κ+a z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg m.additive_pos.le (m.lower_pos.le.trans (m.variance_bounds z).1))]
    exact add_le_add le_rfl (m.variance_bounds z).2
  have hm:Tendsto Rem (𝓝[>] (0:ℝ)) (𝓝 (remainderMass L m ν k)):=
    ActualUncutRemainder.integral_tendsto L (fun z=>κ+a z) ha (add_nonneg m.additive_pos.le hM) hb U X
      m.physicalState_measurable m.physicalField_measurable ν μ k
  have he:∀ᶠδ:ℝ in 𝓝[>] (0:ℝ),Leaf δ=Ref δ+Rem δ:=by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0<δ at hδ
    have hh':=OrdinaryZeroHeatLevel.expected_zero_heat_level L δ hδ m hlocal v hbase hh ν hη hgap k
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

end SHE.OrdinaryUncutLevel
