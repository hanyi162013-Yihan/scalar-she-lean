module
public import SHE.ActualRootRemainder
public import SHE.OrdinaryZeroHeatLevel
public import SHE.OrdinaryJointSelf
public import SHE.RootJointHeatLeafLimit
public import SHE.RootJointReferenceLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.OrdinaryRootHeatLevel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  RootHeatBounds CutoffWordAnalytic IntegratedPhysicalStep Filter Topology
open scoped NNReal
local instance ordinaryRootHeatLevel_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryRootHeatLevel_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type}[MeasurableSpace P][MeasurableSpace Ω]
variable {R:ReferenceData}{n:ℕ}(L:Level R P n)(δ:ℝ)(hδ:0<δ)
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)

def data (ε:ℝ≥0)(k:ℕ):LevelData (History P k) Ω (n+k):=
  OrdinaryModelLevelIto.data m (level L δ hδ ε k) (fun _ _ _=>0)
def leafMass (ν:Measure P)(ε:ℝ≥0)(k:ℕ):ℝ:=
  ∫z:History P k×Ω,(data L δ hδ m ε k).leaf z.1 z.2 ∂(historyMeasure R ν k).prod μ
def referenceMass (ν:Measure P)(ε:ℝ≥0)(k:ℕ):ℝ:=
  ∫z:History P k×Ω,(data L δ hδ m ε k).reference z.1 z.2 ∂(historyMeasure R ν k).prod μ
def remainderMass (ν:Measure P)(ε:ℝ≥0)(k:ℕ):ℝ:=
  ∫z:History P k×Ω,(data L δ hδ m ε k).remainder z.1 z.2 ∂(historyMeasure R ν k).prod μ

def RootConverges (ν:Measure P):Prop:=
  Tendsto (fun ε:ℝ=>∫z:History P 0×Ω,
    |RootJointHeatLeafLimit.leaf L δ hδ m.wordState m.wordState 0 ε.toNNReal 0 z.1 z.2-
      RootJointHeatLeafLimit.leaf L δ hδ m.wordState m.wordState 0 0 0 z.1 z.2|
      ∂(historyMeasure R ν 0).prod μ) (𝓝[>] (0:ℝ)) (𝓝 0)

theorem leaf_eq (ε:ℝ≥0)(k:ℕ)(p:History P k)(ω:Ω):
    (data L δ hδ m ε k).leaf p ω=
      RootJointHeatLeafLimit.leaf L δ hδ m.wordState m.wordState 0 ε k p ω:=by
  unfold RootJointHeatLeafLimit.leaf JointWordAnalytic.leaf
  rw [OrdinaryJointSelf.state]
  rfl

theorem reference_eq (ε:ℝ≥0)(k:ℕ)(p:History P k)(ω:Ω):
    (data L δ hδ m ε k).reference p ω=
      JointWordAnalytic.reference (level L δ hδ ε k) 0 m.physicalState m.physicalState
        m.physicalField m.physicalField p ω:=by
  rw [OrdinaryJointSelf.reference]
  rfl

theorem leafMass_tendsto (ν:Measure P)[IsFiniteMeasure ν]
    (hroot:RootConverges L δ hδ m ν)(k:ℕ):
    Tendsto (fun ε:ℝ=>leafMass L δ hδ m ν ε.toNNReal k) (𝓝[>] (0:ℝ))
      (𝓝 (leafMass L δ hδ m ν 0 k)):=by
  obtain ⟨C,_,hC⟩:=(test_uniform L δ hδ k).norm_bound
  have hi(ε:ℝ≥0):Integrable (fun z:History P k×Ω=>(data L δ hδ m ε k).leaf z.1 z.2)
      ((historyMeasure R ν k).prod μ):=
    (integrable_const C).mono'
      (physical_leaf_measurable (level L δ hδ ε k) m.physicalState_measurable
        m.physicalField_measurable (fun _ _ _=>0)).aestronglyMeasurable
      (ae_of_all _ (fun z=>hC (ε,z.1) _))
  have ht:Tendsto (fun ε:ℝ=>∫z:History P k×Ω,
      |(data L δ hδ m ε.toNNReal k).leaf z.1 z.2-(data L δ hδ m 0 k).leaf z.1 z.2|
        ∂(historyMeasure R ν k).prod μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    simp_rw [leaf_eq]
    exact RootJointHeatLeafLimit.integrated_leaf_difference_tendsto_zero L δ hδ m.wordState m.wordState 0 ν hroot k
  exact FiniteWordExpectation.integral_tendsto_of_abs ((historyMeasure R ν k).prod μ)
    (fun z:History P k×Ω=>(data L δ hδ m 0 k).leaf z.1 z.2)
    (fun ε:ℝ=>fun z:History P k×Ω=>(data L δ hδ m ε.toNNReal k).leaf z.1 z.2)
    (𝓝[>] (0:ℝ)) (hi 0) (fun ε:ℝ=>hi ε.toNNReal) ht

theorem referenceMass_tendsto (hstart:∀p,R.base<L.terminal p)
    (ν:Measure P)[IsFiniteMeasure ν](k:ℕ):
    Tendsto (fun ε:ℝ=>referenceMass L δ hδ m ν ε.toNNReal k) (𝓝[>] (0:ℝ))
      (𝓝 (referenceMass L δ hδ m ν 0 k)):=by
  obtain ⟨C,_,hC⟩:=(test_uniform L δ hδ k).norm_bound
  have hi(ε:ℝ≥0):Integrable (fun z:History P k×Ω=>(data L δ hδ m ε k).reference z.1 z.2)
      ((historyMeasure R ν k).prod μ):=
    (integrable_const C).mono'
      (physical_reference_measurable (level L δ hδ ε k) m.physicalState_measurable
        m.physicalField_measurable (fun _ _ _=>0)).aestronglyMeasurable
      (ae_of_all _ (fun z=>GaussianSmooth.average_norm_bound _ (hC (ε,z.1)) _))
  have ht:Tendsto (fun ε:ℝ=>∫z:History P k×Ω,
      |(data L δ hδ m ε.toNNReal k).reference z.1 z.2-(data L δ hδ m 0 k).reference z.1 z.2|
        ∂(historyMeasure R ν k).prod μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    simp_rw [reference_eq]
    exact RootJointReferenceLimit.integrated_reference_difference_tendsto_zero L δ hδ 0
      m.physicalState m.physicalState m.physicalField m.physicalField hstart
      m.physicalState_measurable m.physicalState_measurable m.physicalField_measurable m.physicalField_measurable ν μ k
  exact FiniteWordExpectation.integral_tendsto_of_abs ((historyMeasure R ν k).prod μ)
    (fun z:History P k×Ω=>(data L δ hδ m 0 k).reference z.1 z.2)
    (fun ε:ℝ=>fun z:History P k×Ω=>(data L δ hδ m ε.toNNReal k).reference z.1 z.2)
    (𝓝[>] (0:ℝ)) (hi 0) (fun ε:ℝ=>hi ε.toNNReal) ht

theorem remainderMass_tendsto (ν:Measure P)[IsFiniteMeasure ν](k:ℕ):
    Tendsto (fun ε:ℝ=>remainderMass L δ hδ m ν ε.toNNReal k) (𝓝[>] (0:ℝ))
      (𝓝 (remainderMass L δ hδ m ν 0 k)):=by
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have ha:Measurable (fun z=>κ+a z):=measurable_const.add m.variance_measurable
  have hA:0≤κ+M:=add_nonneg m.additive_pos.le hM
  have hb(z):|κ+a z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg m.additive_pos.le (m.lower_pos.le.trans (m.variance_bounds z).1))]
    exact add_le_add le_rfl (m.variance_bounds z).2
  obtain ⟨C,_,hC⟩:=ActualRootRemainder.uniform_remainder_bound L δ hδ (fun z=>κ+a z) hA hb
    m.physicalState m.physicalField k
  have hi(ε:ℝ≥0):Integrable (fun z:History P k×Ω=>(data L δ hδ m ε k).remainder z.1 z.2)
      ((historyMeasure R ν k).prod μ):=
    (integrable_const C).mono'
      (ActualVarianceLevel.remainder_measurable (level L δ hδ ε k) (fun z=>κ+a z) ha
        m.physicalState m.physicalState_measurable m.physicalField m.physicalField_measurable (fun _ _ _=>0)).aestronglyMeasurable
      (ae_of_all _ (fun z=>hC ε z.1 z.2))
  exact FiniteWordExpectation.integral_tendsto_of_abs _ _ _ _ (hi 0) (fun ε=>hi ε.toNNReal)
    (ActualRootRemainder.integrated_difference_tendsto_zero L δ hδ (fun z=>κ+a z) ha hA hb
      m.physicalState m.physicalField m.physicalState_measurable m.physicalField_measurable ν μ k)

/-- The rough actual bracket identity at the genuine zero root heat
age, before removal of the fixed recursive time cutoff. -/
theorem expected_zero_root_level (hlocal:StandardTerminalPastLocality m.scalarIto)
    (v:ℝ≥0)(hbase:R.base=(v:ℝ))(hh:R.horizon≤(H:ℝ))(hstart:∀p,R.base<L.terminal p)
    (ν:Measure P)[IsFiniteMeasure ν](hroot:RootConverges L δ hδ m ν)(k:ℕ):
    leafMass L δ hδ m ν 0 k=referenceMass L δ hδ m ν 0 k+remainderMass L δ hδ m ν 0 k:=by
  have he:∀ᶠε:ℝ in 𝓝[>] (0:ℝ),leafMass L δ hδ m ν ε.toNNReal k=
      referenceMass L δ hδ m ν ε.toNNReal k+remainderMass L δ hδ m ν ε.toNNReal k:=by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hecoe:(ε.toNNReal:ℝ)=ε:=Real.coe_toNNReal _ hε.le
    have hg:HeatCutoffHistories.Gap (level L δ hδ ε.toNNReal k) ε:=by
      intro p i
      exact hecoe.symm.le.trans (level_gap L δ hδ ε.toNNReal k p i)
    exact OrdinaryModelLevelIto.expected_level m (level L δ hδ ε.toNNReal k) hlocal v hbase hh
      (η:=ε) hε hg (historyMeasure R ν k)
  have ht:=((referenceMass_tendsto L δ hδ m hstart ν k).add
    (remainderMass_tendsto L δ hδ m ν k)).congr' (he.mono (fun _ h=>h.symm))
  exact tendsto_nhds_unique (leafMass_tendsto L δ hδ m ν hroot k) ht

end SHE.OrdinaryRootHeatLevel
