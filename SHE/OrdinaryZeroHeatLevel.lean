module
public import SHE.ActualRecursiveRemainder
public import SHE.OrdinaryModelLevelIto
public import SHE.StateZeroHeatWordExpectation
public import SHE.TwoChannelWordState

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.OrdinaryZeroHeatLevel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  RecursiveHeatBounds CutoffWordAnalytic IntegratedPhysicalStep CutoffReferenceTree Filter Topology
open scoped NNReal
local instance ordinaryZeroHeatLevel_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryZeroHeatLevel_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type*}[MeasurableSpace P][MeasurableSpace Ω]
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

theorem leafMass_tendsto (ν:Measure P)[IsFiniteMeasure ν](k:ℕ):
    Tendsto (fun ε:ℝ=>leafMass L δ hδ m ν ε.toNNReal k) (𝓝[>] (0:ℝ))
      (𝓝 (leafMass L δ hδ m ν 0 k)):=
  StateZeroHeatWordExpectation.leafMass_tendsto L δ hδ m.wordState ν k

theorem referenceMass_tendsto (ν:Measure P)[IsFiniteMeasure ν]
    {η:ℝ}(hη:0<η)(hgap:HeatCutoffHistories.Gap L η)(k:ℕ):
    Tendsto (fun ε:ℝ=>referenceMass L δ hδ m ν ε.toNNReal k) (𝓝[>] (0:ℝ))
      (𝓝 (referenceMass L δ hδ m ν 0 k)):=by
  obtain ⟨C,_,hC⟩:=(test_uniform L δ hδ k).norm_bound
  have hm(ε:ℝ≥0):Measurable (fun z:History P k×Ω=>(data L δ hδ m ε k).reference z.1 z.2):=
    physical_reference_measurable (level L δ hδ ε k) m.physicalState_measurable m.physicalField_measurable (fun _ _ _=>0)
  have hb(ε:ℝ≥0)(z:History P k×Ω):‖(data L δ hδ m ε k).reference z.1 z.2‖≤C:=
    GaussianSmooth.average_norm_bound _ (hC (ε,z.1)) _
  have hc(z:History P k×Ω):Continuous (fun ε:ℝ≥0=>(data L δ hδ m ε k).reference z.1 z.2):=by
    have he(ε:ℝ≥0):(data L δ hδ m ε k).reference z.1 z.2=
        deterministicReference (level L δ hδ ε k) (m.physicalState (z.2,R.base)) z.1:=
      physical_reference_eq (level L δ hδ ε k)
        (StateZeroHeatWordExpectation.regular_level L δ hδ hη hgap ε k)
        m.physicalState m.physicalField (fun _ _ _=>0) (m.physicalState (z.2,R.base)) z.2 rfl z.1
    simp_rw [he]
    exact RecursiveReferenceLimit.continuous_reference L δ hδ k z.1 _
  unfold referenceMass
  refine tendsto_integral_filter_of_dominated_convergence (fun _=>C) ?_ ?_ (integrable_const _) ?_
  · exact Filter.Eventually.of_forall (fun ε:ℝ=>(hm ε.toNNReal).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun ε:ℝ=>ae_of_all _ (hb ε.toNNReal))
  · exact ae_of_all _ (fun z=>by
      have hh:=((hc z).comp continuous_real_toNNReal).tendsto (0:ℝ)
      simpa only [Function.comp_def,Real.toNNReal_zero] using hh.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ))))

theorem remainderMass_tendsto (ν:Measure P)[IsFiniteMeasure ν](k:ℕ):
    Tendsto (fun ε:ℝ=>remainderMass L δ hδ m ν ε.toNNReal k) (𝓝[>] (0:ℝ))
      (𝓝 (remainderMass L δ hδ m ν 0 k)):=by
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have ha:Measurable (fun z=>κ+a z):=measurable_const.add m.variance_measurable
  have hA:0≤κ+M:=add_nonneg m.additive_pos.le hM
  have hb(z):|κ+a z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg m.additive_pos.le (m.lower_pos.le.trans (m.variance_bounds z).1))]
    exact add_le_add le_rfl (m.variance_bounds z).2
  obtain ⟨C,_,hC⟩:=ActualRecursiveRemainder.uniform_remainder_bound L δ hδ (fun z=>κ+a z) hA hb
    m.physicalState m.physicalField k
  have hi(ε:ℝ≥0):Integrable (fun z:History P k×Ω=>(data L δ hδ m ε k).remainder z.1 z.2)
      ((historyMeasure R ν k).prod μ):=
    (integrable_const C).mono'
      (ActualVarianceLevel.remainder_measurable (level L δ hδ ε k) (fun z=>κ+a z) ha
        m.physicalState m.physicalState_measurable m.physicalField m.physicalField_measurable (fun _ _ _=>0)).aestronglyMeasurable
      (ae_of_all _ (fun z=>hC ε z.1 z.2))
  exact FiniteWordExpectation.integral_tendsto_of_abs _ _ _ _ (hi 0) (fun ε=>hi ε.toNNReal)
    (ActualRecursiveRemainder.integrated_difference_tendsto_zero L δ hδ (fun z=>κ+a z) ha hA hb
      m.physicalState m.physicalField m.physicalState_measurable m.physicalField_measurable ν μ k)

/-- Spatial regularization is removed in the actual rough-bracket
level identity, without matching the actual and auxiliary coefficients. -/
theorem expected_zero_heat_level (hlocal:StandardTerminalPastLocality m.scalarIto)
    (v:ℝ≥0)(hbase:R.base=(v:ℝ))(hh:R.horizon≤(H:ℝ))
    (ν:Measure P)[IsFiniteMeasure ν]{η:ℝ}(hη:0<η)(hgap:HeatCutoffHistories.Gap L η)(k:ℕ):
    leafMass L δ hδ m ν 0 k=referenceMass L δ hδ m ν 0 k+remainderMass L δ hδ m ν 0 k:=by
  have he:∀ᶠε:ℝ in 𝓝[>] (0:ℝ),leafMass L δ hδ m ν ε.toNNReal k=
      referenceMass L δ hδ m ν ε.toNNReal k+remainderMass L δ hδ m ν ε.toNNReal k:=by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds] with ε hε hεη
    have hecoe:(ε.toNNReal:ℝ)=ε:=Real.coe_toNNReal _ hε.le
    have heg:HeatCutoffHistories.Gap L (ε.toNNReal:ℝ):=by
      intro p i
      rw [hecoe]
      exact hεη.le.trans (hgap p i)
    have hg:=HeatCutoffHistories.iterate_gap L hδ ε.toNNReal.2 heg k
    exact OrdinaryModelLevelIto.expected_level m (level L δ hδ ε.toNNReal k) hlocal v hbase hh (η:=(ε.toNNReal:ℝ))
      (by rw [hecoe];exact hε) hg (historyMeasure R ν k)
  have ht:=((referenceMass_tendsto L δ hδ m ν hη hgap k).add
    (remainderMass_tendsto L δ hδ m ν k)).congr' (he.mono (fun _ h=>h.symm))
  exact tendsto_nhds_unique (leafMass_tendsto L δ hδ m ν k) ht

end SHE.OrdinaryZeroHeatLevel
