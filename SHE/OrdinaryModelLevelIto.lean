module
public import SHE.OrdinaryModelPastIto
public import SHE.FiniteWordExpectation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryModelLevelIto
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation NativeObservationNaturality WordRecursion OrthogonalItoChannels
  CutoffWordLevel IntegratedPhysicalStep
open scoped NNReal ENNReal
local instance ordinaryModelLevelIto_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryModelLevelIto_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryModelLevelIto_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryModelLevelIto_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω X:Type*}[MeasurableSpace Ω][MeasurableSpace X]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}
variable (m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R X n)

def data (N:X→(ℝ→WordRecursion.State n→ℝ)→Ω→ℝ):LevelData X Ω n:=
  ActualVarianceLevel.data L (fun z=>κ+a z) m.physicalState m.physicalField N

/-- Actual rough-bracket applicability for an arbitrary smooth
reference word. The reference total variance need not equal κ+a. -/
theorem exists_level_ito (hlocal:StandardTerminalPastLocality m.scalarIto)
    (v:ℝ≥0)(hbase:R.base=(v:ℝ))(hh:R.horizon≤(H:ℝ))
    {η:ℝ}(hη:0<η)(hgap:∀p i,η≤(L.observations.observations p i).target-L.terminal p):
    ∃N:X→(ℝ→WordRecursion.State n→ℝ)→Ω→ℝ,
      ItoConditions (data m L N) μ ∧
      (∀p G A,MeasurableSet[𝓕 v] A→(∫ω in A,N p G ω ∂μ)=0):=by
  have hex(p:X):∃N:(ℝ→WordRecursion.State n→ℝ)→Ω→ℝ,
      (∀G,Integrable (N G) μ∧∀A,MeasurableSet[𝓕 v] A→(∫ω in A,N G ω ∂μ)=0)∧
      PhysicalIto.FiniteItoInput μ
        (fun ω=>observe (fun t=>m.physicalState (ω,t)) (fun q=>m.physicalField (ω,q)) (L.observations.observations p))
        (fun ω t=>CovarianceMatrix.densityMatrix (fun q=>κ+a (m.physicalField (ω,q)))
          (L.observations.observations p) t) R.base (L.terminal p) N:=by
    let b:ℝ≥0:=(L.terminal p).toNNReal
    have hb0:0≤L.terminal p:=R.base_nonneg.trans (L.terminal_base p)
    have hbcoe:(b:ℝ)=L.terminal p:=Real.coe_toNNReal _ hb0
    have hb:b≤H:=by exact_mod_cast (show (b:ℝ)≤H by rw [hbcoe];exact (L.terminal_horizon p).trans hh)
    have hvb:v≤b:=by exact_mod_cast (show (v:ℝ)≤(b:ℝ) by rw [←hbase,hbcoe];exact L.terminal_base p)
    have hg:∀i,η≤(L.observations.observations p i).target-(b:ℝ):=by simpa only [hbcoe] using hgap p
    have hi:=OrdinaryModelPastIto.finiteItoInput m hlocal (L.observations.observations p) b hb hη hg v hvb
    rw [hbcoe,←hbase] at hi
    exact hi
  choose N hN using hex
  refine ⟨N,⟨?_,?_,?_⟩,?_⟩
  · intro p
    exact ae_of_all _ (PredictableScalarField.wordField_section_measurable 𝓕 m.state_predictable)
  · intro p
    exact (hN p).2
  · intro p
    change (∫ω,N p (GaussianItoTest.backward (L.window p) (L.test p)) ω ∂μ)=0
    simpa only [Measure.restrict_univ] using
      ((hN p).1 (GaussianItoTest.backward (L.window p) (L.test p))).2 Set.univ MeasurableSet.univ
  · intro p G A hA
    exact ((hN p).1 G).2 A hA

/-- The actual ordinary-U expected level, with its original rough
bracket remainder and arbitrary smooth auxiliary reference. -/
theorem expected_level (hlocal:StandardTerminalPastLocality m.scalarIto)
    (v:ℝ≥0)(hbase:R.base=(v:ℝ))(hh:R.horizon≤(H:ℝ))
    {η:ℝ}(hη:0<η)(hgap:∀p i,η≤(L.observations.observations p i).target-L.terminal p)
    (ν:Measure X)[IsFiniteMeasure ν]:
    (∫z:X×Ω,(data m L (fun _ _ _=>0)).leaf z.1 z.2 ∂ν.prod μ)=
      (∫z:X×Ω,(data m L (fun _ _ _=>0)).reference z.1 z.2 ∂ν.prod μ)+
      ∫z:X×Ω,(data m L (fun _ _ _=>0)).remainder z.1 z.2 ∂ν.prod μ:=by
  obtain ⟨N,hIto,hNc⟩:=exists_level_ito m L hlocal v hbase hh hη hgap
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have ha:Measurable (fun z=>κ+a z):=measurable_const.add m.variance_measurable
  have hcap(z):|κ+a z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg m.additive_pos.le (m.lower_pos.le.trans (m.variance_bounds z).1))]
    exact add_le_add le_rfl (m.variance_bounds z).2
  have hD:=ActualVarianceLevel.analyticConditions L (fun z=>κ+a z) ha m.physicalState
    m.physicalState_measurable m.physicalField m.physicalField_measurable N
    (add_nonneg m.additive_pos.le hM) hcap
  exact FiniteWordExpectation.expected_level (data m L N) hD ν μ hIto

end SHE.OrdinaryModelLevelIto
