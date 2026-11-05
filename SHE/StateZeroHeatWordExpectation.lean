module

public import SHE.StateRecursiveLeafLimit
public import SHE.RecursiveReferenceLimit
public import SHE.RecursiveRemainderConvergence
public import SHE.FiniteWordExpectation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.StateZeroHeatWordExpectation
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RecursiveHeatBounds CutoffWordAnalytic PredictableWordState CutoffReferenceTree
open IntegratedPhysicalStep FiniteWordExpectation RecursiveRemainderConvergence
open Filter Topology
open scoped NNReal
local instance zeroHeatWordExpectation_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance zeroHeatWordExpectation_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n) (δ : ℝ) (hδ : 0 < δ)
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {τ : Measure Ω} [IsProbabilityMeasure τ]
variable {h : ℝ≥0} (m : Data 𝓕 τ h)

theorem regular_level {η : ℝ} (hη : 0 < η) (hgap : HeatCutoffHistories.Gap L η)
    (ε : ℝ≥0) (k : ℕ) : RegularAtBase (level L δ hδ ε k) := by
  classical
  intro p
  cases k with
  | zero =>
    left
    intro i
    have hh := hgap p i
    have hb := L.terminal_base p
    change R.base<(L.observations.observations p i).target
    linarith
  | succ k =>
    change History P k × (ℝ × HeatCircle) at p
    by_cases hp : (level L δ hδ ε k).Good δ p
    · left
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change R.base<(level L δ hδ ε k).nodeTime p+(ε:ℝ)
        rw [(level L δ hδ ε k).nodeTime_eq hδ hp]
        linarith [hp.1,ε.2]
      · change R.base<((level L δ hδ ε k).observations.observations p.1 j).target
        exact ((level L δ hδ ε k).good_time hδ hp).1.trans
          (((level L δ hδ ε k).good_time hδ hp).2.trans_le ((level L δ hδ ε k).targets_after p.1 j))
    · right
      change (level L δ hδ ε k).childTest δ p=0
      rw [CutoffWordLevel.Level.childTest_eq _ hδ p]
      exact if_neg hp

def leafMass (μ : Measure P) (ε : ℝ≥0) (k : ℕ) : ℝ :=
  ∫ q : History P k × Ω,StateRecursiveLeafLimit.leaf L δ hδ m ε k q.1 q.2
    ∂(historyMeasure R μ k).prod τ
def referenceMass (μ : Measure P) (u : CircleL2) (ε : ℝ≥0) (k : ℕ) : ℝ :=
  ∫ p : History P k,deterministicReference (level L δ hδ ε k) u p ∂historyMeasure R μ k
def remainderMass (μ : Measure P) (ε : ℝ≥0) (k : ℕ) : ℝ :=
  ∫ q : History P k × Ω,remainder L δ hδ m.physicalState m.physicalField ε k q.1 q.2
    ∂(historyMeasure R μ k).prod τ

theorem leafMass_tendsto (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    Tendsto (fun ε : ℝ => leafMass L δ hδ m μ ε.toNNReal k) (𝓝[>] (0:ℝ))
      (𝓝 (leafMass L δ hδ m μ 0 k)) := by
  obtain ⟨C,_,hC⟩ := (test_uniform L δ hδ k).norm_bound
  have hi (ε : ℝ≥0) : Integrable (fun q : History P k × Ω =>
      StateRecursiveLeafLimit.leaf L δ hδ m ε k q.1 q.2) ((historyMeasure R μ k).prod τ) :=
    (integrable_const C).mono' (StateRecursiveLeafLimit.leaf_measurable L δ hδ m ε k).aestronglyMeasurable
      (Eventually.of_forall (fun q => hC (ε,q.1) _))
  exact integral_tendsto_of_abs _ _ _ _ (hi 0) (fun ε => hi ε.toNNReal)
    (StateRecursiveLeafLimit.integrated_leaf_difference_tendsto_zero L δ hδ m μ k)

theorem referenceMass_tendsto (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) (u : CircleL2) :
    Tendsto (fun ε : ℝ => referenceMass L δ hδ μ u ε.toNNReal k) (𝓝[>] (0:ℝ))
      (𝓝 (referenceMass L δ hδ μ u 0 k)) := by
  obtain ⟨C,_,hC⟩ := (test_uniform L δ hδ k).norm_bound
  have hi (ε : ℝ≥0) : Integrable (deterministicReference (level L δ hδ ε k) u) (historyMeasure R μ k) := by
    apply (integrable_const C).mono' (deterministicReference_measurable _ u).aestronglyMeasurable
    filter_upwards with p
    rw [RecursiveReferenceLimit.reference_eq_average]
    exact GaussianSmooth.average_norm_bound _ (hC (ε,p)) _
  exact integral_tendsto_of_abs _ _ _ _ (hi 0) (fun ε => hi ε.toNNReal)
    (RecursiveReferenceLimit.integrated_reference_difference_tendsto_zero L δ hδ μ k u)

theorem remainderMass_tendsto (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    Tendsto (fun ε : ℝ => remainderMass L δ hδ m μ ε.toNNReal k) (𝓝[>] (0:ℝ))
      (𝓝 (remainderMass L δ hδ m μ 0 k)) := by
  obtain ⟨C,_,hC⟩ := uniform_remainder_bound L δ hδ m.physicalState m.physicalField k
  have hi (ε : ℝ≥0) : Integrable (fun q : History P k × Ω =>
      remainder L δ hδ m.physicalState m.physicalField ε k q.1 q.2) ((historyMeasure R μ k).prod τ) :=
    (integrable_const C).mono'
      (physical_remainder_measurable (level L δ hδ ε k) m.physicalState_measurable
        m.physicalField_measurable (fun _ _ _ => 0)).aestronglyMeasurable
      (Eventually.of_forall (fun q => hC ε q.1 q.2))
  exact integral_tendsto_of_abs _ _ _ _ (hi 0) (fun ε => hi ε.toNNReal)
    (integrated_remainder_difference_tendsto_zero L δ hδ m.physicalState m.physicalField
      m.physicalState_measurable m.physicalField_measurable μ τ k)

/-- The physical expected word identity after genuinely removing spatial
heat regularization at every fixed recursive depth. Its original zero-age
observations use the chosen joint scalar field. No zero-age Itô formula
or pointwise natural-version compatibility is assumed. -/
theorem expected_zero_heat_level
    (hIto : ∀ (ε : ℝ≥0),0<(ε:ℝ) → ∀ k : ℕ,
      HeatCutoffHistories.Gap (level L δ hδ ε k) (ε:ℝ) →
      ∃ N, ItoConditions (physicalLevel (level L δ hδ ε k) m.physicalState m.physicalField N) τ)
    (μ : Measure P) [IsFiniteMeasure μ]
    {η : ℝ} (hη : 0 < η) (hgap : HeatCutoffHistories.Gap L η)
    (hh : R.horizon ≤ (h:ℝ)) (k : ℕ) (u : CircleL2)
    (hu : ∀ᵐ ω ∂τ,m.physicalState (ω,R.base)=u) :
    leafMass L δ hδ m μ 0 k=referenceMass L δ hδ μ u 0 k+remainderMass L δ hδ m μ 0 k := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      leafMass L δ hδ m μ ε.toNNReal k=
        referenceMass L δ hδ μ u ε.toNNReal k+remainderMass L δ hδ m μ ε.toNNReal k := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds] with ε hε hεη
    have hecoe : ((ε.toNNReal:ℝ≥0):ℝ)=ε := Real.coe_toNNReal _ hε.le
    have heg : HeatCutoffHistories.Gap L (ε.toNNReal:ℝ) := by
      intro p i
      rw [hecoe]
      exact hεη.le.trans (hgap p i)
    have hge : HeatCutoffHistories.Gap (level L δ hδ ε.toNNReal k) (ε.toNNReal:ℝ) :=
      HeatCutoffHistories.iterate_gap L hδ ε.toNNReal.2 heg k
    obtain ⟨N,hN⟩ := hIto ε.toNNReal (by rw [hecoe]; exact hε) k hge
    let D := physicalLevel (level L δ hδ ε.toNNReal k) m.physicalState m.physicalField N
    have hD := physical_analyticConditions (level L δ hδ ε.toNNReal k)
      m.physicalState_measurable m.physicalField_measurable N
    have hi := expected_level D hD (historyMeasure R μ k) τ hN
    obtain ⟨K,_,hK⟩ := uniform_level_bound D hD
    have hQi : Integrable (fun q : History P k × Ω => D.reference q.1 q.2) ((historyMeasure R μ k).prod τ) :=
      (integrable_const K).mono' hD.reference_measurable.aestronglyMeasurable
        (Eventually.of_forall (fun q => (hK q.1 q.2).2.1))
    have hQ : (∫ q : History P k × Ω,D.reference q.1 q.2 ∂(historyMeasure R μ k).prod τ)=
        referenceMass L δ hδ μ u ε.toNNReal k := by
      rw [integral_prod _ hQi]
      apply integral_congr_ae
      filter_upwards with p
      have hpe := hu.mono (fun ω hω => physical_reference_eq (level L δ hδ ε.toNNReal k)
        (regular_level L δ hδ hη hgap ε.toNNReal k) m.physicalState m.physicalField N u ω hω p)
      rw [integral_congr_ae hpe]
      simp only [integral_const,probReal_univ,one_smul]
    rw [hQ] at hi
    exact hi
  have ht := (referenceMass_tendsto L δ hδ μ k u).add (remainderMass_tendsto L δ hδ m μ k)
  have he' : (fun ε : ℝ => leafMass L δ hδ m μ ε.toNNReal k)=ᶠ[𝓝[>] (0:ℝ)]
      (fun ε => referenceMass L δ hδ μ u ε.toNNReal k+remainderMass L δ hδ m μ ε.toNNReal k) := he
  exact tendsto_nhds_unique (leafMass_tendsto L δ hδ m μ k) (ht.congr' he'.symm)

end SHE.StateZeroHeatWordExpectation
