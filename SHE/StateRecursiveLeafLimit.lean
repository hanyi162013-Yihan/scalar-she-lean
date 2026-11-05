module

public import SHE.RecursiveLiteralChildLimit
public import SHE.StateRecursiveSpatialLimit
public import SHE.ProductIntegralCycle

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.StateRecursiveLeafLimit
open Set MeasureTheory AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RecursiveHeatBounds CutoffWordAnalytic PredictableWordState Filter Topology
open scoped NNReal ENNReal
local instance recursiveHeatLeafLimit_nativePeriod : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance recursiveHeatLeafLimit_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance recursiveHeatLeafLimit_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n) (δ : ℝ) (hδ : 0 < δ)
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {τ : Measure Ω} [IsProbabilityMeasure τ]
variable {h : ℝ≥0} (m : Data 𝓕 τ h)

def leaf (ε : ℝ≥0) (k : ℕ) (p : History P k) (ω : Ω) : ℝ :=
  (level L δ hδ ε k).test p (observe (fun t => m.physicalState (ω,t))
    (fun q => m.physicalField (ω,q)) ((level L δ hδ ε k).observations.observations p)
    ((level L δ hδ ε k).terminal p))

theorem leaf_succ (ε : ℝ≥0) (k : ℕ) (p : History P (k+1)) (ω : Ω) :
    leaf L δ hδ m ε (k+1) p ω=HeatCutoffStep.childLeaf (level L δ hδ ε k)
      δ ε m.physicalState m.physicalField p ω := rfl

theorem heatChild_zero_eq_literal (Q : CutoffWordLevel.Level R P n)
    (U : Ω × ℝ → CircleL2) (X : Ω × (ℝ × HeatCircle) → ℝ)
    (p : P × (ℝ × HeatCircle)) (ω : Ω) :
    HeatCutoffStep.childLeaf Q δ 0 U X p ω=CutoffWordStep.childLeaf Q δ U X p ω := by
  have hZ : (HeatCutoffHistories.Level.heatChildObservations Q 0).observations p=
      Q.childObservations.observations p := by
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    change Observation.mk (Q.nodeTime p) (Q.nodeTime p+0) p.2.2=
      Observation.mk (Q.nodeTime p) (Q.nodeTime p) p.2.2
    rw [add_zero]
  unfold HeatCutoffStep.childLeaf CutoffWordStep.childLeaf
  rw [hZ]

theorem leaf_measurable (ε : ℝ≥0) (k : ℕ) :
    Measurable (fun q : History P k × Ω => leaf L δ hδ m ε k q.1 q.2) :=
  physical_leaf_measurable _ m.physicalState_measurable m.physicalField_measurable (fun _ _ _ => 0)

theorem child_uniform (k : ℕ) : ∃ C : ℝ,0 ≤ C ∧ ∀ ε : ℝ≥0,∀ p ω,
    ‖HeatCutoffStep.childLeaf (level L δ hδ ε k) δ ε m.physicalState m.physicalField p ω‖ ≤ C ∧
    ‖CutoffWordStep.childLeaf (level L δ hδ ε k) δ m.physicalState m.physicalField p ω‖ ≤ C := by
  obtain ⟨C,hC,hCb⟩ := (test_uniform L δ hδ (k+1)).norm_bound
  exact ⟨C,hC,fun ε p ω => ⟨hCb (ε,p) _,hCb (ε,p) _⟩⟩

/-- Genuine product-measure rearrangement places the moving spatial
correction in the same complete history/sample space as the leaves. -/
theorem integrated_spatial_difference_tendsto_zero (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    Tendsto (fun ε : ℝ => ∫ q : History P (k+1) × Ω,
      |HeatCutoffStep.childLeaf (level L δ hδ ε.toNNReal k) δ ε m.physicalState m.physicalField q.1 q.2-
        CutoffWordStep.childLeaf (level L δ hδ ε.toNNReal k) δ m.physicalState m.physicalField q.1 q.2|
      ∂(historyMeasure R μ (k+1)).prod τ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have ht := StateRecursiveSpatialLimit.integrated_recursive_child_difference_tendsto_zero L m δ hδ μ k
  obtain ⟨C,hC,hCb⟩ := child_uniform L δ hδ m k
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have he : ((ε.toNNReal:ℝ≥0):ℝ)=ε := Real.coe_toNNReal _ hε.le
  let f : History P k → ℝ × HeatCircle → Ω → ℝ := fun p z ω =>
    |HeatCutoffStep.childLeaf (level L δ hδ ε.toNNReal k) δ ε m.physicalState m.physicalField (p,z) ω-
      CutoffWordStep.childLeaf (level L δ hδ ε.toNNReal k) δ m.physicalState m.physicalField (p,z) ω|
  have hm : Measurable (fun p : (History P k × (ℝ × HeatCircle)) × Ω => f p.1.1 p.1.2 p.2) :=
    ((HeatCutoffStep.childLeaf_measurable _ δ ε hδ hε.le m.physicalState m.physicalField
      m.physicalState_measurable m.physicalField_measurable).sub
      (CutoffWordStep.childLeaf_measurable _ δ hδ m.physicalState m.physicalField
        m.physicalState_measurable m.physicalField_measurable)).norm
  have hp : Measurable (fun q : (((History P k × Ω) × ℝ) × HeatCircle) =>
      ((q.1.1.1,(q.1.2,q.2)),q.1.1.2)) :=
    (measurable_fst.fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)).prodMk measurable_fst.fst.snd
  have hi : Integrable (fun q : (((History P k × Ω) × ℝ) × HeatCircle) =>
      f q.1.1.1 (q.1.2,q.2) q.1.1.2)
      ((((historyMeasure R μ k).prod τ).prod (volume.restrict (Ioc R.base R.horizon))).prod haarAddCircle) := by
    apply (integrable_const (2*C)).mono' (hm.comp hp).aestronglyMeasurable
    filter_upwards with q
    dsimp only [f,Function.comp_def,Prod.fst,Prod.snd]
    rw [Real.norm_eq_abs,abs_abs]
    have hh := (hCb ε.toNNReal (q.1.1.1,(q.1.2,q.2)) q.1.1.2).1
    rw [he] at hh
    exact (norm_sub_le _ _).trans
      ((add_le_add hh (hCb ε.toNNReal (q.1.1.1,(q.1.2,q.2)) q.1.1.2).2).trans_eq (by ring))
  exact (ProductIntegralCycle.integral_cycle_iterated (historyMeasure R μ k)
    (volume.restrict (Ioc R.base R.horizon)) haarAddCircle τ f hi).symm

/-- Actual heat-regularized recursive leaves converge to the literal
zero-age leaves in full finite-history/sample L¹, at every fixed depth
and fixed δ. No uniformity as δ→0 or depth→∞ is claimed. -/
theorem integrated_leaf_difference_tendsto_zero (μ : Measure P) [IsFiniteMeasure μ] (depth : ℕ) :
    Tendsto (fun ε : ℝ => ∫ q : History P depth × Ω,
      |leaf L δ hδ m ε.toNNReal depth q.1 q.2-leaf L δ hδ m 0 depth q.1 q.2|
      ∂(historyMeasure R μ depth).prod τ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  cases depth with
  | zero =>
    have he : (fun ε : ℝ => ∫ q : History P 0 × Ω,
        |leaf L δ hδ m ε.toNNReal 0 q.1 q.2-leaf L δ hδ m 0 0 q.1 q.2|
        ∂(historyMeasure R μ 0).prod τ)=fun _ => 0 := by
      funext ε
      simp only [leaf,level,HeatCutoffHistories.iterate,sub_self,abs_zero,integral_zero]
    rw [he]
    exact tendsto_const_nhds
  | succ k =>
    have hs := integrated_spatial_difference_tendsto_zero L δ hδ m μ k
    have hl := RecursiveLiteralChildLimit.integrated_literalChild_difference_tendsto_zero L δ hδ
      m.physicalState m.physicalField m.physicalState_measurable m.physicalField_measurable μ τ k
    have ht := hs.add hl
    simp only [add_zero] at ht
    apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _))) ?_ ht
    obtain ⟨C,hC,hCb⟩ := child_uniform L δ hδ m k
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have he : ((ε.toNNReal:ℝ≥0):ℝ)=ε := Real.coe_toNNReal _ hε.le
    let ν := (historyMeasure R μ (k+1)).prod τ
    let f := fun q : History P (k+1) × Ω =>
      |HeatCutoffStep.childLeaf (level L δ hδ ε.toNNReal k) δ ε m.physicalState m.physicalField q.1 q.2-
        CutoffWordStep.childLeaf (level L δ hδ ε.toNNReal k) δ m.physicalState m.physicalField q.1 q.2|
    let g := fun q : History P (k+1) × Ω =>
      |CutoffWordStep.childLeaf (level L δ hδ ε.toNNReal k) δ m.physicalState m.physicalField q.1 q.2-
        CutoffWordStep.childLeaf (level L δ hδ 0 k) δ m.physicalState m.physicalField q.1 q.2|
    have hfm : Measurable f :=
      ((HeatCutoffStep.childLeaf_measurable _ δ ε hδ hε.le m.physicalState m.physicalField
        m.physicalState_measurable m.physicalField_measurable).sub
        (CutoffWordStep.childLeaf_measurable _ δ hδ m.physicalState m.physicalField
          m.physicalState_measurable m.physicalField_measurable)).norm
    have hgm : Measurable g :=
      ((CutoffWordStep.childLeaf_measurable _ δ hδ m.physicalState m.physicalField
        m.physicalState_measurable m.physicalField_measurable).sub
        (CutoffWordStep.childLeaf_measurable _ δ hδ m.physicalState m.physicalField
          m.physicalState_measurable m.physicalField_measurable)).norm
    have hfi : Integrable f ν := by
      apply (integrable_const (2*C)).mono' hfm.aestronglyMeasurable
      filter_upwards with q
      rw [Real.norm_eq_abs,abs_abs]
      have hh := (hCb ε.toNNReal q.1 q.2).1
      rw [he] at hh
      exact (norm_sub_le _ _).trans ((add_le_add hh (hCb ε.toNNReal q.1 q.2).2).trans_eq (by ring))
    have hgi : Integrable g ν := by
      apply (integrable_const (2*C)).mono' hgm.aestronglyMeasurable
      filter_upwards with q
      rw [Real.norm_eq_abs,abs_abs]
      exact (norm_sub_le _ _).trans
        ((add_le_add (hCb ε.toNNReal q.1 q.2).2 (hCb 0 q.1 q.2).2).trans_eq (by ring))
    rw [← integral_add hfi hgi]
    apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _)) (hfi.add hgi)
    filter_upwards with q
    rw [leaf_succ,leaf_succ,he]
    simp only [NNReal.coe_zero]
    rw [heatChild_zero_eq_literal]
    exact abs_sub_le _ _ _

end SHE.StateRecursiveLeafLimit
