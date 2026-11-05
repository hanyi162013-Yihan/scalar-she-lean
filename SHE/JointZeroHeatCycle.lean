module

public import SHE.JointHeatLeafLimit
public import SHE.JointRecursiveRemainderConvergence
public import SHE.NodeIntegralCycle

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.JointZeroHeatCycle
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RecursiveHeatBounds CutoffWordAnalytic
open JointRecursiveRemainderConvergence Filter Topology
open scoped NNReal
local instance jointZeroHeatCycle_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance jointZeroHeatCycle_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n) (δ : ℝ) (hδ : 0 < δ)
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {τ : Measure Ω} [IsProbabilityMeasure τ]
variable {h : ℝ≥0} (dU dV : PredictableWordState.Data 𝓕 τ h) (Λ : ℝ)

def leafMass (μ : Measure P) (ε : ℝ≥0) (k : ℕ) : ℝ :=
  ∫ q : History P k×Ω,JointHeatLeafLimit.leaf L δ hδ dU dV Λ ε k q.1 q.2
    ∂(historyMeasure R μ k).prod τ

def remainderMass (μ : Measure P) (ε : ℝ≥0) (k : ℕ) : ℝ :=
  ∫ q : History P k×Ω,JointRecursiveRemainderConvergence.remainder L δ hδ Λ
    dU.physicalState dV.physicalState dU.physicalField dV.physicalField ε k q.1 q.2
    ∂(historyMeasure R μ k).prod τ

def correctionMass (μ : Measure P) (k : ℕ) : ℝ :=
  ∫ q : History P k × Ω,JointCutoffStep.correction (level L δ hδ 0 k) Λ δ dU.physicalState dV.physicalState dU.physicalField dV.physicalField q.1 q.2 ∂(historyMeasure R μ k).prod τ

theorem child_mass_eq (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    (∫ q : History P k × Ω,∫ z,JointCutoffStep.childLeaf (level L δ hδ 0 k) Λ δ dU.physicalState dV.physicalState dU.physicalField dV.physicalField (q.1,z) q.2 ∂nodeMeasure R ∂(historyMeasure R μ k).prod τ)=
      leafMass L δ hδ dU dV Λ μ 0 (k+1) := by
  obtain ⟨C,_,hC⟩ := (test_uniform L δ hδ (k+1)).norm_bound
  let f := fun p : History P k => fun z : ℝ × HeatCircle => fun ω : Ω =>
    JointCutoffStep.childLeaf (level L δ hδ 0 k) Λ δ dU.physicalState dV.physicalState dU.physicalField dV.physicalField (p,z) ω
  have hp : Measurable (fun q : (History P k × Ω) × (ℝ × HeatCircle) => ((q.1.1,q.2),q.1.2)) :=
    (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  have hm := (JointCutoffStep.childLeaf_measurable (level L δ hδ 0 k) Λ δ dU.physicalState_measurable dV.physicalState_measurable dU.physicalField_measurable dV.physicalField_measurable hδ).comp hp
  have hi : Integrable (fun q : (History P k × Ω) × (ℝ × HeatCircle) => f q.1.1 q.2 q.1.2)
      (((historyMeasure R μ k).prod τ).prod (nodeMeasure R)) :=
    (integrable_const C).mono' hm.aestronglyMeasurable (Eventually.of_forall (fun q => hC (0,(q.1.1,q.2)) _))
  have he := NodeIntegralCycle.integral_cycle_iterated (historyMeasure R μ k) (nodeMeasure R) τ f hi
  calc
    _ = ∫ q : History P (k+1) × Ω,f q.1.1 q.1.2 q.2 ∂(historyMeasure R μ (k+1)).prod τ := he.symm
    _ = leafMass L δ hδ dU dV Λ μ 0 (k+1) := by
      apply integral_congr_ae
      filter_upwards with q
      rw [JointHeatLeafLimit.leaf_succ]
      simp only [NNReal.coe_zero]
      exact (JointHeatLeafLimit.heatChild_zero_eq_literal δ Λ _ dU.physicalState dV.physicalState dU.physicalField dV.physicalField q.1 q.2).symm

theorem correctionMass_eq (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    correctionMass L δ hδ dU dV Λ μ k=remainderMass L δ hδ dU dV Λ μ 0 k-leafMass L δ hδ dU dV Λ μ 0 (k+1) := by
  obtain ⟨C,_,hC⟩ := (test_uniform L δ hδ (k+1)).norm_bound
  have hp : Measurable (fun q : (History P k × Ω) × (ℝ × HeatCircle) => ((q.1.1,q.2),q.1.2)) :=
    (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  have hm := (JointCutoffStep.childLeaf_measurable (level L δ hδ 0 k) Λ δ dU.physicalState_measurable dV.physicalState_measurable dU.physicalField_measurable dV.physicalField_measurable hδ).comp hp
  have hi : Integrable (fun q : (History P k × Ω) × (ℝ × HeatCircle) =>
      JointCutoffStep.childLeaf (level L δ hδ 0 k) Λ δ dU.physicalState dV.physicalState dU.physicalField dV.physicalField (q.1.1,q.2) q.1.2)
      (((historyMeasure R μ k).prod τ).prod (nodeMeasure R)) :=
    (integrable_const C).mono' hm.aestronglyMeasurable (Eventually.of_forall (fun q => hC (0,(q.1.1,q.2)) _))
  obtain ⟨B,_,hB⟩ := uniform_remainder_bound L δ hδ Λ dU.physicalState dV.physicalState dU.physicalField dV.physicalField k
  have hr : Integrable (fun q : History P k × Ω => remainder L δ hδ Λ dU.physicalState dV.physicalState dU.physicalField dV.physicalField 0 k q.1 q.2)
      ((historyMeasure R μ k).prod τ) :=
    (integrable_const B).mono'
      (JointWordAnalytic.remainder_measurable (level L δ hδ 0 k) Λ dU.physicalState_measurable dV.physicalState_measurable dU.physicalField_measurable dV.physicalField_measurable).aestronglyMeasurable
      (Eventually.of_forall (fun q => hB 0 q.1 q.2))
  have he := integral_sub hr hi.integral_prod_left
  simp only [Pi.sub_apply] at he
  change (∫ q : History P k × Ω,remainder L δ hδ Λ dU.physicalState dV.physicalState dU.physicalField dV.physicalField 0 k q.1 q.2-
    ∫ z,JointCutoffStep.childLeaf (level L δ hδ 0 k) Λ δ dU.physicalState dV.physicalState dU.physicalField dV.physicalField (q.1,z) q.2 ∂nodeMeasure R
      ∂(historyMeasure R μ k).prod τ)=_
  rw [he,child_mass_eq]
  rfl

end SHE.JointZeroHeatCycle
