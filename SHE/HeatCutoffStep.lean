module

public import SHE.HeatCutoffHistories
public import SHE.CutoffWordAnalytic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.HeatCutoffStep
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffWordAnalytic IntegratedPhysicalStep HeatCutoffHistories SmoothWords
open Classical
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n)
variable (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε)
variable (U : Ω × ℝ → CircleL2) (X : Ω × (ℝ × HeatCircle) → ℝ)

def childLeaf (p : P × (ℝ × HeatCircle)) (ω : Ω) : ℝ :=
  L.childTest δ p (observe (fun t => U (ω,t)) (fun q => X (ω,q))
    ((HeatCutoffHistories.Level.heatChildObservations L ε).observations p) (L.nodeTime p))

include hδ hε in
theorem childLeaf_measurable (hU : Measurable U) (hX : Measurable X) :
    Measurable (fun p : (P × (ℝ × HeatCircle)) × Ω => childLeaf L δ ε U X p.1 p.2) :=
  physical_leaf_measurable (HeatCutoffHistories.Level.heatExtend L δ ε hδ hε) hU hX (fun _ _ _ => 0)

include hδ in
theorem childLeaf_uniform_bound : ∃ C : ℝ,0 ≤ C ∧ ∀ p ω,‖childLeaf L δ ε U X p ω‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := (L.childTest_uniform hδ).norm_bound
  exact ⟨C,hC,fun p ω => hb p _⟩

/-- This exact correction contains both the discarded time strip δ
and the spatial regularization ε; neither is silently removed. -/
def correction (p : P) (ω : Ω) : ℝ :=
  PhysicalIto.wordRemainder (L.window p) R.totalVariance (fun t => U (ω,t))
    (fun q => X (ω,q)) (L.test p)-∫ z,childLeaf L δ ε U X (p,z) ω ∂nodeMeasure R

include hδ hε in
theorem correction_measurable (hU : Measurable U) (hX : Measurable X) :
    Measurable (fun p : P × Ω => correction L δ ε U X p.1 p.2) := by
  have hc : Measurable (fun p : (P × Ω) × (ℝ × HeatCircle) => childLeaf L δ ε U X (p.1.1,p.2) p.1.2) :=
    (childLeaf_measurable L δ ε hδ hε U X hU hX).comp
      ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  have hi := hc.stronglyMeasurable.integral_prod_right' (ν := nodeMeasure R)
  exact (physical_remainder_measurable L hU hX (fun _ _ _ => 0)).sub hi.measurable

/-- The difference from the literal zero-age insertion is exactly a
scalar coefficient error, with the same old observations and Gaussian
Hessian. Thus the common-window covariance is never replaced. -/
theorem childLeaf_sub_literal (hεp : 0 < ε) (p : P × (ℝ × HeatCircle)) (ω : Ω) :
    childLeaf L δ ε U X p ω-CutoffWordStep.childLeaf L δ U X p ω =
      (1/2:ℝ)*(R.totalVariance (PhysicalProfile.physicalHeatMean (U (ω,L.nodeTime p)) (ε,p.2.2))-
        R.totalVariance (X (ω,(L.nodeTime p,p.2.2))))*
      directionalSecond (L.averagedTest p)
        (observe (fun t => U (ω,t)) (fun q => X (ω,q)) (L.observations.observations p.1) (L.nodeTime p))
        (L.cutoffRow δ p) := by
  have htail : tailProjection n (observe (fun t => U (ω,t)) (fun q => X (ω,q))
      (L.childObservations.observations p) (L.nodeTime p))=
      observe (fun t => U (ω,t)) (fun q => X (ω,q)) (L.observations.observations p.1) (L.nodeTime p) := by
    ext i
    rfl
  have hhead : observe (fun t => U (ω,t)) (fun q => X (ω,q))
      (L.childObservations.observations p) (L.nodeTime p) 0=X (ω,(L.nodeTime p,p.2.2)) :=
    observe_append_zero _ _ _ _ _
  unfold childLeaf CutoffWordStep.childLeaf CutoffWordLevel.Level.childTest CutoffInsertionCore.core
  rw [HeatCutoffHistories.Level.heatChild_head L ε hεp,
    HeatCutoffHistories.Level.heatChild_tail L ε,htail,hhead]
  ring

include hδ hε in
theorem integrated_recursive_step (hU : Measurable U) (hX : Measurable X)
    (N : P → (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ)
    (μ : Measure P) [IsFiniteMeasure μ] (τ : Measure Ω) [IsProbabilityMeasure τ]
    (hIto : ItoConditions (physicalLevel L U X N) τ) :
    Integrable ((physicalLevel L U X N).integratedNoise μ) τ ∧
      (∫ ω,(physicalLevel L U X N).integratedNoise μ ω ∂τ)=0 ∧
      ∀ ω,(∫ p,(physicalLevel L U X N).leaf p ω ∂μ)=
        (∫ p,(physicalLevel L U X N).reference p ω ∂μ)+
          (physicalLevel L U X N).integratedNoise μ ω+
          (∫ p,childLeaf L δ ε U X p ω ∂μ.prod (nodeMeasure R))+
          ∫ p,correction L δ ε U X p ω ∂μ := by
  have hA := physical_analyticConditions L hU hX N
  obtain ⟨hNi,hNz,hNe,hstep⟩ := integrated_level (physicalLevel L U X N) hA μ τ hIto
  obtain ⟨K,hKn,hK⟩ := uniform_level_bound (physicalLevel L U X N) hA
  obtain ⟨C,hCn,hC⟩ := childLeaf_uniform_bound L δ ε hδ U X
  refine ⟨hNi,hNz,fun ω => ?_⟩
  have hm := (childLeaf_measurable L δ ε hδ hε U X hU hX).comp
    (measurable_id.prodMk (measurable_const (a := ω)))
  have hi : Integrable (fun p : P × (ℝ × HeatCircle) => childLeaf L δ ε U X p ω)
      (μ.prod (nodeMeasure R)) :=
    (integrable_const C).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun p => hC p ω))
  have hr : Integrable (fun p => (physicalLevel L U X N).remainder p ω) μ :=
    (integrable_const K).mono'
      (hA.remainder_measurable.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => (hK p ω).2.2.1))
  have he := integral_sub hr hi.integral_prod_left
  change (∫ p,correction L δ ε U X p ω ∂μ)=_ at he
  rw [← integral_prod _ hi] at he
  linarith only [hstep ω,he]

end SHE.HeatCutoffStep
