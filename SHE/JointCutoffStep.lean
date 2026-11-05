module

public import SHE.JointInsertionIntegrability
public import SHE.JointWordObserveHeat
public import SHE.CutoffWordStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.JointCutoffStep
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open JointWordAnalytic GaussianItoTest
open Classical
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n) (Λ δ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

def childLeaf (p : P×(ℝ×HeatCircle)) (ω : Ω) : ℝ := L.childTest δ p
  (JointWordObserve.evaluate Λ (fun t => U (ω,t)) (fun t => V (ω,t))
    (fun tx => XU (ω,tx)) (fun tx => XV (ω,tx)) (L.childObservations.observations p) (L.nodeTime p))

def heatChildLeaf (ε : ℝ) (p : P×(ℝ×HeatCircle)) (ω : Ω) : ℝ := L.childTest δ p
  (JointWordObserve.evaluate Λ (fun t => U (ω,t)) (fun t => V (ω,t))
    (fun tx => XU (ω,tx)) (fun tx => XV (ω,tx))
    ((HeatCutoffHistories.Level.heatChildObservations L ε).observations p) (L.nodeTime p))

def correction (p : P) (ω : Ω) : ℝ := remainder L Λ U V XU XV p ω-
  ∫ z,childLeaf L Λ δ U V XU XV (p,z) ω ∂nodeMeasure R

def heatCorrection (ε : ℝ) (p : P) (ω : Ω) : ℝ := remainder L Λ U V XU XV p ω-
  ∫ z,heatChildLeaf L Λ δ U V XU XV ε (p,z) ω ∂nodeMeasure R

variable {U V XU XV}
variable (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)

include hU hV hXU hXV in
theorem childLeaf_measurable (hδ : 0<δ) :
    Measurable (fun p : (P×(ℝ×HeatCircle))×Ω => childLeaf L Λ δ U V XU XV p.1 p.2) :=
  JointWordAnalytic.leaf_measurable (L.extend δ hδ) Λ hU hV hXU hXV

include hU hV hXU hXV in
theorem heatChildLeaf_measurable (hδ : 0<δ) {ε : ℝ} (hε : 0≤ε) :
    Measurable (fun p : (P×(ℝ×HeatCircle))×Ω => heatChildLeaf L Λ δ U V XU XV ε p.1 p.2) :=
  JointWordAnalytic.leaf_measurable (HeatCutoffHistories.Level.heatExtend L δ ε hδ hε) Λ hU hV hXU hXV

theorem childLeaf_uniform_bound (hδ : 0<δ) : ∃ K : ℝ,0≤K ∧ ∀ p ω,‖childLeaf L Λ δ U V XU XV p ω‖≤K := by
  obtain ⟨K,hKn,hK⟩ := (L.childTest_uniform hδ).norm_bound
  exact ⟨K,hKn,fun p ω => hK p _⟩

theorem heatChildLeaf_uniform_bound (hδ : 0<δ) (ε : ℝ) : ∃ K : ℝ,0≤K ∧ ∀ p ω,‖heatChildLeaf L Λ δ U V XU XV ε p ω‖≤K := by
  obtain ⟨K,hKn,hK⟩ := (L.childTest_uniform hδ).norm_bound
  exact ⟨K,hKn,fun p ω => hK p _⟩

/-- Only the scalar local coefficient is expanded at the appended V
point. All old actual joint coordinates are retained without freezing. -/
theorem childLeaf_eq (hδ : 0<δ) (p : P×(ℝ×HeatCircle)) (ω : Ω) :
    childLeaf L Λ δ U V XU XV p ω=if L.Good δ p then insertion L Λ U V XU XV p.1 ω p.2.1 p.2.2 else 0 := by
  unfold childLeaf
  rw [L.childTest_eq hδ p]
  by_cases hp : L.Good δ p
  · simp only [hp,ite_true]
    have ht := L.nodeTime_eq hδ hp
    change WordRecursion.insertion R.totalVariance R.reference (L.observations.observations p.1) p.2.1 p.2.2
      (gaussianSemigroup R.reference (L.observations.observations p.1) p.2.1 (L.terminal p.1) (L.test p.1))
      (JointWordObserve.evaluate Λ _ _ _ _ (appendObservation _ (L.nodeTime p) p.2.2) (L.nodeTime p))=_
    rw [ht,JointWordObserve.evaluate_append]
    rw [JointWordAnalytic.insertion,PhysicalIto.backward_eq_semigroup (L.window p.1) (L.test p.1)
      (Ioo_subset_Icc_self (L.good_time hδ hp))]
    rfl
  · simp only [hp,ite_false,Pi.zero_apply]

include hU hV hXU hXV in
theorem correction_measurable (hδ : 0<δ) :
    Measurable (fun p : P×Ω => correction L Λ δ U V XU XV p.1 p.2) := by
  have hc := (childLeaf_measurable L Λ δ hU hV hXU hXV hδ).comp
    ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  have hm := hc.stronglyMeasurable.integral_prod_right' (ν := nodeMeasure R)
  exact (remainder_measurable L Λ hU hV hXU hXV).sub hm.measurable

include hU hV hXU hXV in
theorem heatCorrection_measurable (hδ : 0<δ) {ε : ℝ} (hε : 0≤ε) :
    Measurable (fun p : P×Ω => heatCorrection L Λ δ U V XU XV ε p.1 p.2) := by
  have hc := (heatChildLeaf_measurable L Λ δ hU hV hXU hXV hδ hε).comp
    ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  have hm := hc.stronglyMeasurable.integral_prod_right' (ν := nodeMeasure R)
  exact (remainder_measurable L Λ hU hV hXU hXV).sub hm.measurable

end SHE.JointCutoffStep
