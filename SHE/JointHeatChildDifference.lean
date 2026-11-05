module

public import SHE.JointCutoffStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.JointHeatChildDifference
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open JointWordAnalytic GaussianItoTest JointCutoffStep SmoothWords
open Classical
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩

theorem tail_append {n : ℕ} (v : ℝ) (z : WordRecursion.State n) :
    tailProjection n (JointPhysicalInsertion.appendState v z)=z := by
  apply PiLp.ext
  intro i
  rfl

variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n) (Λ δ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

/-- The exact epsilon correction is only the scalar coefficient heat
error, multiplied by the same full old-joint Hessian weight. -/
theorem heat_sub_literal {ε : ℝ} (hε : 0<ε) (p : P×(ℝ×HeatCircle)) (ω : Ω) :
    heatChildLeaf L Λ δ U V XU XV ε p ω-childLeaf L Λ δ U V XU XV p ω=
      (1/2:ℝ)*(R.totalVariance (PhysicalProfile.physicalHeatMean (V (ω,L.nodeTime p)) (ε,p.2.2))-
        R.totalVariance (XV (ω,(L.nodeTime p,p.2.2))))*
      directionalSecond (L.averagedTest p)
        (JointWordObserve.evaluate Λ (fun t => U (ω,t)) (fun t => V (ω,t))
          (fun tx => XU (ω,tx)) (fun tx => XV (ω,tx)) (L.observations.observations p.1) (L.nodeTime p))
        (L.cutoffRow δ p) := by
  have hLit : JointWordObserve.evaluate Λ (fun t => U (ω,t)) (fun t => V (ω,t))
      (fun tx => XU (ω,tx)) (fun tx => XV (ω,tx)) (L.childObservations.observations p) (L.nodeTime p)=
      JointPhysicalInsertion.appendState (XV (ω,(L.nodeTime p,p.2.2)))
        (JointWordObserve.evaluate Λ (fun t => U (ω,t)) (fun t => V (ω,t))
          (fun tx => XU (ω,tx)) (fun tx => XV (ω,tx)) (L.observations.observations p.1) (L.nodeTime p)) :=
    JointWordObserve.evaluate_append Λ _ _ _ _ _ _ _
  unfold heatChildLeaf childLeaf
  rw [JointWordObserveHeat.child_heat L Λ _ _ _ _ hε p,hLit]
  unfold CutoffWordLevel.Level.childTest CutoffInsertionCore.core
  simp only [JointPhysicalInsertion.appendState_zero,tail_append]
  ring

end SHE.JointHeatChildDifference
