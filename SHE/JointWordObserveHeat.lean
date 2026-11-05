module

public import SHE.JointWordObserve
public import SHE.HeatCutoffHistories

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.JointWordObserveHeat
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel HeatCutoffHistories
open JointWordObserve
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩

/-- A newly appended stop q with target q+epsilon is the literal heat
observation of Vq; old joint coordinates keep their original stops. -/
theorem append_heat {n : ℕ} (Λ : ℝ) (U V : ℝ→CircleL2) (XU XV : ℝ×HeatCircle→ℝ)
    (Z : Fin n→Observation) (q : ℝ) {ε : ℝ} (hε : 0<ε) (x : HeatCircle) :
    evaluate Λ U V XU XV (Fin.cases ⟨q,q+ε,x⟩ Z) q=
      JointPhysicalInsertion.appendState (PhysicalProfile.physicalHeatMean (V q) (ε,x))
        (evaluate Λ U V XU XV Z q) := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [evaluate,WithLp.ofLp_toLp,Fin.cases_zero,observe,
      ite_eq_left (lt_add_of_pos_right q hε),sub_self,mul_zero,Real.exp_zero,one_mul,
      show q+ε-q=ε by ring,JointPhysicalInsertion.appendState_zero]
    ring
  · simp only [evaluate,WithLp.ofLp_toLp,Fin.cases_succ,observe,JointPhysicalInsertion.appendState_succ]

variable {P : Type*} [MeasurableSpace P] {R : ReferenceData} {n : ℕ} (L : Level R P n)

theorem child_heat (Λ : ℝ) (U V : ℝ→CircleL2) (XU XV : ℝ×HeatCircle→ℝ)
    {ε : ℝ} (hε : 0<ε) (p : P×(ℝ×HeatCircle)) :
    evaluate Λ U V XU XV ((Level.heatChildObservations L ε).observations p) (L.nodeTime p)=
      JointPhysicalInsertion.appendState
        (PhysicalProfile.physicalHeatMean (V (L.nodeTime p)) (ε,p.2.2))
        (evaluate Λ U V XU XV (L.observations.observations p.1) (L.nodeTime p)) := by
  exact append_heat Λ U V XU XV _ (L.nodeTime p) hε p.2.2

end SHE.JointWordObserveHeat
