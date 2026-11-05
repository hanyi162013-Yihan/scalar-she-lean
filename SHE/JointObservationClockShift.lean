module

public import SHE.ObservationTimeShift
public import SHE.JointWordObserve

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.JointObservationClockShift
open StoppedFourier WordRecursion
local instance jointObservationClockShift_period:Fact (0<2*Real.pi):=⟨by positivity⟩

/-- Clock translation keeps the original physical representative at
zero heat age, and keeps every positive heat age exactly. -/
theorem observe_translation {n:ℕ} (v q:ℝ) (U:ℝ→CircleL2) (X:ℝ×HeatCircle→ℝ)
    (Z:Fin n→Observation):
    observe U X (ObservationTimeShift.observations v Z) (q+v)=
      observe (fun t=>U (t+v)) (fun p=>X (p.1+v,p.2)) Z q:=by
  apply PiLp.ext
  intro i
  simp only [observe,WithLp.ofLp_toLp,ObservationTimeShift.observations_target,
    ObservationTimeShift.observations_center,add_lt_add_iff_right,add_sub_add_right_eq_sub]

/-- The stop damping and target heat age are both preserved by the
SAME clock translation; no stop/target identification is used. -/
theorem evaluate_translation {n:ℕ} (Λ v q:ℝ) (U V:ℝ→CircleL2)
    (XU XV:ℝ×HeatCircle→ℝ) (Z:Fin n→Observation):
    JointWordObserve.evaluate Λ U V XU XV (ObservationTimeShift.observations v Z) (q+v)=
      JointWordObserve.evaluate Λ (fun t=>U (t+v)) (fun t=>V (t+v))
        (fun p=>XU (p.1+v,p.2)) (fun p=>XV (p.1+v,p.2)) Z q:=by
  apply PiLp.ext
  intro i
  simp only [JointWordObserve.evaluate,WithLp.ofLp_toLp,observe_translation,
    ObservationTimeShift.observations_stop,add_sub_add_right_eq_sub]

end SHE.JointObservationClockShift
