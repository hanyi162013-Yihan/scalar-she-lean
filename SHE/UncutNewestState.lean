module

public import SHE.JointUncutWordEvaluation
public import SHE.FullPhysicalWord
public import SHE.OldIntervalGaussian
public import SHE.CoveredHistoryGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHE.UncutNewestState
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffInsertionCore
  GaussianConvolution SmoothWords JointPhysicalInsertion JointWordObserve
  PhysicalChainArrays CoveredHistoryGeometry
open scoped BigOperators
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

omit [MeasurableSpace Ω] in
/-- The actual successor terminal state appends exactly the newest V
point; every earlier joint observation remains in its original position. -/
theorem terminal_append (Λ : ℝ) (U V : Ω×ℝ→CircleL2)
    (XU XV : Ω×(ℝ×HeatCircle)→ℝ) (k : ℕ) (p : History X (k+1)) (ω : Ω) :
    JointWordAnalytic.state (carrier L (k+1)) Λ U V XU XV p ω
      ((carrier L (k+1)).terminal p)=
      appendState (XV (ω,((carrier L k).nodeTime p,p.2.2)))
        (JointWordAnalytic.state (carrier L k) Λ U V XU XV p.1 ω ((carrier L k).nodeTime p)) := by
  change JointWordObserve.evaluate Λ _ _ _ _ _ _=_
  have ht : (carrier L (k+1)).terminal p=(carrier L k).nodeTime p:=rfl
  have hobs : (carrier L (k+1)).observations.observations p=
      appendObservation ((carrier L k).observations.observations p.1)
        ((carrier L k).nodeTime p) p.2.2:=by
    funext i
    refine Fin.cases ?_ (fun _=>rfl) i
    change Observation.mk _ (_+0) _=Observation.mk _ _ _
    rw [add_zero]
    rfl
  rw [ht,hobs]
  exact JointWordObserve.evaluate_append _ _ _ _ _ _ _ _

end SHE.UncutNewestState
