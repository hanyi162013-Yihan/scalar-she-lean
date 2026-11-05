module
public import SHE.JointUncutWordEvaluation
public import SHE.JointUncutLocalRemainder
public import SHE.ActualUncutRemainder

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.OrdinaryJointSelf
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers UncutWordEvaluation
variable {P Ω:Type}[MeasurableSpace P][MeasurableSpace Ω]
variable [MeasurableSpace CircleL2][BorelSpace CircleL2]
variable {R:ReferenceData}{n:ℕ}(L:Level R P n)(Λ:ℝ)
variable (U:Ω×ℝ→CircleL2)(X:Ω×(ℝ×HeatCircle)→ℝ)

/-- Self-pair specialization really is the ordinary observation;
changing a reference-profile parameter alone would not imply this. -/
theorem state (p:P)(ω:Ω)(t:ℝ):
    JointWordAnalytic.state L Λ U U X X p ω t=
      observe (fun s=>U (ω,s)) (fun q=>X (ω,q)) (L.observations.observations p) t:=by
  apply PiLp.ext
  intro i
  simp only [JointWordAnalytic.state,JointWordObserve.evaluate,WithLp.ofLp_toLp,
    sub_self,mul_zero,add_zero]

theorem reference (p:P)(ω:Ω):
    JointWordAnalytic.reference L Λ U U X X p ω=
      (CutoffWordAnalytic.physicalLevel L U X (fun _ _ _=>0)).reference p ω:=by
  unfold JointWordAnalytic.reference
  rw [state]
  rfl

theorem localRemainder (p:P)(ω:Ω):
    JointWordAnalytic.remainder L Λ U U X X p ω=
      PhysicalIto.wordRemainder (L.window p) R.totalVariance
        (fun t=>U (ω,t)) (fun q=>X (ω,q)) (L.test p):=by
  unfold JointWordAnalytic.remainder PhysicalIto.wordRemainder
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  apply integral_congr_ae
  filter_upwards with y
  unfold JointWordAnalytic.insertion PhysicalIto.insertedWord
  rw [WordRecursion.insertion_observe,JointPhysicalInsertion.insertion_appendState,state]
  rfl

theorem uncutLeaf (k:ℕ)(p:History P k)(ω:Ω):
    JointUncutWordEvaluation.leaf L Λ U U X X k p ω=UncutWordEvaluation.leaf L U X k p ω:=by
  unfold JointUncutWordEvaluation.leaf UncutWordEvaluation.leaf
  rw [state]

theorem uncutLocalRemainder (k:ℕ)(p:History P k)(ω:Ω):
    JointUncutLocalRemainder.value L Λ U U X X k p ω=
      ActualUncutRemainder.value L R.totalVariance U X k p ω:=by
  unfold JointUncutLocalRemainder.value ActualUncutRemainder.value
  rw [localRemainder]

end SHE.OrdinaryJointSelf
