module

public import SHE.JointWordObserve
public import SHE.ObservationTargetContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.JointObservationTargetContinuity
open StoppedFourier WordRecursion JointWordObserve

/-- True joint observation continuity when targets move, with the
original individual stops controlling their own exponential weights. -/
theorem continuous_evaluate {P : Type*} [TopologicalSpace P] {n : ℕ}
    (Λ : ℝ) (Z : P→Fin n→Observation) (centers : Fin n→HeatCircle)
    (hT : ∀ i,Continuous (fun p => (Z p i).target))
    (hσ : ∀ i,Continuous (fun p => (Z p i).stop))
    (hx : ∀ p i,(Z p i).center=centers i)
    (t : ℝ) (hgap : ∀ p i,t<(Z p i).target)
    (U V : ℝ→CircleL2) (XU XV : ℝ×HeatCircle→ℝ) :
    Continuous (fun p => evaluate Λ U V XU XV (Z p) t) := by
  have hu := ObservationTargetContinuity.continuous_observe Z centers hT hx t hgap U XU
  have hv := ObservationTargetContinuity.continuous_observe Z centers hT hx t hgap V XV
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  apply continuous_pi
  intro i
  have hui := (EuclideanSpace.proj i).continuous.comp hu
  have hvi := (EuclideanSpace.proj i).continuous.comp hv
  have he : Continuous (fun p => Real.exp (-Λ*((Z p i).stop-t))) :=
    Real.continuous_exp.comp (((hσ i).sub continuous_const).const_mul (-Λ))
  exact hui.add (he.mul (hvi.sub hui))

end SHE.JointObservationTargetContinuity
