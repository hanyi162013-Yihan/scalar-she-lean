module

public import SHE.WordRootReindex
public import SHE.JointWordAnalytic
public import SHE.StrictHistoryFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.WordRootReindex
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalParentGeometry
variable {X Y Ω:Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R Q:ReferenceData} {n:ℕ} (L:Level R Y n) (K:Level Q X n) (f:X→Y)
variable (hb:Q.base=R.base) (hT:∀x,K.terminal x=L.terminal (f x))
variable (hZ:∀x,K.observations.observations x=L.observations.observations (f x))
include hb hT

theorem strict_iff (k:ℕ) (p:History X k):StrictHistory K k p↔StrictHistory L k (history f k p):=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    change (StrictHistory K k p.1 ∧ Interior K k p)↔_
    rw [ih p.1,interior_iff L K f hb hT k p]
    rfl

include hZ in
theorem current (Λ:ℝ) (U V:Ω×ℝ→CircleL2) (XU XV:Ω×(ℝ×HeatCircle)→ℝ)
    (k:ℕ) (p:History X k) (ω:Ω):
    JointWordAnalytic.state (carrier K k) Λ U V XU XV p ω ((carrier K k).terminal p)=
      JointWordAnalytic.state (carrier L k) Λ U V XU XV (history f k p) ω
        ((carrier L k).terminal (history f k p)):=by
  unfold JointWordAnalytic.state
  rw [terminal L K f hb hT k p,observations L K f hb hT hZ k p]

end SHE.WordRootReindex
