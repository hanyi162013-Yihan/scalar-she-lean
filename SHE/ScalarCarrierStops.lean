module

public import SHE.CutoffCarriers

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace SHE.ScalarCarrierStops
open CutoffWordLevel CutoffWordHistories CutoffCarriers WordRecursion
variable {P:Type*}[MeasurableSpace P]{R:ReferenceData}{n:ℕ}(L:Level R P n)

/-- An actual zero-offset recursive observation keeps stop equal to
target whenever this holds for the original root observations. Every
original and newly inserted coordinate is retained. -/
theorem stop_eq_target
    (hroot:∀p i,(L.observations.observations p i).stop=(L.observations.observations p i).target)
    (k:ℕ)(h:History P k)(i:Fin (n+k)):
    ((carrier L k).observations.observations h i).stop=
      ((carrier L k).observations.observations h i).target:=by
  induction k with
  | zero=>exact hroot h i
  | succ k ih=>
    refine Fin.cases ?_ (fun j=>ih h.1 j) i
    change (carrier L k).nodeTime h=(carrier L k).nodeTime h+0
    simp only [add_zero]

end SHE.ScalarCarrierStops
