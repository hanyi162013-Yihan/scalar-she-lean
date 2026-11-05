module

public import SHE.ObservationTimeShift
public import SHE.StopWeightedRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHE.ObservationTimeShift
open WordRecursion StoppedFourier StopWeightedRows
variable {n : ℕ}

/-- A common past-time shift leaves both the original stop damping
and the genuine later physical direction age exactly unchanged. -/
theorem weightedHeatRow_translation (v Λ q r : ℝ) (Z : Fin n→Observation)
    (y : HeatCircle) :
    weightedHeatRow Λ (observations v Z) (q+v) (r+v) y=
      weightedHeatRow Λ Z q r y := by
  unfold weightedHeatRow
  rw [heatRow_translation]
  congr 1
  apply congrArg diagonal
  funext i
  unfold weights observations
  congr 2
  ring

end SHE.ObservationTimeShift
