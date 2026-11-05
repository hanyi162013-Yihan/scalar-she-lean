module

public import SHE.PhysicalParentGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.PhysicalParentGeometry
open Set MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

theorem strictHistory_measurableSet (k : ℕ) : MeasurableSet {p : History P k | StrictHistory L k p} := by
  induction k with
  | zero => exact MeasurableSet.univ
  | succ k ih =>
    have hp : MeasurableSet {p : History P (k+1) | StrictHistory L k p.1} :=
      ih.preimage measurable_fst
    have hi : MeasurableSet {p : History P (k+1) | Interior L k p} := interior_measurableSet L k
    exact hp.inter hi

/-- The actual active time/history domain is jointly Borel before any
conditional or spatial exceptional sets are disintegrated. -/
theorem activeHistory_measurableSet (k : ℕ) (q : ℝ) :
    MeasurableSet {p : History P k | StrictHistory L k p ∧ q < (carrier L k).terminal p} :=
  (strictHistory_measurableSet L k).inter
    (measurableSet_lt measurable_const (carrier L k).terminal_measurable)

end SHE.PhysicalParentGeometry
