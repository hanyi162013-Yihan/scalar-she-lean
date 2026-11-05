module

public import SHE.CutoffWordHistories

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.HistoryMeasureGeometry
open MeasureTheory CutoffWordLevel CutoffWordHistories

theorem nodeMeasure_eq {R Q : ReferenceData} (hb : R.base=Q.base) (hT : R.horizon=Q.horizon) :
    nodeMeasure R=nodeMeasure Q := by
  simp only [nodeMeasure,hb,hT]

theorem historyMeasure_eq {X : Type*} [MeasurableSpace X] {R Q : ReferenceData}
    (hb : R.base=Q.base) (hT : R.horizon=Q.horizon) (ν : Measure X) (k : ℕ) :
    historyMeasure R ν k=historyMeasure Q ν k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [historyMeasure,ih,nodeMeasure_eq hb hT]
    rfl

end SHE.HistoryMeasureGeometry
