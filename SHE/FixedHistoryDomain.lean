module

public import SHE.FixedHistoryTimeFactors
public import SHE.StrictHistoryFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.FixedHistoryTimeFactors
open Set MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalParentGeometry PhysicalScoreChain HistoryProductMeasure ActualMeanKernel
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The exact active ordered-history domain is independent of the root
and old insertion sites when the original terminal is fixed. -/
theorem strict_sections (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (t : Fin k → ℝ) (p p' : P) (x x' : Fin k → HeatCircle) :
    StrictHistory L k (separated k (p,t,x)) ↔ StrictHistory L k (separated k (p',t,x')) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (StrictHistory L k (separated k (p,(fun i => t i.succ),(fun i => x i.succ))) ∧
      R.base < t 0 ∧ t 0 < (carrier L k).terminal
        (separated k (p,(fun i => t i.succ),(fun i => x i.succ)))) ↔ _
    rw [ih,terminal_separated L T hT]
    change _ ↔ (StrictHistory L k (separated k (p',(fun i => t i.succ),(fun i => x' i.succ))) ∧
      R.base < t 0 ∧ t 0 < (carrier L k).terminal
        (separated k (p',(fun i => t i.succ),(fun i => x' i.succ))))
    rw [terminal_separated L T hT]

/-- The deterministic full old-score time weight is globally Borel,
including the inactive and collision extensions. -/
theorem timeWeight_measurable (ell : ℝ) (C : ℕ → ℝ) (k : ℕ) :
    Measurable (timeWeight L ell C k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    change Measurable (fun p : History P (k+1) => timeWeight L ell C k p.1*
      (C k/(ell*((carrier L k).terminal p.1-(carrier L k).nodeTime p))))
    exact (ih.comp measurable_fst).mul (measurable_const.div
      ((((carrier L k).terminal_measurable.comp measurable_fst).sub
        (carrier L k).nodeTime_measurable).const_mul ell))

end SHE.FixedHistoryTimeFactors
