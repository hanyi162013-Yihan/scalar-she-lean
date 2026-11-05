module

public import SHE.PhysicalScoreSpatialFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry HistoryProductMeasure
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

theorem timeWeight_replaceSpace (ell : ℝ) (C : ℕ → ℝ) (k : ℕ)
    (p : History P k) (x : Fin k → HeatCircle) :
    timeWeight L ell C k (replaceSpace k p x)=timeWeight L ell C k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change timeWeight L ell C k (replaceSpace k p.1 (fun i => x i.succ))*
        (C k/(ell*((carrier L k).terminal (replaceSpace k p.1 (fun i => x i.succ))-
          (carrier L k).nodeTime (replaceSpace (k+1) p x)))) = _
    rw [ih,replaceSpace_terminal,replaceSpace_nodeTime]
    rfl

theorem smallHistory_replaceSpace_iff (H : ℕ → ℝ) (k : ℕ)
    (p : History P k) (x : Fin k → HeatCircle) :
    SmallHistory L H k (replaceSpace k p x) ↔ SmallHistory L H k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (SmallHistory L H k (replaceSpace k p.1 (fun i => x i.succ)) ∧
      ∀ i, ((carrier L k).observations.observations (replaceSpace k p.1 (fun i => x i.succ)) i).target-
        (carrier L k).nodeTime (replaceSpace (k+1) p x) ≤ H k) ↔ _
    rw [ih,replaceSpace_nodeTime]
    have he := replaceSpace_targets L k p.1 (fun i => x i.succ)
    change (SmallHistory L H k p.1 ∧ ∀ i,
      (fun j => ((carrier L k).observations.observations (replaceSpace k p.1 (fun i => x i.succ)) j).target) i-
        (carrier L k).nodeTime p ≤ H k) ↔ _
    rw [he]
    rfl

theorem actual_scoreProduct_spatial_measurable (c : StoppedGaussianFeatures.Domain → ℝ)
    (hc : Measurable c) (k : ℕ) (p : History P k) :
    Measurable (fun x : Fin k → HeatCircle =>
      scoreProduct L ((carrier L k).observations.observations (replaceSpace k p x)) c k (replaceSpace k p x)) :=
  (scoreProduct_measurable L c hc k).comp (replaceSpace_measurable k p)

end SHE.PhysicalScoreChain
