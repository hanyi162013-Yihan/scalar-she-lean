module
public import SHE.PhysicalGapIntegration
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace SHE.StrictHistoryOrder
open Set MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalParentGeometry PhysicalOrderedGaps HistoryProductMeasure OrderedGapCoordinates
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X:Type}[MeasurableSpace X]{R:ReferenceData}{n:ℕ}(L:Level R X n)

/-- A genuinely positive root window makes the original strict
history mask precisely the full newest-first ordered time domain. -/
theorem iff_ordered (T:ℝ)(hT:∀x,L.terminal x=T)(hpos:R.base<T)
    (k:ℕ)(t:Fin k→ℝ)(x:X)(w:Fin k→HeatCircle):
    StrictHistory L k (separated k (x,t,w))↔ordered R.base T k t:=by
  induction k with
  | zero=>simpa only [StrictHistory,ordered,true_iff] using hpos
  | succ k ih=>
    let p:=separated k (x,(fun i=>t i.succ),(fun i=>w i.succ))
    change (StrictHistory L k p ∧ R.base<t 0 ∧ t 0<(carrier L k).terminal p)↔
      (R.base<t 0 ∧ t 0<boundary T k (fun i=>t i.succ) ∧
        ordered R.base T k (fun i=>t i.succ))
    constructor
    · intro hp
      have he:=terminal_eq_boundary L T hT k (fun i=>t i.succ) x (fun i=>w i.succ) hp.1
      exact ⟨hp.2.1,hp.2.2.trans_eq he,(ih (fun i=>t i.succ) (fun i=>w i.succ)).mp hp.1⟩
    · intro hp
      have hs:=(ih (fun i=>t i.succ) (fun i=>w i.succ)).mpr hp.2.2
      have he:=terminal_eq_boundary L T hT k (fun i=>t i.succ) x (fun i=>w i.succ) hs
      change (carrier L k).terminal p=boundary T k (fun i=>t i.succ) at he
      exact ⟨hs,hp.1,by rw [he];exact hp.2.1⟩
end SHE.StrictHistoryOrder
