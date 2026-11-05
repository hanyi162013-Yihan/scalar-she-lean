module

public import SHE.PhysicalGapIntegration
public import SHE.DefectCombinedTime

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000

namespace SHE.DefectGapOffsets
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalChainArrays PhysicalScoreChain HistoryProductMeasure
  CoveredControlledLaw OrderedGapCoordinates
open scoped BigOperators
local instance defectGapOffsets_period:Fact (0<2*Real.pi):=⟨by positivity⟩

/-- Every original endpoint offset from the newest terminal is an
actual sum of original gaps, including the newest zero offset. -/
def offsets:(k:ℕ)→(Fin k→ℝ)→Fin (1+k)→ℝ
  | 0,_=>fun _=>0
  | k+1,d=>Fin.cases 0 (fun j=>offsets k (fun i=>d i.succ) j+d 0)

theorem offsets_nonneg (k:ℕ)(d:Fin k→ℝ)(hd:∀i,0≤d i):∀i,0≤offsets k d i:=by
  induction k with
  | zero=>intro i;exact le_refl 0
  | succ k ih=>
    intro i
    exact Fin.cases (by simp [offsets])
      (fun j=>add_nonneg (ih (fun i=>d i.succ) (fun i=>hd i.succ) j) (hd 0)) i

theorem offsets_measurable (k:ℕ):Measurable (offsets k):=by
  induction k with
  | zero=>exact measurable_const
  | succ k ih=>
    apply Measurable.of_eval
    intro i
    refine Fin.cases measurable_const (fun j=>?_) i
    exact (((measurable_pi_apply j).comp ih).comp (Measurable.of_eval (fun i=>measurable_pi_apply i.succ))).add
      (measurable_pi_apply 0)

variable {R:ReferenceData}{X:Type}[MeasurableSpace X](L:Level R X 1)
variable (T:ℝ)(hT:∀x,L.terminal x=T)
variable (hroot:∀x i,(L.observations.observations x i).target=T)
include hT hroot

theorem targets_relative (k:ℕ)(t:Fin k→ℝ)(x:X)(w:Fin k→HeatCircle)
    (hp:StrictHistory L k (separated k (x,t,w))):
    (fun i=>targets L k (separated k (x,t,w)) i-
      (carrier L k).terminal (separated k (x,t,w)))=offsets k (gaps T k t):=by
  induction k with
  | zero=>funext i;change (L.observations.observations x i).target-L.terminal x=0;rw [hroot,hT];ring
  | succ k ih=>
    have hnode:(carrier L k).nodeTime (separated (k+1) (x,t,w))=t 0:=
      ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩
    have hprev:=PhysicalOrderedGaps.terminal_eq_boundary L T hT k
      (fun i=>t i.succ) x (fun i=>w i.succ) hp.1
    have hh:=ih (fun i=>t i.succ) (fun i=>w i.succ) hp.1
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · change (carrier L k).nodeTime (separated (k+1) (x,t,w))+0-
        (carrier L k).nodeTime (separated (k+1) (x,t,w))=0
      ring
    · change targets L k (separated k (x,(fun i=>t i.succ),(fun i=>w i.succ))) j-
        (carrier L k).nodeTime (separated (k+1) (x,t,w))=
          offsets k (fun i=>gaps T (k+1) t i.succ) j+gaps T (k+1) t 0
      simp only [gaps,Fin.cons_succ,Fin.cons_zero]
      rw [hnode]
      have he:=congrFun hh j
      rw [hprev] at he
      linarith

/-- The original new-time input is a genuine translation by the sum
of all old gaps PLUS its own fresh age. -/
theorem input_clock (k:ℕ)(t:Fin k→ℝ)(x:X)(w:Fin k→HeatCircle)
    (hp:StrictHistory L k (separated k (x,t,w)))(q:ℝ):
    q=T-(∑i,gaps T k t i)-((carrier L k).terminal (separated k (x,t,w))-q):=by
  rw [sum_gaps,PhysicalOrderedGaps.terminal_eq_boundary L T hT k t x w hp]
  ring

end SHE.DefectGapOffsets
