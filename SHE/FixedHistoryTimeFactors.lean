module

public import SHE.WordTimeScaleFields
public import SHE.ActualMeanPointBounds
public import SHE.HistorySpatialSections

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.FixedHistoryTimeFactors
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalChainArrays PhysicalScoreChain HistoryProductMeasure
  ActualMeanKernel CoveredHistoryGeometry CoveredControlledLaw
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)
variable (T : ℝ) (hT : ∀ p,L.terminal p=T)
include T hT

theorem nodeTime_separated (k : ℕ) (t : Fin (k+1) → ℝ) (p : P) (x : Fin (k+1) → HeatCircle) :
    (carrier L k).nodeTime (separated (k+1) (p,t,x))=fixedTerminal (R:=R) T (k+1) t :=
  terminal_separated L T hT (k+1) t p x

/-- The full old interval arrays depend only on original terminal and
old times, even when the original root point and all old sites change. -/
theorem lower_sections (k : ℕ) (t : Fin k → ℝ) (p p' : P) (x x' : Fin k → HeatCircle) :
    lower L k (separated k (p,t,x))=lower L k (separated k (p',t,x')) := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (carrier L k).nodeTime (separated (k+1) (p,t,x))=
        (carrier L k).nodeTime (separated (k+1) (p',t,x'))
      rw [nodeTime_separated L T hT,nodeTime_separated L T hT]
    · exact congrFun (ih (fun i => t i.succ) (fun i => x i.succ) (fun i => x' i.succ)) j

theorem upper_sections (k : ℕ) (t : Fin k → ℝ) (p p' : P) (x x' : Fin k → HeatCircle) :
    upper L k (separated k (p,t,x))=upper L k (separated k (p',t,x')) := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (carrier L k).terminal (separated k (p,(fun i => t i.succ),(fun i => x i.succ)))=
        (carrier L k).terminal (separated k (p',(fun i => t i.succ),(fun i => x' i.succ)))
      rw [terminal_separated L T hT,terminal_separated L T hT]
    · exact congrFun (ih (fun i => t i.succ) (fun i => x i.succ) (fun i => x' i.succ)) j

theorem timeWeight_sections (ell : ℝ) (C : ℕ → ℝ) (k : ℕ) (t : Fin k → ℝ)
    (p p' : P) (x x' : Fin k → HeatCircle) :
    timeWeight L ell C k (separated k (p,t,x))=timeWeight L ell C k (separated k (p',t,x')) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change timeWeight L ell C k (separated k (p,(fun i => t i.succ),(fun i => x i.succ)))*
        (C k/(ell*((carrier L k).terminal (separated k (p,(fun i => t i.succ),(fun i => x i.succ)))-
          (carrier L k).nodeTime (separated (k+1) (p,t,x)))))=_
    rw [ih,terminal_separated L T hT,nodeTime_separated L T hT]
    change _=timeWeight L ell C k (separated k (p',(fun i => t i.succ),(fun i => x' i.succ)))*
        (C k/(ell*((carrier L k).terminal (separated k (p',(fun i => t i.succ),(fun i => x' i.succ)))-
          (carrier L k).nodeTime (separated (k+1) (p',t,x')))))
    rw [terminal_separated L T hT,nodeTime_separated L T hT]

theorem targets_sections (target : Fin n → ℝ)
    (htarget : ∀ p i,(L.observations.observations p i).target=target i)
    (k : ℕ) (t : Fin k → ℝ) (p p' : P) (x x' : Fin k → HeatCircle) :
    targets L k (separated k (p,t,x))=targets L k (separated k (p',t,x')) := by
  induction k with
  | zero =>
    funext i
    exact (htarget p i).trans (htarget p' i).symm
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (carrier L k).nodeTime (separated (k+1) (p,t,x))+0=
        (carrier L k).nodeTime (separated (k+1) (p',t,x'))+0
      rw [nodeTime_separated L T hT,nodeTime_separated L T hT]
    · exact congrFun (ih (fun i => t i.succ) (fun i => x i.succ) (fun i => x' i.succ)) j

/-- Exact root/rough assignment time sum is independent of the scalar
output point. No individual gap degree or Bernstein clip is discarded. -/
theorem total_sections (Q : CanonicalCovariance.ProfileParameters) (target : Fin n → ℝ)
    (htarget : ∀ p i,(L.observations.observations p i).target=target i)
    (k : ℕ) (t : Fin k → ℝ) (p p' : P) (x x' : Fin k → HeatCircle) (q A0 ν : ℝ) :
    PhysicalWordTimeScale.total L Q k (separated k (p,t,x)) q A0 ν=
      PhysicalWordTimeScale.total L Q k (separated k (p',t,x')) q A0 ν := by
  have hl := lower_sections L T hT k t p p' x x'
  have hu := upper_sections L T hT k t p p' x x'
  have ht := targets_sections L T hT target htarget k t p p' x x'
  have he : (carrier L k).terminal (separated k (p,t,x))=
      (carrier L k).terminal (separated k (p',t,x')) := by
    rw [terminal_separated L T hT,terminal_separated L T hT]
  simp only [PhysicalWordTimeScale.total,PhysicalWordTimeScale.factor,
    lowerWith,upperWith,hl,hu,ht,he]

end SHE.FixedHistoryTimeFactors
