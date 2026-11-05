module

public import SHE.FixedHistoryDomain
public import SHE.OrderedGapCoordinates
public import SHE.CoveredHistoryGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.PhysicalOrderedGaps
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain PhysicalChainArrays HistoryProductMeasure
  ActualMeanKernel CoveredHistoryGeometry OrderedGapCoordinates
open scoped BigOperators
local instance physicalOrderedGaps_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

theorem terminal_eq_boundary (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (t : Fin k → ℝ) (p : P) (x : Fin k → HeatCircle)
    (hp : StrictHistory L k (separated k (p,t,x))) :
    (carrier L k).terminal (separated k (p,t,x))=boundary T k t := by
  cases k with
  | zero => exact hT p
  | succ k =>
    change ClippedCovariance.clip R.base
      ((carrier L k).terminal (separated k (p,(fun i => t i.succ),(fun i => x i.succ)))) (t 0)=t 0
    exact ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩

/-- On the actual active interval every clipped history time is its
literal time coordinate; the active domain is exactly the ordered domain. -/
theorem strict_active_iff_ordered (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (q : ℝ) (hqbase : R.base ≤ q) (k : ℕ) (t : Fin k → ℝ) (p : P) (x : Fin k → HeatCircle) :
    (StrictHistory L k (separated k (p,t,x)) ∧ q < (carrier L k).terminal (separated k (p,t,x))) ↔
      ordered q T k t := by
  induction k with
  | zero =>
    change (True ∧ q < L.terminal p) ↔ q < T
    rw [hT]
    simp only [true_and]
  | succ k ih =>
    let a : History P k := separated k (p,(fun i => t i.succ),(fun i => x i.succ))
    constructor
    · rintro ⟨hp,hq⟩
      have hterm := terminal_eq_boundary L T hT (k+1) t p x hp
      have hq0 : q < t 0 := by simpa only [boundary] using (hq.trans_eq hterm)
      have hb := terminal_eq_boundary L T hT k (fun i => t i.succ) p (fun i => x i.succ) hp.1
      change q < t 0 ∧ t 0 < boundary T k (fun i => t i.succ) ∧ ordered q T k (fun i => t i.succ)
      refine ⟨hq0,hp.2.2.trans_eq hb,?_⟩
      exact (ih (fun i => t i.succ) (fun i => x i.succ)).mp ⟨hp.1,hq0.trans hp.2.2⟩
    · rintro ⟨hq0,ht,horder⟩
      have hold := (ih (fun i => t i.succ) (fun i => x i.succ)).mpr horder
      have hb := terminal_eq_boundary L T hT k (fun i => t i.succ) p (fun i => x i.succ) hold.1
      have hi : Interior L k (a,t 0,x 0) := ⟨hqbase.trans_lt hq0,by simpa only [a,hb] using ht⟩
      have hs : StrictHistory L (k+1) (separated (k+1) (p,t,x)) := ⟨hold.1,hi⟩
      refine ⟨hs,?_⟩
      simpa only [terminal_eq_boundary L T hT (k+1) t p x hs,boundary] using hq0

theorem lower_eq_times (k : ℕ) (t : Fin k → ℝ) (p : P) (x : Fin k → HeatCircle)
    (hp : StrictHistory L k (separated k (p,t,x))) :
    lower L k (separated k (p,t,x))=t := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩
    · exact congrFun (ih (fun i => t i.succ) (fun i => x i.succ) hp.1) j

/-- Every old Gaussian interval has exactly its original ordered gap,
before integrating or replacing any gap by another one. -/
theorem old_gaps_eq (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (t : Fin k → ℝ) (p : P) (x : Fin k → HeatCircle)
    (hp : StrictHistory L k (separated k (p,t,x))) :
    (fun i => upper L k (separated k (p,t,x)) i-lower L k (separated k (p,t,x)) i)=gaps T k t := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (carrier L k).terminal (separated k (p,(fun i => t i.succ),(fun i => x i.succ)))-
        (carrier L k).nodeTime (separated (k+1) (p,t,x))=
          boundary T k (fun i => t i.succ)-t 0
      rw [terminal_eq_boundary L T hT k _ _ _ hp.1]
      exact congrArg (fun z => boundary T k (fun i => t i.succ)-z)
        (ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩)
    · exact congrFun (ih (fun i => t i.succ) (fun i => x i.succ) hp.1) j

/-- Fresh interval plus every old interval form the exact positive-gap
simplex coordinates, with the fresh gap as its genuine slack. -/
theorem all_gaps_eq (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (t : Fin k → ℝ) (p : P) (x : Fin k → HeatCircle)
    (hp : StrictHistory L k (separated k (p,t,x))) (q : ℝ) :
    (fun i => upperWith L k (separated k (p,t,x)) i-lowerWith L k (separated k (p,t,x)) q i)=
      Fin.cons ((T-q)-∑ j,gaps T k t j) (gaps T k t) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [upperWith,lowerWith,Fin.cases_zero,Fin.cons_zero]
    rw [terminal_eq_boundary L T hT k t p x hp,sum_gaps]
    ring
  · simpa only [upperWith,lowerWith,Fin.cases_succ,Fin.cons_succ] using congrFun (old_gaps_eq L T hT k t p x hp) j

end SHE.PhysicalOrderedGaps
