module

public import SHE.PhysicalParentGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.PhysicalParentGeometry
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain OrderedHeatForests
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The actual recursive history with the same original parameter and
time coordinates, but with every insertion location freely integrated. -/
def replaceSpace : (k : ℕ) → History P k → (Fin k → HeatCircle) → History P k
  | 0,p,_ => p
  | k+1,p,x => (replaceSpace k p.1 (fun i => x i.succ),p.2.1,x 0)

theorem replaceSpace_root (k : ℕ) (p : History P k) (x : Fin k → HeatCircle) :
    rootParameter k (replaceSpace k p x)=rootParameter k p := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih p.1 (fun i => x i.succ)

theorem replaceSpace_terminal (k : ℕ) (p : History P k) (x : Fin k → HeatCircle) :
    (carrier L k).terminal (replaceSpace k p x)=(carrier L k).terminal p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ClippedCovariance.clip R.base
        ((carrier L k).terminal (replaceSpace k p.1 (fun i => x i.succ))) p.2.1 =
      ClippedCovariance.clip R.base ((carrier L k).terminal p.1) p.2.1
    rw [ih]

theorem replaceSpace_nodeTime (k : ℕ) (p : History P (k+1)) (x : Fin (k+1) → HeatCircle) :
    (carrier L k).nodeTime (replaceSpace (k+1) p x)=(carrier L k).nodeTime p := by
  change ClippedCovariance.clip R.base
      ((carrier L k).terminal (replaceSpace k p.1 (fun i => x i.succ))) p.2.1 =
    ClippedCovariance.clip R.base ((carrier L k).terminal p.1) p.2.1
  rw [replaceSpace_terminal]

theorem replaceSpace_targets (k : ℕ) (p : History P k) (x : Fin k → HeatCircle) :
    (fun i => ((carrier L k).observations.observations (replaceSpace k p x) i).target) =
      fun i => ((carrier L k).observations.observations p i).target := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => congrFun (ih p.1 (fun i => x i.succ)) j) i
    change (carrier L k).nodeTime (replaceSpace (k+1) p x)+0=(carrier L k).nodeTime p+0
    rw [replaceSpace_nodeTime]

theorem replaceSpace_space (k : ℕ) (p : History P k) (x : Fin k → HeatCircle) :
    PhysicalChainArrays.space k (replaceSpace k p x)=x := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih p.1 (fun i => x i.succ)) j

theorem replaceSpace_centers (k : ℕ) (p : History P k) (x : Fin k → HeatCircle) :
    (fun i => ((carrier L k).observations.observations (replaceSpace k p x) i).center) =
      values (fun i => (L.observations.observations (rootParameter k p) i).center) k x := by
  rw [carrier_centers_eq_values,replaceSpace_root,replaceSpace_space]

theorem replaceSpace_strict_iff (k : ℕ) (p : History P k) (x : Fin k → HeatCircle) :
    StrictHistory L k (replaceSpace k p x) ↔ StrictHistory L k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (StrictHistory L k (replaceSpace k p.1 (fun i => x i.succ)) ∧
        (R.base<p.2.1 ∧ p.2.1<(carrier L k).terminal (replaceSpace k p.1 (fun i => x i.succ)))) ↔
      (StrictHistory L k p.1 ∧ (R.base<p.2.1 ∧ p.2.1<(carrier L k).terminal p.1))
    rw [ih,replaceSpace_terminal]

end SHE.PhysicalParentGeometry
