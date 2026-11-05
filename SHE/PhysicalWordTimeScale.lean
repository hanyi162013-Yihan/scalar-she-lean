module

public import SHE.NativeActualPointMoments
public import SHE.ScoreSpatialStability

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.PhysicalWordTimeScale
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalChainArrays CoveredHistoryGeometry CoveredControlledLaw
  GaussianCoordinates GaussianFreshAssignments GaussianAssignmentBlocks
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

theorem lower_replaceSpace (k : ℕ) (p : History X k) (x : Fin k → HeatCircle) :
    lower L k (replaceSpace k p x)=lower L k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact replaceSpace_nodeTime L k p x
    · exact congrFun (ih p.1 (fun i => x i.succ)) j

theorem upper_replaceSpace (k : ℕ) (p : History X k) (x : Fin k → HeatCircle) :
    upper L k (replaceSpace k p x)=upper L k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact replaceSpace_terminal L k p.1 (fun i => x i.succ)
    · exact congrFun (ih p.1 (fun i => x i.succ)) j

theorem lowerWith_replaceSpace (k : ℕ) (p : History X k) (q : ℝ) (x : Fin k → HeatCircle) :
    lowerWith L k (replaceSpace k p x) q=lowerWith L k p q := by
  simp only [lowerWith,lower_replaceSpace]

theorem upperWith_replaceSpace (k : ℕ) (p : History X k) (x : Fin k → HeatCircle) :
    upperWith L k (replaceSpace k p x)=upperWith L k p := by
  simp only [upperWith,replaceSpace_terminal,upper_replaceSpace]

/-- Every original root clip and selected/full rough-leaf age is kept.
This factor depends only on the true history times, not insertion sites. -/
def factor (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k) (q : ℝ)
    (choices : List (Fin k×Fin (k+1)))
    (chosen : ∀ j : Fin k,block (liftChoices choices) j.succ≠[]→Fin (k+1)) (A0 ν : ℝ) : ℝ :=
  VectorPhysicalRoot.scale (liftChoices choices) 0 (lowerWith L k p q) (upperWith L k p) A0 ν (Q.lower/2) n*
    ∏ j,NativeAssignedLeafMoments.leafScale Q (liftChoices choices) j.succ
      (lowerWith L k p q) (upperWith L k p) (targets L k p (leafIndex k (fun i => i) j)) (chosen j)

theorem factor_replaceSpace (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k) (q : ℝ)
    (choices : List (Fin k×Fin (k+1)))
    (chosen : ∀ j : Fin k,block (liftChoices choices) j.succ≠[]→Fin (k+1)) (A0 ν : ℝ) (x : Fin k → HeatCircle) :
    factor L Q k (replaceSpace k p x) q choices chosen A0 ν=factor L Q k p q choices chosen A0 ν := by
  have hT : targets L k (replaceSpace k p x)=targets L k p := replaceSpace_targets L k p x
  simp only [factor,lowerWith_replaceSpace,upperWith_replaceSpace,hT]

/-- Summing absolute time factors gives one nonnegative scalar scale
without replacing any root clip or leaf gain by a coarser maximum. -/
def total (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k) (q A0 ν : ℝ) : ℝ :=
  ((GaussianAssignmentBlocks.assignments (m:=k+1) (List.finRange k)).map (fun choices =>
    |factor L Q k p q choices (ActualPointMomentSum.chosen choices) A0 ν|)).sum

theorem total_nonneg (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k) (q A0 ν : ℝ) :
    0 ≤ total L Q k p q A0 ν := by
  exact List.sum_nonneg (by intro x hx; obtain ⟨choices,_,rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)

theorem factor_le_total (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k) (q A0 ν : ℝ)
    (choices : List (Fin k×Fin (k+1)))
    (hc : choices∈GaussianAssignmentBlocks.assignments (m:=k+1) (List.finRange k)) :
    |factor L Q k p q choices (ActualPointMomentSum.chosen choices) A0 ν| ≤ total L Q k p q A0 ν := by
  apply List.single_le_sum
  · intro x hx
    obtain ⟨choices,_,rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _
  · exact List.mem_map.mpr ⟨choices,hc,rfl⟩

theorem total_replaceSpace (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (q A0 ν : ℝ) (x : Fin k → HeatCircle) :
    total L Q k (replaceSpace k p x) q A0 ν=total L Q k p q A0 ν := by
  simp only [total,factor_replaceSpace]

end SHE.PhysicalWordTimeScale
