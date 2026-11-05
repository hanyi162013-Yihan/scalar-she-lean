module

public import SHE.PhysicalAssignmentGapScale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.OldOnlyTimeFactor
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalChainArrays CoveredHistoryGeometry CoveredControlledLaw
  GaussianCoordinates GaussianFreshAssignments GaussianAssignmentBlocks
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

def chosen (k : ℕ) (p : History X k) (cs : List (Fin k×Fin (k+1)))
    (j : Fin k) (h : block cs j.succ≠[]) : Fin k :=
  MinimumGapChoice.blockChoice (lower L k p) (upper L k p) cs j.succ h

theorem chosen_mem (k : ℕ) (p : History X k) (cs : List (Fin k×Fin (k+1)))
    (j : Fin k) (h : block cs j.succ≠[]) : chosen L k p cs j h∈block cs j.succ :=
  MinimumGapChoice.blockChoice_mem _ _ _ _ _

def factor (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (cs : List (Fin k×Fin (k+1))) (A0 ν : ℝ) : ℝ :=
  VectorPhysicalRoot.scale cs 0 (lower L k p) (upper L k p) A0 ν (Q.lower/2) n*
    ∏ j,NativeAssignedLeafMoments.leafScale Q cs j.succ (lower L k p) (upper L k p)
      (targets L k p (leafIndex k (fun i=>i) j)) (chosen L k p cs j)

/-- Reserving the full remaining Gaussian instead of a front fraction
does not change ANY old root clip or minimum-gap rough gain. -/
theorem factor_eq_sharp (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (q A0 ν : ℝ) (cs : List (Fin k×Fin (k+1))) :
    factor L Q k p cs A0 ν=SharpWordTimeScale.factor L Q k p q cs A0 ν := by
  rw [PhysicalAssignmentGapScale.physical_factor_eq,←PhysicalAssignmentGapScale.plainFactor_eq]
  simp only [factor,PhysicalAssignmentGapScale.plainFactor,VectorPhysicalRoot.scale,
    NativeAssignedLeafMoments.leafScale,chosen,MinimumGapChoice.blockChoice,sub_zero]

end SHE.OldOnlyTimeFactor
