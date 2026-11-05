module

public import SHE.PhysicalWordTimeScale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.PhysicalWordTimeScale
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalChainArrays CoveredHistoryGeometry CoveredControlledLaw
  GaussianCoordinates GaussianFreshAssignments GaussianAssignmentBlocks
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

theorem lowerWith_measurable (k : ℕ) (q : ℝ) (j : Fin (k+1)) :
    Measurable (fun p : History X k => lowerWith L k p q j) :=
  Fin.cases measurable_const (lower_measurable L k) j

theorem upperWith_measurable (k : ℕ) (j : Fin (k+1)) :
    Measurable (fun p : History X k => upperWith L k p j) :=
  Fin.cases (carrier L k).terminal_measurable (upper_measurable L k) j

/-- The full preserved root/rough time factor is Borel on actual history
space, including inactive histories and all boundary time coordinates. -/
theorem factor_measurable (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (q : ℝ)
    (choices : List (Fin k×Fin (k+1)))
    (chosen : ∀ j : Fin k,block (liftChoices choices) j.succ≠[]→Fin (k+1)) (A0 ν : ℝ) :
    Measurable (fun p : History X k => factor L Q k p q choices chosen A0 ν) := by
  have hroot : Measurable (fun p : History X k =>
      VectorPhysicalRoot.scale (liftChoices choices) 0 (lowerWith L k p q) (upperWith L k p) A0 ν (Q.lower/2) n) := by
    unfold VectorPhysicalRoot.scale
    apply measurable_const.mul
    apply Finset.measurable_prod
    intro j _
    exact measurable_const.min (((upperWith_measurable L k _).sub
      (lowerWith_measurable L k q _)).pow_const (1/4:ℝ) |>.const_mul _)
  have hleaf (j : Fin k) : Measurable (fun p : History X k =>
      NativeAssignedLeafMoments.leafScale Q (liftChoices choices) j.succ
        (lowerWith L k p q) (upperWith L k p) (targets L k p (leafIndex k (fun i => i) j)) (chosen j)) := by
    unfold NativeAssignedLeafMoments.leafScale
    split_ifs with h
    · exact measurable_const.mul
        (((carrier L k).observations.target_measurable (leafIndex k (fun i => i) j)).pow_const (Q.exponent/4))
    · exact measurable_const.mul (((upperWith_measurable L k _).sub
        (lowerWith_measurable L k q _)).pow_const (Q.exponent/4))
  exact hroot.mul (Finset.measurable_prod Finset.univ (fun j _ => hleaf j))

theorem total_measurable (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (q A0 ν : ℝ) :
    Measurable (fun p : History X k => total L Q k p q A0 ν) := by
  unfold total
  rw [show (fun p : History X k => ((assignments (m:=k+1) (List.finRange k)).map (fun choices =>
      |factor L Q k p q choices (ActualPointMomentSum.chosen choices) A0 ν|)).sum)=
      fun p => ∑ i : Fin (assignments (m:=k+1) (List.finRange k)).length,
        |factor L Q k p q ((assignments (m:=k+1) (List.finRange k)).get i)
          (ActualPointMomentSum.chosen _) A0 ν| from
      funext (fun _ => FiniteAssignmentMoments.map_sum_eq_fin _ _)]
  exact Finset.measurable_sum Finset.univ (fun i _ =>
    continuous_abs.measurable.comp (factor_measurable L Q k q _ _ A0 ν))

end SHE.PhysicalWordTimeScale
