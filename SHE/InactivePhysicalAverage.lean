module

public import SHE.ActualCovarianceMarkFields
public import SHE.PhysicalParentGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain MeasurableGaussianScores StoppedGaussianFeatures
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n N : ℕ}
variable (L : Level R X n)

/-- Every nonordered original history contains a literal zero old score
direction. No Gaussian nondegeneracy or almost-everywhere support is needed. -/
theorem exists_zero_direction_of_not_strict (Z : Fin N→Observation)
    (k : ℕ) (p : History X k) (hp : ¬StrictHistory L k p) :
    ∃ j : Fin k,directions L Z k p j=0 := by
  classical
  induction k with
  | zero => exact False.elim (hp trivial)
  | succ k ih =>
    by_cases hprev : StrictHistory L k p.1
    · have hn : ¬Interior L k p := fun hi=>hp ⟨hprev,hi⟩
      refine ⟨0,?_⟩
      simp only [directions,Fin.cases_zero,direction,hn,ite_false]
    · obtain ⟨j,hj⟩ := ih p.1 hprev
      exact ⟨j.succ,hj⟩

theorem secondScore_zero_direction (A : MeasurableGeneralizedInverse.Mat N)
    (y : WordRecursion.State N) : secondScore A 0 y=0 := by
  simp only [secondScore,firstScore,scoreVariance,coefficient,map_zero,inner_zero_left,
    zero_pow (by norm_num : (2:ℕ)≠0),sub_zero]

/-- All old-score averaged words vanish identically outside the strict
history domain, so extending their spatial/time integrals by zero is exact. -/
theorem oldAverage_zero_of_not_strict (c : Domain→ℝ) (k : ℕ)
    (p : History X k) (hp : ¬StrictHistory L k p) : oldAverage L c k p=0 := by
  classical
  obtain ⟨j,hj⟩ := exists_zero_direction_of_not_strict L
    ((carrier L k).observations.observations p) k p hp
  have hz (x : Fin k→WordRecursion.State (n+k)) :
      (∏ l,secondScore (covariances L ((carrier L k).observations.observations p) c k p l)
        (directions L ((carrier L k).observations.observations p) k p l) (x l))=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hj,secondScore_zero_direction]
  funext z
  simp only [oldAverage,WeightedBorelAverage.average,hz,zero_mul,integral_zero,Pi.zero_apply]

end SHE.PhysicalChainArrays
