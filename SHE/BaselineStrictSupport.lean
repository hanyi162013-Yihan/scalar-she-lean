module

public import SHE.ActualBaselineTimeFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
noncomputable section

namespace SHE.PhysicalChainArrays
open MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalParentGeometry GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ} (L : Level R X n)

/-- Original nonstrict histories have a literal zero old direction;
every erased-baseline mark therefore vanishes, for any profile and
current mean, without a parameter-dependent exceptional set. -/
theorem baselineMark_zero_of_not_strict (c : StoppedGaussianFeatures.Domain→ℝ)
    (k : ℕ) (h : History X k) (hn : ¬StrictHistory L k h) (q : ℝ)
    (db : Fin k→ℝ) (m : WordRecursion.State (n+k)) : baselineMark L c k h q db m=0 := by
  classical
  obtain ⟨j,hj⟩:=exists_zero_direction_of_not_strict L ((carrier L k).observations.observations h) k h hn
  have hz (x : Fin k→WordRecursion.State (n+k)) :
      (∏ l,secondScore (covariances L ((carrier L k).observations.observations h) c k h l)
        (directions L ((carrier L k).observations.observations h) k h l) (x l))=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hj,secondScore_zero_direction]
  simp only [baselineMark,omittedAverage,WeightedBorelAverage.average,hz,zero_mul,integral_zero,
    gaussianAverage,mul_zero,Finset.sum_const_zero,neg_zero]

theorem baselinePoint_zero_of_not_strict (c : StoppedGaussianFeatures.Domain→ℝ)
    (k : ℕ) (h : History X k) (hn : ¬StrictHistory L k h) (q : ℝ)
    (db : Fin k→ℝ) (m : WordRecursion.State (n+k)) :
    ActualBaselineMarkFields.point L c k q db m h=0 := by
  unfold ActualBaselineMarkFields.point
  split_ifs
  · exact baselineMark_zero_of_not_strict L c k h hn q db m
  · rfl

end SHE.PhysicalChainArrays
