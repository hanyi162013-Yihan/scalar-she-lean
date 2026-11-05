module

public import SHE.NativePointAssignmentMoments
public import SHE.FiniteAssignmentMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section

namespace SHE.ActualPointMomentSum
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  PhysicalChainArrays OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

def chosen {k : ℕ} (choices : List (Fin k×Fin (k+1))) (j : Fin k)
    (h : block (liftChoices choices) j.succ≠[]) : Fin (k+1) :=
  (block (liftChoices choices) j.succ).head h

theorem chosen_mem {k : ℕ} (choices : List (Fin k×Fin (k+1))) (j : Fin k)
    (h : block (liftChoices choices) j.succ≠[]) : chosen choices j h∈block (liftChoices choices) j.succ :=
  List.head_mem h

theorem choices_nodup (k : ℕ) (choices : List (Fin k×Fin (k+1)))
    (hc : choices∈assignments (m:=k+1) (List.finRange k)) : (choices.map Prod.fst).Nodup := by
  rw [assignment_coordinates _ _ hc]
  exact List.nodup_finRange k

theorem root_length_le (k : ℕ) (choices : List (Fin k×Fin (k+1)))
    (hc : choices∈assignments (m:=k+1) (List.finRange k)) :
    (block (liftChoices choices) 0).length≤k := by
  rw [block_lift,List.length_map]
  simpa only [Fintype.card_fin] using
    (block_nodup choices (choices_nodup k choices hc) 0).length_le_card

theorem assignment_average_measurable (L : CutoffWordLevel.Level R X n) (c : Domain→ℝ)
    (k : ℕ) (p : History X k) (q : ℝ) (direction : WordRecursion.State (n+k))
    (mean : Ω→WordRecursion.State (n+k)) (hm : Measurable mean)
    (choices : List (Fin k×Fin (k+1))) :
    Measurable (fun ω => ∫ x,rangeAssignedWord L c k p q direction (mean ω) choices x
      ∂terminalAssignedMeasure L c k p q) := by
  haveI : IsProbabilityMeasure (terminalAssignedMeasure L c k p q) := by
    dsimp only [terminalAssignedMeasure]
    infer_instance
  let Z := (carrier L k).observations.observations p
  let A := GaussianFreshFraction.covariances (intervalCovariance Z c q ((carrier L k).terminal p)) (covariances L Z c k p)
  let D : Fin (k+1)→WordRecursion.State (n+k) := Fin.cons direction (directions L Z k p)
  have hf : Measurable (fun z : Ω×((Fin (k+1)→WordRecursion.State (n+k))×WordRecursion.State (n+k)) =>
      rangeAssignedWord L c k p q direction (mean z.1) choices z.2) := by
    exact NativeFirstScoreWordMoments.word_measurable R.totalVariance R.totalVariance_smooth.smooth.continuous.measurable
      flags A D (liftChoices choices) (L.test (rootParameter k p)) (L.test_uniform.smooth _).continuous.measurable
      mean hm (rootSelector k (fun i => i)) (leafIndex k (fun i => i)) (baseline L k p)
  exact (hf.stronglyMeasurable.integral_prod_right').measurable

end SHE.ActualPointMomentSum
