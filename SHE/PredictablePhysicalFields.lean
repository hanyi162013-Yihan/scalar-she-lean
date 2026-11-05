module

public import SHE.FullPredictablePhysicalWord
public import SHE.GaussianProductAverageFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord
  PhysicalScoreChain OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution
open scoped BigOperators
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse covariances directions word

theorem old_covariances_measurable (c : Domain → ℝ) (hc : Measurable c) (k : ℕ) (j : Fin k) :
    Measurable (fun p : History P k => covariances L ((carrier L k).observations.observations p) c k p j) :=
  covariances_measurable L (carrier L k).observations (fun p => c p.2)
    (hc.comp measurable_snd) k id measurable_id j

theorem old_directions_measurable (k : ℕ) (j : Fin k) :
    Measurable (fun p : History P k => directions L ((carrier L k).observations.observations p) k p j) :=
  directions_measurable L (carrier L k).observations k id measurable_id j

set_option backward.isDefEq.respectTransparency true in
/-- The literal full fixed-old word average is Borel jointly in the
original history and the current mean. -/
theorem oldAverage_measurable (c : Domain → ℝ) (hc : Measurable c) (k : ℕ) :
    Measurable (fun p : History P k × WordRecursion.State (n+k) => oldAverage L c k p.1 p.2) := by
  unfold oldAverage
  exact GaussianProductAverageFields.weighted_average_measurable
    (X := History P k × WordRecursion.State (n+k)) (n := n+k) (r := k)
    (fun p j => covariances L ((carrier L k).observations.observations p.1) c k p.1 j)
    (fun j => (old_covariances_measurable L c hc k j).comp measurable_fst)
    (fun p j => directions L ((carrier L k).observations.observations p.1) k p.1 j)
    (fun j => (old_directions_measurable L k j).comp measurable_fst)
    (fun p => word L k p.1.1 (fun i => i) p.2)
    ((word_measurable L k (fun i => i)).comp (measurable_fst.fst.prodMk measurable_snd))
    Prod.snd measurable_snd

theorem windowCovariance_measurable (k : ℕ) : Measurable (windowCovariance L k) := by
  have hi : Measurable (initialTerminal L k) := L.terminal_measurable.comp (rootParameter_measurable k)
  let Z : VariableObservations.Family (History P k) (n+k) := {
    observations := fun p i => ⟨min ((carrier L k).observations.observations p i).stop (initialTerminal L k p),
      ((carrier L k).observations.observations p i).target,
      ((carrier L k).observations.observations p i).center⟩
    stop_measurable := fun i => ((carrier L k).observations.stop_measurable i).min hi
    target_measurable := (carrier L k).observations.target_measurable
    center_measurable := (carrier L k).observations.center_measurable }
  exact StoppedGaussianFields.covariance_measurable Z (R.reference_measurable.comp measurable_snd) measurable_const

theorem reserve_measurable (c : Domain → ℝ) (hc : Measurable c) (k : ℕ) :
    Measurable (reserve L c k) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  have he : (fun p => reserve L c k p i j) = fun p => windowCovariance L k p i j-
      ∑ l,covariances L ((carrier L k).observations.observations p) c k p l i j := by
    funext p
    simp only [reserve,Matrix.sub_apply,Matrix.sum_apply]
  rw [he]
  exact (windowCovariance_measurable L k).eval_matrix.sub
    (Finset.measurable_sum Finset.univ (fun l _ => (old_covariances_measurable L c hc k l).eval_matrix))

/-- Genuine jointly Borel predictable word evaluation at any measurable
dependent current mean. No separately AE family is evaluated diagonally. -/
theorem predictable_word_measurable (c : Domain → ℝ) (hc : Measurable c) (k : ℕ)
    (m : History P k → WordRecursion.State (n+k)) (hm : Measurable m) :
    Measurable (fun p => gaussianAverage (reserve L c k p) (oldAverage L c k p) (m p)) := by
  have hF : Measurable (fun p : History P k × WordRecursion.State (n+k) =>
      oldAverage L c k p.1 (m p.1+p.2)) :=
    (oldAverage_measurable L c hc k).comp
      (measurable_fst.prodMk ((hm.comp measurable_fst).add measurable_snd))
  exact (hF.stronglyMeasurable.integral_kernel_prod_right'
    (κ := GaussianScoreKernel.gaussianKernel (reserve L c k) (reserve_measurable L c hc k))).measurable

end SHE.PhysicalChainArrays
