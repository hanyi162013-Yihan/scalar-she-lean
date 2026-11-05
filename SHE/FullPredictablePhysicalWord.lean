module

public import SHE.FullPhysicalWord
public import SHE.PhysicalPredictableRepresentation

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

def oldAverage (c : Domain → ℝ) (k : ℕ) (p : History P k) : WordRecursion.State (n+k) → ℝ :=
  WeightedBorelAverage.average
    (Measure.pi (fun j => multivariateGaussian (0 : WordRecursion.State (n+k))
      (covariances L ((carrier L k).observations.observations p) c k p j)))
    (fun x => ∏ j, MeasurableGaussianScores.secondScore
      (covariances L ((carrier L k).observations.observations p) c k p j)
      (directions L ((carrier L k).observations.observations p) k p j) (x j))
    (fun x => ∑ j,x j) (word L k p (fun i => i))

def reserve (c : Domain → ℝ) (k : ℕ) (p : History P k) :
    MeasurableGeneralizedInverse.Mat (n+k) :=
  windowCovariance L k p-∑ j,covariances L ((carrier L k).observations.observations p) c k p j

/-- The true predictable reference uses the complete conditional window
minus fixed-old intervals, with a jointly specified original full word.
There is no chain choice, covariance applicability, or score-support
hypothesis left in this all-order representation. -/
theorem predictable_eq_old_average_ae (c : Domain → ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0 < ell) (hb : ∀ z,ell ≤ c z ∧ c z ≤ R.reference z)
    (hages : ∀ p i,(L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      (reserve L c k p).PosSemidef ∧ ∀ z : WordRecursion.State (n+k),
        gaussianAverage (initialCovariance L k p) (UncutSmoothWords.test L k p) z =
          gaussianAverage (reserve L c k p) (oldAverage L c k p) z := by
  filter_upwards [predictable_representation_ae L c hc hell hb hages μ k] with p hp
  obtain ⟨chain,_,hphysical,hPSD,h⟩ := hp
  have hold := SHE.PhysicalChainArrays.Physical.old_eq L _ c chain hphysical
  have hd := SHE.PhysicalChainArrays.Physical.direction_eq L _ c chain hphysical
  have havg : chain.oldAverage = oldAverage L c k p := by
    unfold Chain.oldAverage oldAverage
    rw [hold,hd,fullTest_eq_word L chain]
  refine ⟨?_,fun z => ?_⟩
  · rw [hold] at hPSD
    exact hPSD
  · have hh := h z
    rw [hold,havg] at hh
    exact hh

end SHE.PhysicalChainArrays
