module

public import SHE.OmittedPhysicalIdentity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates PhysicalScoreChain
  StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
open scoped BigOperators
local instance actualBaselineAssignments_periodPos : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

/-- The exact baseline leg of the original weighted word: its (1/2)^k
normalization is present ONCE, and each derivative multiplies the
original old-score average with only that native leaf erased. -/
def baselineMark (c : Domain→ℝ) (k : ℕ) (p : History X k) (q : ℝ)
    (db : Fin k→ℝ) (mean : WordRecursion.State (n+k)) : ℝ :=
  -(∑ j,db j*omittedAverage L c k p q j mean)

/-- Literal agreement with the omitted-test term in the complete
three-leg weighted Gaussian FTC. -/
theorem baselineMark_eq_literal (c : Domain→ℝ) (k : ℕ) (p : History X k) (q : ℝ)
    (db : Fin k→ℝ) (mean : WordRecursion.State (n+k)) :
    baselineMark L c k p q db mean=-(1/2:ℝ)^k*∑ j,db j*
      gaussianAverage (fullResidualCovariance L c k p q)
        (WeightedBorelAverage.average
          (Measure.pi (fun l=>multivariateGaussian (0 : WordRecursion.State (n+k))
            (covariances L ((carrier L k).observations.observations p) c k p l)))
          (fun x=>∏ l,MeasurableGaussianScores.secondScore
            (covariances L ((carrier L k).observations.observations p) c k p l)
            (directions L ((carrier L k).observations.observations p) k p l) (x l)) (fun x=>∑ l,x l)
          (FiniteCenteredProduct.test (Finset.univ.erase j) (initial L k p (fun i=>i))
            (fun l z=>R.totalVariance (z (leafIndex k (fun i=>i) l))) (baseline L k p))) mean := by
  unfold baselineMark omittedAverage
  rw [Finset.mul_sum,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every original full-profile baseline derivative is represented by
its genuine old Gaussian assignment sum. No coefficient derivative,
new covariance fraction, or lower-order word is inserted. -/
theorem baseline_mark_assignment_ae (c : Domain→ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0<ell) (hb : ∀ z,ell≤c z ∧ c z≤R.reference z)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ q : ℝ,∀ db : Fin k→ℝ,∀ mean : WordRecursion.State (n+k),
      baselineMark L c k p q db mean=-(1/2:ℝ)^k*
        ∑ j,db j*((assignments (m:=k+1) (List.finRange k)).map (fun choices=>∫ x,
          omittedAssignedWord L c k p mean choices j x ∂fullAssignedMeasure L c k p q)).sum := by
  filter_upwards [omitted_average_assignment_ae L c hc hell hb hages μ k] with p hp
  intro q db mean
  have he (j : Fin k) := (hp q mean j).2
  unfold baselineMark
  simp_rw [he]
  rw [Finset.mul_sum,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end SHE.PhysicalChainArrays

namespace SHE.ControlledBaselineAssignments
open Set Filter MeasureTheory ProbabilityTheory Real StoppedFourier WordRecursion CutoffWordLevel
  CutoffWordHistories CutoffCarriers GaussianCoordinates PhysicalChainArrays ControlledOldIntervals
  GaussianAssignmentBlocks StoppedGaussianFeatures
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {n : ℕ}

def derivatives (P : CanonicalCovariance.ProfileParameters) (ha : SmoothCylinders.BoundedSmooth P.coefficient)
    (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
    (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X n)
    (k : ℕ) (p : History X k) (j : Fin k) : ℝ :=
  ControlledProfile.derivative P Λ u dir ((lower L k p j,space k p j),θ)

theorem actual_baseline_mark_assignment_ae (P : CanonicalCovariance.ProfileParameters)
    (ha : SmoothCylinders.BoundedSmooth P.coefficient) (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
    (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X n)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure (ControlledWordLevel.referenceData P ha Λ u dir θ) μ k,
      ∀ q : ℝ,∀ mean : WordRecursion.State (n+k),
      baselineMark L (referenceProfile P Λ u dir) k p q (derivatives P ha Λ u dir θ L k p) mean=
        -(1/2:ℝ)^k*∑ j,derivatives P ha Λ u dir θ L k p j*
          ((assignments (m:=k+1) (List.finRange k)).map (fun choices=>∫ x,
            omittedAssignedWord L (referenceProfile P Λ u dir) k p mean choices j x
              ∂fullAssignedMeasure L (referenceProfile P Λ u dir) k p q)).sum := by
  have hb (r : Domain) : fraction P*P.lower≤referenceProfile P Λ u dir r ∧
      referenceProfile P Λ u dir r≤(ControlledWordLevel.referenceData P ha Λ u dir θ).reference r :=
    ⟨(referenceProfile_bounds P Λ u dir r).1,
      (referenceProfile_bounds P Λ u dir r).2.trans ((half_le_self P.lower_pos.le).trans
        (ControlledProfile.profile_bounds P Λ u dir (θ,r)).1)⟩
  filter_upwards [baseline_mark_assignment_ae L _ (referenceProfile_measurable P Λ u dir)
    (mul_pos (fraction_pos P) P.lower_pos) hb hages μ k] with p hp
  exact fun q mean=>hp q (derivatives P ha Λ u dir θ L k p) mean

end SHE.ControlledBaselineAssignments
