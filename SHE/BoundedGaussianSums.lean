module

public import SHE.WeightedBorelAverage
public import SHE.GaussianConvolution

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.GaussianConvolution
open Set MeasureTheory ProbabilityTheory GaussianIncrement
open scoped BigOperators

/-- Finite sums of genuinely bounded Borel tests pass through the actual
possibly singular Gaussian law. No smoothness or positive rank is needed. -/
theorem gaussianAverage_finite {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (F : ℕ→State n→ℝ) (hF : ∀ j,Measurable (F j)) (B : ℕ→ℝ)
    (hb : ∀ j z,|F j z|≤B j) (s : Finset ℕ) :
    gaussianAverage A (fun z=>∑ j∈s,F j z)=∑ j∈s,gaussianAverage A (F j) := by
  funext m
  simp only [gaussianAverage,Finset.sum_apply]
  apply integral_finsetSum
  intro j hj
  exact (integrable_const (B j)).mono'
    (((hF j).comp (measurable_const.add measurable_id)).aestronglyMeasurable)
    (ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs] using hb j (m+z)))
end SHE.GaussianConvolution
