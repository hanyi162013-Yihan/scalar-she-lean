module

public import Mathlib.Probability.BrownianMotion.Basic
public import KolmogorovExtension4.KolmogorovExtension
public import Mathlib.Probability.HasLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.CanonicalBrownianMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The actual probability law of the raw scalar Brownian coordinate
process. Its extension is constructed from the existing Gaussian finite
laws by the proved Kolmogorov extension theorem. -/
def measure : Measure (ℝ≥0 → ℝ) :=
  projectiveLimit BrownianReal.projectiveFamily BrownianReal.isProjectiveMeasureFamily_projectiveFamily

instance probability : IsProbabilityMeasure measure :=
  isProbabilityMeasure_projectiveLimit BrownianReal.isProjectiveMeasureFamily_projectiveFamily

theorem projective : IsProjectiveLimit measure BrownianReal.projectiveFamily :=
  isProjectiveLimit_projectiveLimit BrownianReal.isProjectiveMeasureFamily_projectiveFamily

/-- Every finite restriction has precisely the existing centered
Gaussian Brownian finite law, including repeated or zero times. -/
theorem finite_law (I : Finset ℝ≥0) : HasLaw I.restrict (BrownianReal.projectiveFamily I) measure where
  map_eq := projective I

def process (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ := ω t

/-- The constructed raw coordinate is pre-Brownian in the standard
mathlib sense, so all its Gaussian and independent-increment theorems apply. -/
theorem preBrownian : IsPreBrownianReal process measure where
  hasLaw I := finite_law I

theorem measurable_process (t : ℝ≥0) : Measurable (process t) := measurable_pi_apply t

theorem eval_law (t : ℝ≥0) : HasLaw (process t) (gaussianReal 0 t) measure := preBrownian.hasLaw_eval t

/-- Native raw Brownian covariances have their exact physical clock. -/
theorem covariance (s t : ℝ≥0) : cov[fun x => x s,fun x => x t;measure]=min (s : ℝ) (t : ℝ) := by
  have hh := (finite_law {s,t}).covariance_fun_comp
    (f := Function.eval ⟨s,by simp⟩) (g := Function.eval ⟨t,by simp⟩)
    (Measurable.aemeasurable (by fun_prop)) (Measurable.aemeasurable (by fun_prop))
  simpa [Function.comp_def,Function.eval,Finset.restrict_def,BrownianReal.covariance_eval_projectiveFamily] using hh

end SHEStochastic.CanonicalBrownianMeasure
