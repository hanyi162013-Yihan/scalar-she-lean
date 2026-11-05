module

public import SHE.WeightedCenteredExpansion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.WeightedCenteredExpansion
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  FiniteCenteredProduct
open scoped BigOperators
variable {X ι : Type*} [MeasurableSpace X] [DecidableEq ι] {n : ℕ}

/-- The same integrable Gaussian score marks the entire old-weighted
centered product. This identity preserves all centering gains. -/
theorem integral_score_expansion (s : Finset ι) (μ : Measure X) [SFinite μ]
    (w : X → ℝ) (hw : Integrable w μ) (hwm : Measurable w)
    (shift : X → State n) (hs : Measurable shift)
    (A : Matrix (Fin n) (Fin n) ℝ) (R : State n → ℝ) (a : ι → State n → ℝ) (b : ι → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s,Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s,0 ≤ M i)
    (hRb : ∀ z,|R z| ≤ B) (hab : ∀ i ∈ s,∀ z,|a i z| ≤ M i)
    (m : State n) (V : State n → ℝ) (hV : Integrable V (multivariateGaussian 0 A)) :
    (∫ y,WeightedBorelAverage.average μ w shift (test s R a b) (m+y)*V y ∂multivariateGaussian 0 A)=
      ∑ t ∈ s.powerset,coefficient s t b*
        (∫ y,WeightedBorelAverage.average μ w shift (monomial R a t) (m+y)*V y
          ∂multivariateGaussian 0 A) := by
  have hp (y : State n) : WeightedBorelAverage.average μ w shift (test s R a b) (m+y)*V y=
      ∑ t ∈ s.powerset,coefficient s t b*
        (WeightedBorelAverage.average μ w shift (monomial R a t) (m+y)*V y) := by
    rw [WeightedBorelAverage.test_expansion s μ w hw shift hs R a b hR ha B M hB hM hRb hab,
      Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => mul_assoc _ _ _)
  simp_rw [hp]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro t ht
    have hts := Finset.mem_powerset.mp ht
    have hm := measurable_monomial t R a hR (fun i hi => ha i (hts hi))
    have hb (z : State n) := WeightedBorelAverage.bound μ w hw shift hs _ hm (B*∏ i ∈ t,M i)
      (mul_nonneg hB (Finset.prod_nonneg (fun i hi => hM i (hts hi))))
      (monomial_bound t R a B M hB (fun i hi => hM i (hts hi)) hRb (fun i hi => hab i (hts hi))) z
    exact (hV.bdd_mul ((WeightedBorelAverage.measurable μ w hwm shift hs _ hm).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ (fun y => by
        simpa only [Real.norm_eq_abs,Function.comp_apply,Pi.add_apply,id_eq] using hb (m+y)))).const_mul _

end SHE.WeightedCenteredExpansion
