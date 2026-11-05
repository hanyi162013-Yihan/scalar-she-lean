module

public import SHE.WeightedGaussianWord

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.WeightedCenteredExpansion
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  FiniteCenteredProduct
open scoped BigOperators
variable {X ι : Type*} [MeasurableSpace X] [DecidableEq ι] {n : ℕ}

/-- Every baseline derivative remains one explicit omitted-leaf term,
even after the original integrable old score has been averaged. -/
theorem baseline_expansion (s : Finset ι) (μ : Measure X) [SFinite μ]
    (w : X → ℝ) (hw : Integrable w μ) (hwm : Measurable w)
    (shift : X → State n) (hs : Measurable shift)
    (A : Matrix (Fin n) (Fin n) ℝ) (R : State n → ℝ) (a : ι → State n → ℝ)
    (b : ι → ℝ → ℝ) (db : ι → ℝ) (θ : ℝ)
    (hb : ∀ i ∈ s,HasDerivAt (b i) (db i) θ)
    (hR : Measurable R) (ha : ∀ i ∈ s,Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s,0 ≤ M i)
    (hRb : ∀ z,|R z| ≤ B) (hab : ∀ i ∈ s,∀ z,|a i z| ≤ M i) (m : State n) :
    (∑ t ∈ s.powerset,coefficientDerivative s t (fun i => b i θ) db*
      gaussianAverage A (WeightedBorelAverage.average μ w shift (monomial R a t)) m)=
      -(∑ i ∈ s,db i*gaussianAverage A
        (WeightedBorelAverage.average μ w shift (test (s.erase i) R a (fun j => b j θ))) m) := by
  have hm (t : Finset ι) (ht : t ⊆ s) : Measurable (monomial R a t) :=
    measurable_monomial t R a hR (fun i hi => ha i (ht hi))
  have hmb (t : Finset ι) (ht : t ⊆ s) (z : State n) : |monomial R a t z| ≤ B*∏ i ∈ t,M i :=
    monomial_bound t R a B M hB (fun i hi => hM i (ht hi)) hRb (fun i hi => hab i (ht hi)) z
  have htm (i : ι) : Measurable (test (s.erase i) R a (fun j => b j θ)) :=
    measurable_test _ R a _ hR (fun j hj => ha j (Finset.mem_of_mem_erase hj))
  have htb (i : ι) (z : State n) : |test (s.erase i) R a (fun j => b j θ) z| ≤
      B*∏ j ∈ s.erase i,(M j+|b j θ|) :=
    test_bound _ R a _ B M hB (fun j hj => hM j (Finset.mem_of_mem_erase hj)) hRb
      (fun j hj => hab j (Finset.mem_of_mem_erase hj)) z
  have hp (z : State n) :
      (∑ t ∈ s.powerset,coefficientDerivative s t (fun i => b i θ) db*
        WeightedBorelAverage.average μ w shift (monomial R a t) z)=
      -(∑ i ∈ s,db i*WeightedBorelAverage.average μ w shift
        (test (s.erase i) R a (fun j => b j θ)) z) := by
    have he := congrArg (fun F : State n → ℝ => WeightedBorelAverage.average μ w shift F z)
      (funext (derivative_expansion s R a b db θ hb))
    rw [WeightedBorelAverage.neg] at he
    rw [WeightedBorelAverage.finset_sum s.powerset μ w hw shift hs
      (fun t y => coefficientDerivative s t (fun i => b i θ) db*monomial R a t y)
      (fun t ht => measurable_const.mul (hm t (Finset.mem_powerset.mp ht)))
      (fun t => |coefficientDerivative s t (fun i => b i θ) db| * (B*∏ i ∈ t,M i))
      (fun t ht y => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hmb t (Finset.mem_powerset.mp ht) y) (abs_nonneg _)),
      WeightedBorelAverage.finset_sum s μ w hw shift hs
      (fun i y => db i*test (s.erase i) R a (fun j => b j θ) y)
      (fun i _ => measurable_const.mul (htm i))
      (fun i => |db i| * (B*∏ j ∈ s.erase i,(M j+|b j θ|)))
      (fun i _ y => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (htb i y) (abs_nonneg _))] at he
    simpa only [WeightedBorelAverage.const_mul] using he
  have hiG (t : Finset ι) (ht : t ⊆ s) : Integrable
      (fun y => WeightedBorelAverage.average μ w shift (monomial R a t) (m+y))
      (multivariateGaussian 0 A) :=
    integrable_bounded _ _
      ((WeightedBorelAverage.measurable μ w hwm shift hs _ (hm t ht)).comp
        (measurable_const.add measurable_id)) ((B*∏ i ∈ t,M i)*∫ x,|w x| ∂μ)
      (fun y => WeightedBorelAverage.bound μ w hw shift hs _ (hm t ht) _
        (mul_nonneg hB (Finset.prod_nonneg (fun i hi => hM i (ht hi)))) (hmb t ht) _)
  have hiH (i : ι) : Integrable
      (fun y => WeightedBorelAverage.average μ w shift (test (s.erase i) R a (fun j => b j θ)) (m+y))
      (multivariateGaussian 0 A) :=
    integrable_bounded _ _
      ((WeightedBorelAverage.measurable μ w hwm shift hs _ (htm i)).comp
        (measurable_const.add measurable_id)) ((B*∏ j ∈ s.erase i,(M j+|b j θ|))*∫ x,|w x| ∂μ)
      (fun y => WeightedBorelAverage.bound μ w hw shift hs _ (htm i) _
        (mul_nonneg hB (Finset.prod_nonneg (fun j hj => add_nonneg
          (hM j (Finset.mem_of_mem_erase hj)) (abs_nonneg _)))) (htb i) _)
  have he := congrArg (fun F : State n → ℝ => ∫ y,F (m+y) ∂multivariateGaussian 0 A) (funext hp)
  simp only [integral_neg] at he
  rw [integral_finsetSum s.powerset (fun t ht => (hiG t (Finset.mem_powerset.mp ht)).const_mul _),
    integral_finsetSum s (fun i _ => (hiH i).const_mul _)] at he
  simpa only [integral_const_mul,gaussianAverage] using he

end SHE.WeightedCenteredExpansion
