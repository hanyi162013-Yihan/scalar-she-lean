module

public import SHE.ControlledFutureTransfer
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FiniteCenteredProduct
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
open scoped BigOperators
variable {ι X : Type*} [DecidableEq ι]

def test (s : Finset ι) (R : X → ℝ) (a : ι → X → ℝ) (b : ι → ℝ) (z : X) : ℝ :=
  R z * ∏ i ∈ s, (a i z - b i)

def monomial (R : X → ℝ) (a : ι → X → ℝ) (s : Finset ι) (z : X) : ℝ :=
  R z * ∏ i ∈ s, a i z

def coefficient (s t : Finset ι) (b : ι → ℝ) : ℝ := ∏ i ∈ s \ t, -b i

def coefficientDerivative (s t : Finset ι) (b db : ι → ℝ) : ℝ :=
  ∑ i ∈ s \ t, (∏ j ∈ (s \ t).erase i, -b j) * (-db i)

theorem expansion (s : Finset ι) (R : X → ℝ) (a : ι → X → ℝ) (b : ι → ℝ) (z : X) :
    test s R a b z = ∑ t ∈ s.powerset, coefficient s t b * monomial R a t z := by
  unfold test coefficient monomial
  simp_rw [sub_eq_add_neg]
  rw [Finset.prod_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem coefficient_hasDerivAt (s t : Finset ι) (b : ι → ℝ → ℝ) (db : ι → ℝ)
    (θ : ℝ) (hb : ∀ i ∈ s, HasDerivAt (b i) (db i) θ) :
    HasDerivAt (fun η => coefficient s t (fun i => b i η))
      (coefficientDerivative s t (fun i => b i θ) db) θ := by
  convert HasDerivAt.fun_finsetProd (u := s \ t)
    (fun i hi => (hb i (Finset.mem_sdiff.mp hi).1).neg) using 1 <;>
    simp only [coefficient, coefficientDerivative, smul_eq_mul, Pi.neg_apply]

/-- Every moving deterministic baseline contributes once, with a minus sign;
the root and all other leaves remain intact. -/
theorem test_hasDerivAt (s : Finset ι) (R : X → ℝ) (a : ι → X → ℝ)
    (b : ι → ℝ → ℝ) (db : ι → ℝ) (θ : ℝ)
    (hb : ∀ i ∈ s, HasDerivAt (b i) (db i) θ) (z : X) :
    HasDerivAt (fun η => test s R a (fun i => b i η) z)
      (-(∑ i ∈ s, db i * test (s.erase i) R a (fun j => b j θ) z)) θ := by
  have h := (HasDerivAt.fun_finsetProd (u := s)
    (fun i hi => (hasDerivAt_const θ (a i z)).sub (hb i hi))).const_mul (R z)
  convert h using 1
  · rfl
  · simp only [smul_eq_mul, zero_sub, test, Finset.mul_sum, Pi.sub_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- The finite expansion differentiates to exactly the explicit omitted-leaf
sum. This identity is pointwise and does not differentiate a rough leaf. -/
theorem derivative_expansion (s : Finset ι) (R : X → ℝ) (a : ι → X → ℝ)
    (b : ι → ℝ → ℝ) (db : ι → ℝ) (θ : ℝ)
    (hb : ∀ i ∈ s, HasDerivAt (b i) (db i) θ) (z : X) :
    (∑ t ∈ s.powerset, coefficientDerivative s t (fun i => b i θ) db * monomial R a t z) =
      -(∑ i ∈ s, db i * test (s.erase i) R a (fun j => b j θ) z) := by
  have h := HasDerivAt.fun_sum (u := s.powerset)
    (fun t ht => (coefficient_hasDerivAt s t b db θ hb).mul_const (monomial R a t z))
  have he : (fun η => ∑ t ∈ s.powerset, coefficient s t (fun i => b i η) * monomial R a t z) =
      fun η => test s R a (fun i => b i η) z := by
    funext η
    exact (expansion s R a (fun i => b i η) z).symm
  rw [he] at h
  exact h.unique (test_hasDerivAt s R a b db θ hb z)

theorem measurable_monomial [MeasurableSpace X] (s : Finset ι) (R : X → ℝ)
    (a : ι → X → ℝ) (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i)) :
    Measurable (monomial R a s) := hR.mul (Finset.measurable_prod s ha)

theorem measurable_test [MeasurableSpace X] (s : Finset ι) (R : X → ℝ)
    (a : ι → X → ℝ) (b : ι → ℝ) (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i)) :
    Measurable (test s R a b) :=
  hR.mul (Finset.measurable_prod s (fun i hi => (ha i hi).sub measurable_const))

theorem monomial_bound (s : Finset ι) (R : X → ℝ) (a : ι → X → ℝ)
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hR : ∀ z, |R z| ≤ B) (ha : ∀ i ∈ s, ∀ z, |a i z| ≤ M i) (z : X) :
    |monomial R a s z| ≤ B * ∏ i ∈ s, M i := by
  simp only [monomial, abs_mul, Finset.abs_prod]
  exact mul_le_mul (hR z) (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
    (fun i hi => ha i hi z)) (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) hB

theorem test_bound (s : Finset ι) (R : X → ℝ) (a : ι → X → ℝ) (b : ι → ℝ)
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hR : ∀ z, |R z| ≤ B) (ha : ∀ i ∈ s, ∀ z, |a i z| ≤ M i) (z : X) :
    |test s R a b z| ≤ B * ∏ i ∈ s, (M i + |b i|) := by
  apply monomial_bound s R (fun i z => a i z - b i) B (fun i => M i + |b i|) hB
    (fun i hi => add_nonneg (hM i hi) (abs_nonneg _)) hR
  intro i hi z
  exact (abs_sub _ _).trans (add_le_add (ha i hi z) le_rfl)

theorem integrable_bounded {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ]
    (f : E → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ x, |f x| ≤ B) : Integrable f μ :=
  (integrable_const B).mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))

theorem average_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f : State n → ℝ)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) (m : State n) : |gaussianAverage A f m| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := multivariateGaussian (0 : State n) A)
    (f := fun y => f (m + y)) (C := B)
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using hb (m + y)))
  simpa only [gaussianAverage, Real.norm_eq_abs, probReal_univ, mul_one] using h

theorem average_expansion {n : ℕ} (s : Finset ι) (A : Matrix (Fin n) (Fin n) ℝ)
    (R : State n → ℝ) (a : ι → State n → ℝ) (b : ι → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hRb : ∀ z, |R z| ≤ B) (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i) (m : State n) :
    gaussianAverage A (test s R a b) m =
      ∑ t ∈ s.powerset, coefficient s t b * gaussianAverage A (monomial R a t) m := by
  unfold gaussianAverage
  simp_rw [expansion]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul]
  · intro t ht
    have hts := Finset.mem_powerset.mp ht
    exact (integrable_bounded _ _ ((measurable_monomial t R a hR
      (fun i hi => ha i (hts hi))).comp (measurable_const.add measurable_id))
      (B * ∏ i ∈ t, M i)
      (fun z => monomial_bound t R a B M hB (fun i hi => hM i (hts hi)) hRb
        (fun i hi => hab i (hts hi)) (m + z))).const_mul _

/-- Integrating the exact finite coefficient derivative gives precisely all
moving-baseline terms, including products with any number of other leaves. -/
theorem average_derivative_expansion {n : ℕ} (s : Finset ι)
    (A : Matrix (Fin n) (Fin n) ℝ) (R : State n → ℝ) (a : ι → State n → ℝ)
    (b : ι → ℝ → ℝ) (db : ι → ℝ) (θ : ℝ)
    (hb : ∀ i ∈ s, HasDerivAt (b i) (db i) θ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hRb : ∀ z, |R z| ≤ B) (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i) (m : State n) :
    (∑ t ∈ s.powerset, coefficientDerivative s t (fun i => b i θ) db *
      gaussianAverage A (monomial R a t) m) =
      -(∑ i ∈ s, db i * gaussianAverage A (test (s.erase i) R a (fun j => b j θ)) m) := by
  have hm (t : Finset ι) (ht : t ⊆ s) : Integrable (fun y => monomial R a t (m + y))
      (multivariateGaussian 0 A) :=
    integrable_bounded _ _ ((measurable_monomial t R a hR (fun i hi => ha i (ht hi))).comp
      (measurable_const.add measurable_id)) (B * ∏ i ∈ t, M i)
      (fun z => monomial_bound t R a B M hB (fun i hi => hM i (ht hi)) hRb
        (fun i hi => hab i (ht hi)) (m + z))
  have ht (i : ι) : Integrable (fun y => test (s.erase i) R a (fun j => b j θ) (m + y))
      (multivariateGaussian 0 A) :=
    integrable_bounded _ _ ((measurable_test _ R a _ hR
      (fun j hj => ha j (Finset.mem_of_mem_erase hj))).comp
      (measurable_const.add measurable_id)) _
      (fun z => test_bound _ R a _ B M hB
        (fun j hj => hM j (Finset.mem_of_mem_erase hj)) hRb
        (fun j hj => hab j (Finset.mem_of_mem_erase hj)) (m + z))
  have he := congrArg (fun f : State n → ℝ => ∫ y, f (m + y) ∂multivariateGaussian 0 A)
    (funext (derivative_expansion s R a b db θ hb))
  simp only [integral_neg] at he
  rw [integral_finsetSum s.powerset (fun t ht => (hm t (Finset.mem_powerset.mp ht)).const_mul _),
    integral_finsetSum s (fun i hi => (ht i).const_mul _)] at he
  simpa only [integral_const_mul, gaussianAverage] using he

end SHE.FiniteCenteredProduct
