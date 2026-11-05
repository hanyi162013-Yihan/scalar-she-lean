module

public import SHE.CovarianceMatrix

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.GaussianConvolution
open MeasureTheory ProbabilityTheory SHE.WordRecursion SHE.CovarianceMatrix
open scoped ENNReal MatrixOrder MeasureTheory

/-- Exact convolution of actual finite Gaussian laws, valid also for
singular positive semidefinite covariance matrices. -/
theorem multivariateGaussian_convolution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (multivariateGaussian (0:State n) A) ∗ (multivariateGaussian (0:State n) B) =
      multivariateGaussian (0:State n) (A+B) := by
  apply Measure.ext_of_charFun
  ext x
  rw [charFun_conv,charFun_multivariateGaussian hA,charFun_multivariateGaussian hB,
    charFun_multivariateGaussian (hA.add hB),← Complex.exp_add]
  simp only [inner_zero_right,Complex.ofReal_zero,zero_mul,zero_sub,
    Matrix.add_mulVec,dotProduct_add,Complex.ofReal_add]
  ring_nf

def gaussianAverage {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (F : State n → ℝ) (z : State n) : ℝ :=
  ∫ x : State n,F (z+x) ∂multivariateGaussian 0 A

theorem gaussianAverage_composition {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (F : State n → ℝ)
    (hF : Measurable F) {K : ℝ} (hK : ∀ z,|F z| ≤ K) (z : State n) :
    gaussianAverage A (fun y => gaussianAverage B F y) z = gaussianAverage (A+B) F z := by
  have hi : Integrable (fun x : State n => F (z+x))
      ((multivariateGaussian (0:State n) A) ∗ (multivariateGaussian (0:State n) B)) := by
    apply (integrable_const K).mono' (hF.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs,Function.comp_apply,Pi.add_apply,id_eq] using hK (z+x))
  have hh := integral_conv hi
  rw [multivariateGaussian_convolution A B hA hB] at hh
  unfold gaussianAverage
  simpa only [add_assoc] using hh.symm

theorem covariance_gaussian_convolution {n : ℕ} (c : ℝ × SHE.StoppedFourier.HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) {δ M q r s : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hqr : q ≤ r) (hrs : r ≤ s)
    (hgap : ∀ i,δ ≤ (Z i).target-s)
    (hbound : ∀ t ∈ Set.Icc q s,∀ x,|c (t,x)| ≤ M)
    (hnonneg : ∀ t ∈ Set.Icc q s,∀ x,0 ≤ c (t,x)) :
    (multivariateGaussian (0:State n) (covariance c Z q r)) ∗
      (multivariateGaussian (0:State n) (covariance c Z r s)) =
      multivariateGaussian (0:State n) (covariance c Z q s) := by
  have hA := covariance_posSemidef c hc Z hδ hM hqr (fun i => by linarith [hgap i])
    (fun t ht => hbound t ⟨ht.1,ht.2.trans hrs⟩)
    (fun t ht => hnonneg t ⟨ht.1,ht.2.trans hrs⟩)
  have hB := covariance_posSemidef c hc Z hδ hM hrs hgap
    (fun t ht => hbound t ⟨hqr.trans ht.1,ht.2⟩)
    (fun t ht => hnonneg t ⟨hqr.trans ht.1,ht.2⟩)
  rw [multivariateGaussian_convolution _ _ hA hB,← covariance_add_interval c hc Z hδ hM hqr hrs hgap hbound]

/-- Genuine semigroup consistency for the actual backward observation
covariance, before the first target time and without a rank assumption. -/
theorem gaussianSemigroup_composition {n : ℕ} (c : ℝ × SHE.StoppedFourier.HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) {δ M q r s : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hqr : q ≤ r) (hrs : r ≤ s)
    (hgap : ∀ i,δ ≤ (Z i).target-s)
    (hbound : ∀ t ∈ Set.Icc q s,∀ x,|c (t,x)| ≤ M)
    (hnonneg : ∀ t ∈ Set.Icc q s,∀ x,0 ≤ c (t,x))
    (F : State n → ℝ) (hF : Measurable F) {K : ℝ} (hK : ∀ z,|F z| ≤ K) (z : State n) :
    gaussianSemigroup c Z q r (fun y => gaussianSemigroup c Z r s F y) z =
      gaussianSemigroup c Z q s F z := by
  have hA := covariance_posSemidef c hc Z hδ hM hqr (fun i => by linarith [hgap i])
    (fun t ht => hbound t ⟨ht.1,ht.2.trans hrs⟩)
    (fun t ht => hnonneg t ⟨ht.1,ht.2.trans hrs⟩)
  have hB := covariance_posSemidef c hc Z hδ hM hrs hgap
    (fun t ht => hbound t ⟨hqr.trans ht.1,ht.2⟩)
    (fun t ht => hnonneg t ⟨hqr.trans ht.1,ht.2⟩)
  have hh := gaussianAverage_composition _ _ hA hB F hF hK z
  rw [← covariance_add_interval c hc Z hδ hM hqr hrs hgap hbound] at hh
  exact hh

end SHE.GaussianConvolution
