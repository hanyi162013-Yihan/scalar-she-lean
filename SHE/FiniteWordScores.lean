module

public import SHE.ControlledFiniteWord
public import SHE.GaussianWordCovarianceIntegral
public import SHE.GaussianVectorFractions

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FiniteWordScores
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianRangeSmooth
  FiniteCenteredProduct MeasurableGaussianScores GaussianWordCovarianceIntegral
open scoped BigOperators NNReal Matrix.Norms.L2Operator
variable {ι : Type*} [DecidableEq ι] {n : ℕ}

theorem integral_weighted_expansion (s : Finset ι) (A : Matrix (Fin n) (Fin n) ℝ)
    (R : State n → ℝ) (a : ι → State n → ℝ) (b : ι → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hRb : ∀ z, |R z| ≤ B) (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i)
    (m : State n) (W : State n → ℝ) (hW : Integrable W (multivariateGaussian 0 A)) :
    (∫ y, test s R a b (m + y) * W y ∂multivariateGaussian 0 A) =
      ∑ t ∈ s.powerset, coefficient s t b *
        (∫ y, monomial R a t (m + y) * W y ∂multivariateGaussian 0 A) := by
  have hp (y : State n) : test s R a b (m + y) * W y =
      ∑ t ∈ s.powerset, coefficient s t b * (monomial R a t (m + y) * W y) := by
    rw [expansion, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  simp_rw [hp]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro t ht
    have hts := Finset.mem_powerset.mp ht
    exact (hW.bdd_mul ((measurable_monomial t R a hR (fun i hi => ha i (hts hi))).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ (fun z => by
        simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.add_apply, id_eq] using monomial_bound t R a B M hB
          (fun i hi => hM i (hts hi)) hRb (fun i hi => hab i (hts hi)) (m + z)))).const_mul _

theorem firstScore_integrable (A : Matrix (Fin n) (Fin n) ℝ) (D : State n) :
    Integrable (firstScore A D) (multivariateGaussian 0 A) :=
  (IsGaussian.memLp_dual (multivariateGaussian (0 : State n) A)
    (innerSL ℝ (coefficient A D)) 1 (by norm_num)).integrable (by norm_num)

/-- The entire finite centered product is marked by the same first score;
the subset expansion introduces no derivative of an old score or leaf. -/
theorem meanMark_expansion (s : Finset ι) (A : Matrix (Fin n) (Fin n) ℝ)
    (R : State n → ℝ) (a : ι → State n → ℝ) (b : ι → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hRb : ∀ z, |R z| ≤ B) (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i)
    (m D : State n) :
    (∫ y, test s R a b (m + y) * firstScore A D y ∂multivariateGaussian 0 A) =
      ∑ t ∈ s.powerset, coefficient s t b *
        (∫ y, monomial R a t (m + y) * firstScore A D y ∂multivariateGaussian 0 A) :=
  integral_weighted_expansion s A R a b hR ha B M hB hM hRb hab m _ (firstScore_integrable A D)

variable {X : Type*} [MeasurableSpace X]

def covarianceMark (μ : Measure X) (A : Matrix (Fin n) (Fin n) ℝ) (e : X → ℝ)
    (row : X → State n) (F : State n → ℝ) (m : State n) : ℝ :=
  (1 / 2 : ℝ) * ∫ p, e p * (∫ y, F (m + y) * secondScore A (row p) y
    ∂multivariateGaussian 0 A) ∂μ

/-- The exact finite-product covariance mark is the literal continuum
second-score integral. All outer integrability follows from physical frame
energy; there is no rank or conditioning bound in the identity. -/
theorem covarianceMark_expansion (μ : Measure X) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (e : X → ℝ) (he : Measurable e)
    (row : X → State n) (hrow : Measurable row)
    (hrange : ∀ᵐ p ∂μ, row p ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range)
    (henergy : Integrable (fun p => |e p| * ‖row p‖ ^ 2) μ)
    (s : Finset ι) (R : State n → ℝ) (a : ι → State n → ℝ) (b : ι → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hRb : ∀ z, |R z| ≤ B) (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i) (m : State n) :
    covarianceMark μ A e row (test s R a b) m =
      ∑ t ∈ s.powerset, coefficient s t b * covarianceMark μ A e row (monomial R a t) m := by
  have hp (p : X) : e p * (∫ y, test s R a b (m + y) * secondScore A (row p) y
      ∂multivariateGaussian 0 A) =
      ∑ t ∈ s.powerset, coefficient s t b * (e p * rawMark A (monomial R a t) m (row p)) := by
    rw [integral_weighted_expansion s A R a b hR ha B M hB hM hRb hab m _
      (GaussianVectorFractions.gaussian_secondScore_integrable A (row p)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [rawMark]
    ring
  unfold covarianceMark
  simp_rw [hp]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [rawMark]
    ring
  · intro t ht
    have hts := Finset.mem_powerset.mp ht
    exact (rawMark_outer_integrable μ hA row hrow hrange e he henergy
      (monomial R a t) (measurable_monomial t R a hR (fun i hi => ha i (hts hi)))
      (B * ∏ i ∈ t, M i) (fun z => monomial_bound t R a B M hB
        (fun i hi => hM i (hts hi)) hRb (fun i hi => hab i (hts hi)) z) m).const_mul _

end SHE.FiniteWordScores
