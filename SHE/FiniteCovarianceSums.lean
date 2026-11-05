module

public import SHE.GaussianWordCovarianceIntegral
public import SHE.FiniteWordScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.FiniteWordScores
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution MeasurableGaussianScores
  GaussianWordCovarianceIntegral
open scoped BigOperators
variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- A finite sum passes through the actual continuum covariance score.
Both Gaussian and signed physical integrals are justified by the true
bounded tests and physical row energy. -/
theorem covarianceMark_finset (μ : Measure X) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (e : X→ℝ) (he : Measurable e) (row : X→State n) (hr : Measurable row)
    (hrange : ∀ᵐ x ∂μ,row x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (henergy : Integrable (fun x=>|e x| * ‖row x‖^2) μ)
    (F : ℕ→State n→ℝ) (hF : ∀ j,Measurable (F j)) (B : ℕ→ℝ)
    (hb : ∀ j z,|F j z|≤B j) (s : Finset ℕ) (m : State n) :
    covarianceMark μ A e row (fun z=>∑ j∈s,F j z) m=
      ∑ j∈s,covarianceMark μ A e row (F j) m := by
  have hi (j : ℕ) (x : X) : Integrable
      (fun y=>F j (m+y)*secondScore A (row x) y) (multivariateGaussian 0 A) :=
    (GaussianVectorFractions.gaussian_secondScore_integrable A (row x)).bdd_mul
      ((hF j).comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ (fun y=>by simpa only [Real.norm_eq_abs] using hb j (m+y)))
  have ho (j : ℕ) : Integrable
      (fun x=>e x*(∫ y,F j (m+y)*secondScore A (row x) y ∂multivariateGaussian 0 A)) μ :=
    rawMark_outer_integrable μ hA row hr hrange e he henergy (F j) (hF j) (B j) (hb j) m
  unfold covarianceMark
  simp_rw [Finset.sum_mul]
  simp_rw [integral_finsetSum s (fun j _=>hi j _),Finset.mul_sum]
  rw [integral_finsetSum s (fun j _=>ho j),Finset.mul_sum]
end SHE.FiniteWordScores
