module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Moments.CovarianceBilin

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.CenteredGaussianFiniteLaw
open MeasureTheory ProbabilityTheory WithLp
open scoped NNReal ENNReal
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A centered finite Gaussian vector has the exact multivariate law
specified by its coordinate covariance matrix. Degenerate matrices and
repeated coordinates are allowed. -/
theorem law (X : Ω → (ι → ℝ)) (hX : HasGaussianLaw X μ)
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (hMean : ∀ i,(∫ ω,X ω i ∂μ)=0)
    (hCov : ∀ i j,cov[fun ω => X ω i,fun ω => X ω j;μ]=A i j) :
    HasLaw (fun ω => toLp 2 (X ω)) (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) μ := by
  let Z := fun ω => toLp 2 (X ω)
  have hZ : HasGaussianLaw Z μ :=
    hX.map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap
  refine ⟨hZ.aemeasurable,?_⟩
  letI := hZ.isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map hZ.aemeasurable measurable_id.aestronglyMeasurable]
    simp only [id_eq]
    rw [integral_id_multivariateGaussian]
    apply PiLp.ext
    intro i
    change (EuclideanSpace.proj (𝕜 := ℝ) i) (∫ ω,Z ω ∂μ)=0
    rw [←(EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hZ.integrable]
    exact hMean i
  · rw [←ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis (fun i j => ?_)
    simp only [ContinuousLinearMap.toBilinForm_apply]
    change covarianceBilin (μ.map (fun ω => toLp 2 (fun i => X ω i)))
      (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)=
      covarianceBilin (multivariateGaussian (0 : EuclideanSpace ℝ ι) A)
        (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)
    rw [covarianceBilin_apply_basisFun (fun i => (hX.eval i).memLp_two),covarianceBilin_multivariateGaussian hA,hCov]
    simp

/-- Direct Euclidean-state form, avoiding any choice of topology on an
intermediate function space. -/
theorem law_state (X : Ω → EuclideanSpace ℝ ι) (hX : HasGaussianLaw X μ)
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (hMean : ∀ i,(∫ ω,X ω i ∂μ)=0)
    (hCov : ∀ i j,cov[fun ω => X ω i,fun ω => X ω j;μ]=A i j) :
    HasLaw X (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) μ := by
  refine ⟨hX.aemeasurable,?_⟩
  letI := hX.isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map hX.aemeasurable measurable_id.aestronglyMeasurable]
    simp only [id_eq]
    rw [integral_id_multivariateGaussian]
    apply PiLp.ext
    intro i
    change (EuclideanSpace.proj (𝕜 := ℝ) i) (∫ ω,X ω ∂μ)=0
    rw [←(EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hX.integrable]
    exact hMean i
  · rw [←ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis (fun i j => ?_)
    simp only [ContinuousLinearMap.toBilinForm_apply]
    change covarianceBilin (μ.map X) (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)=
      covarianceBilin (multivariateGaussian (0 : EuclideanSpace ℝ ι) A)
        (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)
    have hRep : (fun ω => toLp 2 (fun i => X ω i))=X := by funext ω;rfl
    have hh := covarianceBilin_apply_basisFun
      (fun i => (hX.map (EuclideanSpace.proj (𝕜 := ℝ) i)).memLp_two) i j
    change covarianceBilin (μ.map (fun ω => toLp 2 (fun i => X ω i)))
      (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)=
      cov[fun ω => X ω i,fun ω => X ω j;μ] at hh
    rw [hRep] at hh
    rw [hh,covarianceBilin_multivariateGaussian hA,hCov]
    simp

end SHEStochastic.CenteredGaussianFiniteLaw
