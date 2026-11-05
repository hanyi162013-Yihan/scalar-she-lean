module

public import SHE.ParameterSmoothContinuity
public import SHE.GaussianContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.GaussianParameterContinuity
open MeasureTheory ProbabilityTheory Matrix WordRecursion GaussianContinuity
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {n : ℕ}

/-- Gaussian averaging is continuous for a genuinely moving bounded
continuous test as well as a moving PSD covariance and physical mean. -/
theorem continuous_average {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (F : X → State n → G) (hF : Continuous (fun p : X × State n => F p.1 p.2))
    {K : ℝ} (hb : ∀ p z,‖F p z‖ ≤ K) (A : X → PositiveCovariance n) (hA : Continuous A) :
    Continuous (fun p : X × State n => GaussianSmooth.average
      (multivariateGaussian 0 (A p.1).val) (F p.1) p.2) := by
  have he : (fun p : X × State n => GaussianSmooth.average
        (multivariateGaussian 0 (A p.1).val) (F p.1) p.2)=
      fun p : X × State n => ∫ x : State n,F p.1
        (p.2+toEuclideanCLM (𝕜:=ℝ) (CFC.sqrt (A p.1).val) x) ∂stdGaussian (State n) := by
    funext p
    exact gaussian_integral_as_standard (F p.1)
      (hF.comp (continuous_const.prodMk continuous_id)) _ _
  rw [he]
  apply continuous_of_dominated (bound := fun _ : State n => K)
  · intro p
    exact (hF.comp (continuous_const.prodMk
      (continuous_const.add (toEuclideanCLM (𝕜:=ℝ) (CFC.sqrt (A p.1).val)).continuous))).aestronglyMeasurable
  · exact fun p => ae_of_all _ (fun x => hb _ _)
  · exact integrable_const _
  · apply ae_of_all
    intro x
    have hp : Continuous (fun p : X × State n => A p.1) := hA.comp continuous_fst
    have hsqrt := (continuous_positive_sqrt n).comp hp
    have heq : (fun p : X × State n => toEuclideanCLM (𝕜:=ℝ) (CFC.sqrt (A p.1).val) x)=
        fun p : X × State n => WithLp.toLp 2 (fun i => ∑ j,(CFC.sqrt (A p.1).val) i j*x j) := by
      funext p
      apply (WithLp.equiv 2 (Fin n → ℝ)).injective
      exact Matrix.ofLp_toEuclideanCLM _ _
    have hlin : Continuous (fun p : X × State n =>
        toEuclideanCLM (𝕜:=ℝ) (CFC.sqrt (A p.1).val) x) := by
      rw [heq]
      apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
      apply continuous_pi
      intro i
      exact continuous_finsetSum _ (fun j _ =>
        (((continuous_apply j).comp (continuous_apply i)).comp hsqrt).mul_const (x j))
    exact hF.comp (continuous_fst.prodMk (continuous_snd.add hlin))

theorem continuous_average_hessian (F : X → State n → ℝ)
    (hF : Continuous (fun p : X × State n => F p.1 p.2))
    (hFs : UniformSmooth.UniformBoundedSmooth F)
    (A : X → PositiveCovariance n) (hA : Continuous A) :
    Continuous (fun p : X × State n => GaussianTaylor.hessian
      (GaussianSmooth.average (multivariateGaussian 0 (A p.1).val) (F p.1)) p.2) := by
  obtain ⟨K,_,hK⟩ := hFs.norm_bound
  have hc := continuous_average F hF hK A hA
  have hs := hFs.average (fun p => multivariateGaussian 0 (A p).val) (fun _ => inferInstance)
  exact ParameterSmoothContinuity.continuous_hessian _ hc hs

end SHE.GaussianParameterContinuity
