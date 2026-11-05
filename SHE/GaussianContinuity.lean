module

public import SHE.GaussianConvolution
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace SHE.GaussianContinuity
open MeasureTheory ProbabilityTheory Matrix SHE.WordRecursion
open scoped MatrixOrder Matrix.Norms.L2Operator

abbrev PositiveCovariance (n : ℕ) := {A : Matrix (Fin n) (Fin n) ℝ // A.PosSemidef}

theorem continuous_positive_sqrt (n : ℕ) :
    Continuous (fun A : PositiveCovariance n => CFC.sqrt A.val) :=
  CFC.continuousOn_sqrt.comp_continuous continuous_subtype_val (fun A => A.property.nonneg)

theorem gaussian_integral_as_standard {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {n : ℕ} (F : State n → E) (hF : Continuous F)
    (A : Matrix (Fin n) (Fin n) ℝ) (m : State n) :
    (∫ y : State n,F (m+y) ∂multivariateGaussian 0 A) =
      ∫ x : State n,F (m+toEuclideanCLM (𝕜:=ℝ) (CFC.sqrt A) x) ∂stdGaussian (State n) := by
  have hg : Continuous (fun y : State n => F (m+y)) := by fun_prop
  rw [multivariateGaussian,integral_map (by fun_prop) hg.aestronglyMeasurable]
  simp only [zero_add]

/-- Gaussian averaging is jointly continuous in the actual PSD covariance
and physical mean for every bounded continuous Banach-valued test. This
includes singular limits and continuous Hessian/operator-valued tests. -/
theorem continuous_gaussian_average {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {n : ℕ} (F : State n → E) (hF : Continuous F)
    {K : ℝ} (hbound : ∀ z,‖F z‖ ≤ K) :
    Continuous (fun p : PositiveCovariance n × State n =>
      ∫ y : State n,F (p.2+y) ∂multivariateGaussian 0 p.1.val) := by
  have he : (fun p : PositiveCovariance n × State n =>
      ∫ y : State n,F (p.2+y) ∂multivariateGaussian 0 p.1.val) =
      fun p : PositiveCovariance n × State n =>
        ∫ x : State n,F (p.2+toEuclideanCLM (𝕜:=ℝ) (CFC.sqrt p.1.val) x) ∂stdGaussian (State n) := by
    funext p
    exact gaussian_integral_as_standard F hF p.1.val p.2
  rw [he]
  apply continuous_of_dominated (bound:=fun _ : State n => K)
  · intro p
    exact (hF.comp (continuous_const.add (toEuclideanCLM (𝕜:=ℝ) (CFC.sqrt p.1.val)).continuous)).aestronglyMeasurable
  · intro p
    exact ae_of_all _ (fun x => hbound _)
  · exact integrable_const K
  · apply ae_of_all
    intro x
    have hsqrt : Continuous (fun p : PositiveCovariance n × State n => CFC.sqrt p.1.val) :=
      (continuous_positive_sqrt n).comp continuous_fst
    have heq : (fun p : PositiveCovariance n × State n => toEuclideanCLM (𝕜:=ℝ) (CFC.sqrt p.1.val) x) =
        fun p : PositiveCovariance n × State n => WithLp.toLp 2 (fun i => ∑ j,(CFC.sqrt p.1.val) i j*x j) := by
      funext p
      apply (WithLp.equiv 2 (Fin n → ℝ)).injective
      exact Matrix.ofLp_toEuclideanCLM _ _
    have hlin : Continuous (fun p : PositiveCovariance n × State n =>
        toEuclideanCLM (𝕜:=ℝ) (CFC.sqrt p.1.val) x) := by
      rw [heq]
      apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
      apply continuous_pi
      intro i
      exact continuous_finsetSum _ (fun j _ =>
        (((continuous_apply j).comp (continuous_apply i)).comp hsqrt).mul_const (x j))
    exact hF.comp (continuous_snd.add hlin)

end SHE.GaussianContinuity
