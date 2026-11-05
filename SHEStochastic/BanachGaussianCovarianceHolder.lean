module

public import SHEStochastic.GaussianCovarianceHolder
public import Mathlib.Analysis.Normed.Module.HahnBanach

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.BanachGaussianCovarianceHolder
open MeasureTheory ProbabilityTheory SHE SHE.GaussianIncrement SHE.GaussianAudit
  SHE.GaussianSignedCovariance
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The same Hölder covariance estimate holds for Banach-valued tests.
A norming real functional reuses the scalar Gaussian proof, retaining its
constant and avoiding coordinate losses for matrix-valued coefficients. -/
theorem bound {r K β : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → E) (hF : StronglyMeasurable F) (M : ℝ) (hb : ∀ y, ‖F y‖ ≤ M)
    (hh : ∀ x y, ‖F x-F y‖ ≤ K*‖x-y‖^β)
    (A C : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsotropicGaussianHolder.matrix r ≤ A) (hC : IsotropicGaussianHolder.matrix r ≤ C)
    (z : State n) :
    ‖(∫ y, F (z+y) ∂multivariateGaussian 0 A)-
      (∫ y, F (z+y) ∂multivariateGaussian 0 C)‖ ≤
      (K*secondScoreAbsIncrementMoment β*r^(β/2-1))*covarianceBoundConstant n*‖A-C‖ := by
  let v := (∫ y, F (z+y) ∂multivariateGaussian 0 A)-
    (∫ y, F (z+y) ∂multivariateGaussian 0 C)
  obtain ⟨L, hL, hLv⟩ := exists_dual_vector'' ℝ v
  have hLval : L v = ‖v‖ := by simpa only [RCLike.ofReal_real_eq_id, id_eq] using hLv
  have hbound (x : E) : |L x| ≤ ‖x‖ := by
    exact (L.le_opNorm x).trans (by nlinarith only [hL, norm_nonneg x])
  let f := fun y => L (F y)
  have hf : Measurable f := (L.continuous.comp_stronglyMeasurable hF).measurable
  have hfb (y : State n) : |f y| ≤ M := (hbound _).trans (hb y)
  have hfh (x y : State n) : |f x-f y| ≤ K*‖x-y‖^β := by
    change |L (F x)-L (F y)| ≤ _
    rw [← map_sub]
    exact (hbound _).trans (hh x y)
  have hl := GaussianCovarianceHolder.bound hr hK hβ f hf M hfb hfh A C hA hC z
  have hi (B : Matrix (Fin n) (Fin n) ℝ) :
      Integrable (fun y => F (z+y)) (multivariateGaussian 0 B) :=
    Integrable.of_bound (hF.comp_measurable (measurable_const.add measurable_id)).aestronglyMeasurable
      M (Filter.Eventually.of_forall fun y => hb _)
  have he : SHE.GaussianConvolution.gaussianAverage A f z-
      SHE.GaussianConvolution.gaussianAverage C f z = L v := by
    dsimp only [v]
    rw [map_sub, ← L.integral_comp_comm (hi A), ← L.integral_comp_comm (hi C)]
    rfl
  rw [he, hLval, abs_of_nonneg (norm_nonneg v)] at hl
  exact hl

end SHEStochastic.BanachGaussianCovarianceHolder
