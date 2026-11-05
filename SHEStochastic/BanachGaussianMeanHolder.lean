module

public import SHEStochastic.GaussianMeanHolder
public import SHEStochastic.BanachIntegralComparison

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.BanachGaussianMeanHolder
open MeasureTheory ProbabilityTheory SHE.GaussianIncrement
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem bound {r K β : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → E) (hF : StronglyMeasurable F) (M : ℝ) (hb : ∀ y, ‖F y‖ ≤ M)
    (hh : ∀ x y, ‖F x-F y‖ ≤ K*‖x-y‖^β)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsotropicGaussianHolder.matrix r ≤ A)
    (z w : State n) :
    ‖(∫ y, F (z+y) ∂multivariateGaussian 0 A)-(∫ y, F (w+y) ∂multivariateGaussian 0 A)‖ ≤
      (K*GaussianNormMoment.moment (Fin n) (β+1)*r^((β-1)/2))*‖z-w‖ := by
  have hi (v : State n) : Integrable (fun y => F (v+y)) (multivariateGaussian 0 A) :=
    Integrable.of_bound (hF.comp_measurable (measurable_const.add measurable_id)).aestronglyMeasurable
      M (Filter.Eventually.of_forall fun _ => hb _)
  apply BanachIntegralComparison.bound (hi z) (hi w)
  intro L hL
  have hnorm (x : E) : |L x| ≤ ‖x‖ := (L.le_opNorm x).trans
    (by nlinarith only [hL,norm_nonneg x])
  apply GaussianMeanHolder.bound hr hK hβ (fun y => L (F y))
    (L.continuous.comp_stronglyMeasurable hF).measurable M (fun y => (hnorm _).trans (hb y))
    (fun x y => by rw [← map_sub]; exact (hnorm _).trans (hh x y)) A hA z w

end SHEStochastic.BanachGaussianMeanHolder
