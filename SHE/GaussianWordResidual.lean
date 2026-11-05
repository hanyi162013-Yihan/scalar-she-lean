module

public import SHE.GaussianTriangularKernel
public import SHE.GaussianFiniteSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.GaussianWordResidual
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
open MeasurableGaussianScores
open scoped BigOperators
variable {n r : ℕ}

/-- Regroup the genuinely independent old/residual pairs and combine all
residual vectors into their exact summed Gaussian covariance. The fixed
old tuple, its original scores and the full test remain intact. -/
theorem pair_word_eq_residual_average
    (R B : Fin r → MeasurableGeneralizedInverse.Mat n) (hB : ∀ j, (B j).PosSemidef)
    (d : Fin r → State n) (F : State n → ℝ) (hF : Measurable F)
    (M : ℝ) (hb : ∀ z, |F z| ≤ M) (z : State n) :
    (∫ x : Fin r → State n × State n,
      (∏ j, secondScore (R j) (d j) (x j).1) *
        F (z + ∑ j, ((x j).1 + (x j).2))
      ∂Measure.pi (fun j => (multivariateGaussian (0 : State n) (R j)).prod
        (multivariateGaussian 0 (B j)))) =
      gaussianAverage (∑ j, B j)
        (WeightedBorelAverage.average
          (Measure.pi (fun j => multivariateGaussian (0 : State n) (R j)))
          (fun x => ∏ j, secondScore (R j) (d j) (x j))
          (fun x => ∑ j, x j) F) z := by
  let μ : Measure (Fin r → State n) := Measure.pi (fun j => multivariateGaussian 0 (R j))
  let ν : Measure (Fin r → State n) := Measure.pi (fun j => multivariateGaussian 0 (B j))
  let S : (Fin r → State n) → ℝ := fun x => ∏ j, secondScore (R j) (d j) (x j)
  let shift : (Fin r → State n) → State n := fun x => ∑ j, x j
  have hS : Integrable S μ :=
    Integrable.fintype_prod (fun j => GaussianVectorFractions.gaussian_secondScore_integrable (R j) (d j))
  have hSm : Measurable S := by
    apply Finset.measurable_prod Finset.univ
    intro j _
    have hm : Measurable (fun x : Fin r → State n => inner ℝ (coefficient (R j) (d j)) (x j)) :=
      (innerSL ℝ (coefficient (R j) (d j))).measurable.comp (measurable_pi_apply j)
    exact (hm.pow_const 2).sub measurable_const
  have hshift : Measurable shift := Finset.measurable_sum Finset.univ
    (fun j _ => measurable_pi_apply j)
  have hm : Measurable (fun p : (Fin r → State n) × (Fin r → State n) =>
      F (z + shift p.1 + shift p.2)) :=
    hF.comp ((measurable_const.add (hshift.comp measurable_fst)).add (hshift.comp measurable_snd))
  have hi : Integrable (fun p : (Fin r → State n) × (Fin r → State n) =>
      S p.1 * F (z + shift p.1 + shift p.2)) (μ.prod ν) :=
    (hS.comp_fst ν).mul_bdd hm.aestronglyMeasurable (ae_of_all _ (fun p => by
      change ‖F (z + shift p.1 + shift p.2)‖ ≤ M
      simpa only [Real.norm_eq_abs] using hb (z + shift p.1 + shift p.2)))
  have hs :
      (∫ x : Fin r → State n × State n,
        (∏ j, secondScore (R j) (d j) (x j).1) * F (z + ∑ j, ((x j).1 + (x j).2))
        ∂Measure.pi (fun j => (multivariateGaussian (0 : State n) (R j)).prod
          (multivariateGaussian 0 (B j)))) =
      ∫ p : (Fin r → State n) × (Fin r → State n), S p.1 * F (z + shift p.1 + shift p.2)
        ∂μ.prod ν := by
    have h := (measurePreserving_arrowProdEquivProdArrow (State n) (State n) (Fin r)
      (fun j => multivariateGaussian (0 : State n) (R j))
      (fun j => multivariateGaussian (0 : State n) (B j))).integral_comp'
      (fun p => S p.1 * F (z + shift p.1 + shift p.2))
    convert! h using 1
    apply integral_congr_ae
    apply ae_of_all
    intro x
    change _ = (∏ j, secondScore (R j) (d j) (x j).1) *
      F (z + (∑ j, (x j).1) + ∑ j, (x j).2)
    dsimp only
    rw [Finset.sum_add_distrib, add_assoc]
  rw [hs, MeasureTheory.integral_prod_symm _ hi]
  have he :
      (fun y : Fin r → State n => ∫ x, S x * F (z + shift x + shift y) ∂μ) =
      fun y => WeightedBorelAverage.average μ S shift F (z + shift y) := by
    funext y
    apply integral_congr_ae
    apply ae_of_all
    intro x
    change S x * F (z + shift x + shift y) = S x * F (z + shift y + shift x)
    congr 2
    abel
  rw [he]
  have hG := WeightedBorelAverage.measurable μ S hSm shift hshift F hF
  have hmap := integral_map (μ := ν) (φ := shift)
    (f := fun y => WeightedBorelAverage.average μ S shift F (z+y)) hshift.aemeasurable
    (hG.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  have hlaw : ν.map shift = multivariateGaussian (0 : State n) (∑ j, B j) :=
    GaussianFiniteSum.map_sum r B hB
  rw [hlaw] at hmap
  exact hmap.symm

end SHE.GaussianWordResidual
