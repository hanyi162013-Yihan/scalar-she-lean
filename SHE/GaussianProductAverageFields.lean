module

public import SHE.FiniteKernelProduct
public import SHE.GaussianScoreKernel
public import SHE.WeightedBorelAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.GaussianProductAverageFields
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianScoreKernel MeasurableGaussianScores
open scoped BigOperators
variable {X : Type*} [MeasurableSpace X] {n r : ℕ}
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse

theorem measurable_product_average (A : X → Fin r → MeasurableGeneralizedInverse.Mat n)
    (hA : ∀ j,Measurable (fun x => A x j)) (F : X × (Fin r → State n) → ℝ)
    (hF : Measurable F) :
    Measurable (fun x => ∫ y,F (x,y) ∂Measure.pi (fun j => multivariateGaussian 0 (A x j))) := by
  exact FiniteKernelProduct.measurable_integral r
    (fun j => gaussianKernel (fun x => A x j) (hA j)) F hF

set_option backward.isDefEq.respectTransparency true in
/-- The full fixed-old score average is jointly Borel in all original
covariances, directions, root/leaf tests and arbitrary dependent means. -/
theorem weighted_average_measurable (A : X → Fin r → MeasurableGeneralizedInverse.Mat n)
    (hA : ∀ j,Measurable (fun x => A x j)) (d : X → Fin r → State n)
    (hd : ∀ j,Measurable (fun x => d x j)) (F : X × State n → ℝ) (hF : Measurable F)
    (m : X → State n) (hm : Measurable m) :
    Measurable (fun x => WeightedBorelAverage.average
      (Measure.pi (fun j => multivariateGaussian (0 : State n) (A x j)))
      (fun y => ∏ j,secondScore (A x j) (d x j) (y j))
      (fun y => ∑ j,y j) (fun z => F (x,z)) (m x)) := by
  have hscore (j : Fin r) : Measurable (fun p : X × (Fin r → State n) =>
      secondScore (A p.1 j) (d p.1 j) (p.2 j)) := by
    have hp : Measurable (fun x : X => (A x j,d x j)) := (hA j).prodMk (hd j)
    have hcX : Measurable (fun x : X => coefficient (A x j) (d x j)) :=
      (coefficient_measurable (n := n)).comp hp
    have hc : Measurable (fun p : X × (Fin r → State n) => coefficient (A p.1 j) (d p.1 j)) :=
      hcX.comp measurable_fst
    have hy : Measurable (fun p : X × (Fin r → State n) => inner ℝ
        (coefficient (A p.1 j) (d p.1 j)) (p.2 j)) :=
      (continuous_inner (𝕜 := ℝ)).measurable.comp (hc.prodMk ((measurable_pi_apply j).comp measurable_snd))
    have hv : Measurable (fun p : X × (Fin r → State n) => inner ℝ
        (coefficient (A p.1 j) (d p.1 j)) (d p.1 j)) :=
      (continuous_inner (𝕜 := ℝ)).measurable.comp (hc.prodMk ((hd j).comp measurable_fst))
    exact (hy.pow_const 2).sub hv
  have hshift : Measurable (fun p : X × (Fin r → State n) => m p.1+∑ j,p.2 j) :=
    (hm.comp measurable_fst).add (Finset.measurable_sum Finset.univ
      (fun j _ => (measurable_pi_apply j).comp measurable_snd))
  exact measurable_product_average A hA _
    ((Finset.measurable_prod Finset.univ (fun j _ => hscore j)).mul
      (hF.comp (measurable_fst.prodMk hshift)))

end SHE.GaussianProductAverageFields
