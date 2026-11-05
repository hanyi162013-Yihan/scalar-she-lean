module

public import SHE.VaryingAssignedFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.GaussianFibreBorel
open MeasureTheory ProbabilityTheory GaussianIncrement GaussianDependentScores GaussianScoreKernel
variable {Ω : Type*} [MeasurableSpace Ω] {n r : ℕ}

/-- Borel integration over the ACTUAL independent old Gaussian product
and full residual Gaussian law. Both covariance fields may vary and
change rank with the same original parameter as the entire integrand. -/
theorem average_measurable
    (A : Ω→Fin r→MeasurableGeneralizedInverse.Mat n) (hA : ∀j,Measurable (fun ω=>A ω j))
    (B : Ω→MeasurableGeneralizedInverse.Mat n) (hB : Measurable B)
    (F : Ω×((Fin r→State n)×State n)→ℝ) (hF : Measurable F) :
    Measurable (fun ω=>∫x,F (ω,x)
      ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A ω j))).prod
        (multivariateGaussian (0:State n) (B ω))) := by
  let κold := FiniteKernelProduct.kernel r (fun j=>gaussianKernel (fun ω=>A ω j) (hA j))
  let κ := κold.prod (gaussianKernel B hB)
  have hh := (hF.stronglyMeasurable.integral_kernel_prod_right' (κ:=κ)).measurable
  convert! hh using 1
  funext ω
  rw [show κ ω=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A ω j))).prod
      (multivariateGaussian (0:State n) (B ω)) by
    dsimp only [κ]
    rw [Kernel.prod_apply,FiniteKernelProduct.kernel_apply]
    rfl]

end SHE.GaussianFibreBorel
