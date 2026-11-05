module

public import SHE.DampedHeatKernel
public import SHE.HaarIncrementEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.DampedKernelIncrement
open MeasureTheory Set CircleHeat FiniteHaar
open scoped NNReal ENNReal

theorem exp_difference {Λ τ δ : ℝ} (hΛ : 0 ≤ Λ) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) :
    |Real.exp (-Λ*(τ+δ))-Real.exp (-Λ*τ)| ≤ Λ*δ := by
  have hτe : Real.exp (-Λ*τ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hδe : Real.exp (-Λ*δ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hlow : 1-Real.exp (-Λ*δ) ≤ Λ*δ := by linarith [Real.add_one_le_exp (-Λ*δ)]
  have he : Real.exp (-Λ*(τ+δ))=Real.exp (-Λ*τ)*Real.exp (-Λ*δ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he,abs_of_nonpos (by nlinarith [Real.exp_pos (-Λ*τ)])]
  have hm := mul_le_mul hτe hlow (sub_nonneg.mpr hδe) (by norm_num : (0:ℝ) ≤ 1)
  nlinarith only [hm]

/-- The literal damped common-Haar kernel increment is controlled by
the undamped increment and a lower-order fixed-time kernel term. -/
theorem kernel_increment_sq {Λ ell M τ δ : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell)
    (hδ : 0 ≤ δ) (f : EllipticField ell M) :
    ‖DampedHeatKernel.kernel Λ ell M hell (τ+δ,f)-DampedHeatKernel.kernel Λ ell M hell (τ,f)‖^2 ≤
      2*‖RealHaarIntegrand.kernel ell M hell (τ+δ,f)-RealHaarIntegrand.kernel ell M hell (τ,f)‖^2+
      2*(Λ*δ)^2*‖RealHaarIntegrand.kernel ell M hell (τ,f)‖^2 := by
  by_cases hτ : τ ≤ 0
  · rw [DampedHeatKernel.kernel_zero hell hτ,HaarKernelApproximation.kernel_zero hell hτ,sub_zero,sub_zero,norm_zero]
    have hb := pow_le_pow_left₀ (norm_nonneg _) (DampedHeatKernel.kernel_norm_le hΛ hell (t := τ+δ) f) 2
    nlinarith [sq_nonneg ‖RealHaarIntegrand.kernel ell M hell (τ+δ,f)‖]
  · have hτpos : 0 < τ := lt_of_not_ge hτ
    let x := RealHaarIntegrand.kernel ell M hell (τ+δ,f)
    let y := RealHaarIntegrand.kernel ell M hell (τ,f)
    let a := Real.exp (-Λ*(τ+δ))
    let b := Real.exp (-Λ*τ)
    have ha : |a| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    have hab : |a-b| ≤ Λ*δ := exp_difference hΛ hτpos.le hδ
    have he : a • x-b • y=a • (x-y)+(a-b) • y := by
      simp only [smul_sub,sub_smul]
      abel
    have hn : ‖a • x-b • y‖ ≤ ‖x-y‖+(Λ*δ)*‖y‖ := by
      rw [he]
      apply (norm_add_le _ _).trans
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
      exact add_le_add (by nlinarith [norm_nonneg (x-y)])
        (mul_le_mul_of_nonneg_right hab (norm_nonneg y))
    change ‖a • x-b • y‖^2 ≤ 2*‖x-y‖^2+2*(Λ*δ)^2*‖y‖^2
    have hs := sq_nonneg (‖x-y‖-(Λ*δ)*‖y‖)
    have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith only [hs,hp]

end SHE.DampedKernelIncrement
