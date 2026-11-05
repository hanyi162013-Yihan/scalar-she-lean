module

public import SHE.PolynomialGaussianTime

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.PolynomialEnergyOpen
open Set MeasureTheory Real

/-- Actual measurable energy densities dominated by the proved
polynomial Gaussian kernel are integrable, with its exact scaled mass.
No operator norm or integrability of the energy is assumed. -/
theorem dominated {γ s L K h : ℝ} (hγ : 0<γ) (hs : γ<s) (hL : 0<L) (hK : 0≤K)
    (G : ℝ→ℝ) (hG : Measurable G)
    (hb : ∀ t∈Ioo (0:ℝ) h,|G t|≤K*PolynomialGaussianTime.kernel γ s L t) :
    IntegrableOn G (Ioc (0:ℝ) h) ∧
      (∫ t in Ioc (0:ℝ) h,G t)≤K*(1/γ+1/(s-γ))*L^(-γ) := by
  have hmem:∀ᵐ t∂volume.restrict (Ioc (0:ℝ) h),t∈Ioo (0:ℝ) h:=by
    rw [←restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have hf : IntegrableOn (fun t=>K*PolynomialGaussianTime.kernel γ s L t) (Ioi 0):=
    (PolynomialGaussianTime.integrable hγ hs hL).const_mul K
  have hf' := hf.mono_set (show Ioc (0:ℝ) h⊆Ioi 0 from fun _ ht=>ht.1)
  have hi : IntegrableOn G (Ioc (0:ℝ) h):=by
    apply hf'.mono' hG.aestronglyMeasurable
    filter_upwards [hmem] with t ht
    simpa only [Real.norm_eq_abs] using hb t ht
  refine ⟨hi,?_⟩
  have hle : (∫ t in Ioc (0:ℝ) h,G t)≤∫ t in Ioi (0:ℝ),K*PolynomialGaussianTime.kernel γ s L t:=by
    apply (integral_mono_ae hi hf' (by
      filter_upwards [hmem] with t ht
      exact (le_abs_self _).trans (hb t ht))).trans
    apply setIntegral_mono_set hf
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg hK (mul_nonneg (rpow_nonneg ht.le _)
        (le_min zero_le_one (rpow_nonneg (mul_nonneg hL.le ht.le) _)))
    · exact ae_of_all _ (fun t ht=>ht.1)
  apply hle.trans_eq
  rw [integral_const_mul,PolynomialGaussianTime.integral hγ hs hL]
  ring

end SHE.PolynomialEnergyOpen
