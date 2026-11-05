module

public import SHE.ScalarHeatBandTime
public import SHE.ConvolutionEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
namespace SHE.HeatBandCausalEnergy
open Set MeasureTheory Real
open scoped ENNReal

def density (H β c : ℝ) (j : ℕ) (t : ℝ) : ℝ:=
  (H*ScalarHeatBandEnvelope.constant β 0)^2*CompactMollifier.radius (j+1)^(2*β-2)*
    PolynomialGaussianTime.kernel (1/2) ((3-β)/2) (c^2/CompactMollifier.radius (j+1)^4) t

def kernel (H β c : ℝ) (j : ℕ) : ℝ→ENNReal:=
  (Ioi (0:ℝ)).indicator (fun t=>ENNReal.ofReal (density H β c j t))

theorem kernel_measurable (H β c : ℝ) (j : ℕ) : Measurable (kernel H β c j):=by
  have hf : Measurable (density H β c j):=by unfold density PolynomialGaussianTime.kernel; fun_prop
  exact (ENNReal.continuous_ofReal.measurable.comp hf).indicator measurableSet_Ioi

/-- Exact causal L¹ mass of the ACTUAL sufficient heat-band Gaussian
smoothing envelope for the first signed-noise term. It has band power
nu^{-2 beta}, with no frequency-dependent constant. -/
theorem kernel_mass {H β c : ℝ} (hβ : β≤1) (hc : 0<c) (j : ℕ) :
    (∫⁻ t,kernel H β c j t)=ENNReal.ofReal
      ((H*ScalarHeatBandEnvelope.constant β 0)^2*ScalarHeatBandTime.massConstant β 0*c⁻¹*
        CompactMollifier.radius (j+1)^(2*β)) := by
  let r:=CompactMollifier.radius (j+1)
  have hr : 0<r:=CompactMollifier.radius_pos (j+1)
  have hL : 0<c^2/r^4:=div_pos (sq_pos_of_pos hc) (pow_pos hr 4)
  have hi : IntegrableOn (density H β c j) (Ioi 0):=
    (PolynomialGaussianTime.integrable (by norm_num : (0:ℝ)<1/2)
      (by linarith : (1/2:ℝ)<(3-β)/2) hL).const_mul
      ((H*ScalarHeatBandEnvelope.constant β 0)^2*r^(2*β-2))
  have hn : ∀ᵐ t∂volume.restrict (Ioi (0:ℝ)),0≤density H β c j t:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (rpow_nonneg hr.le _))
      (mul_nonneg (rpow_nonneg ht.le _) (le_min zero_le_one (rpow_nonneg (mul_nonneg hL.le ht.le) _)))
  rw [kernel,lintegral_indicator measurableSet_Ioi,←ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  change (∫ t in Ioi (0:ℝ), (H*ScalarHeatBandEnvelope.constant β 0)^2*r^(2*β-2)*PolynomialGaussianTime.kernel (1/2) ((3-β)/2) (c^2/r^4) t)=_
  rw [integral_const_mul,PolynomialGaussianTime.integral (by norm_num : (0:ℝ)<1/2)
    (by linarith : (1/2:ℝ)<(3-β)/2) hL]
  have he:=ScalarHeatBandTime.scale_factor (β:=β) (ρ:=0) hr hc
  norm_num only [zero_add,mul_zero,add_zero,neg_zero] at he
  rw [show (3-β)/2-1/2=1-β/2 by ring]
  have hi' : c^(-(1:ℝ))=c⁻¹:=Real.rpow_neg_one _
  rw [hi'] at he
  dsimp only [ScalarHeatBandTime.massConstant]
  norm_num only [zero_add,sub_zero]
  calc
    _=(H*ScalarHeatBandEnvelope.constant β 0)^2*(1/(1/2:ℝ)+1/(1-β/2))*(r^(2*β-2)*(c^2/r^4)^(-(1/2:ℝ))):=by ring
    _=_:=by rw [he]; dsimp only [r]; ring

/-- Actual input energies are convolved over the original ordered
window. Tonelli and the proved kernel mass give finite first-term
noise energy; no supremum of the current input is substituted. -/
theorem causal_bound {H β c : ℝ} (hβ : β≤1) (hc : 0<c) (j : ℕ)
    (F : ℝ→ENNReal) (hF : Measurable F) (T : ℝ) :
    (∫⁻ t in Ioc (0:ℝ) T,∫⁻ s in Ioc (0:ℝ) t,kernel H β c j (t-s)*F s)≤
      ENNReal.ofReal ((H*ScalarHeatBandEnvelope.constant β 0)^2*ScalarHeatBandTime.massConstant β 0*c⁻¹*
        CompactMollifier.radius (j+1)^(2*β))*(∫⁻ s in Ioc (0:ℝ) T,F s):=by
  simpa only [kernel_mass hβ hc j] using
    SHE.causal_convolution_energy_bound (kernel H β c j) F (kernel_measurable H β c j) hF T

theorem causal_finite {H β c : ℝ} (hβ : β≤1) (hc : 0<c) (j : ℕ)
    (F : ℝ→ENNReal) (hF : Measurable F) (T : ℝ) (hFin : (∫⁻ s in Ioc (0:ℝ) T,F s)<∞) :
    (∫⁻ t in Ioc (0:ℝ) T,∫⁻ s in Ioc (0:ℝ) t,kernel H β c j (t-s)*F s)<∞:=by
  exact (causal_bound hβ hc j F hF T).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFin)

end SHE.HeatBandCausalEnergy
