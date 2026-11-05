module
public import SHE.DampedEnergy
public import SHE.CompanionEnergy
public import SHE.PredictableTime
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.BieleckiKernel
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

def kernel (h γ:ℝ)(u:ℝ):ℝ≥0∞:=
  (Ioc (0:ℝ) h).indicator (fun u=>ENNReal.ofReal (Real.exp (-2*γ*u)*u^(-(1/2:ℝ)))) u

def mass (γ:ℝ):ℝ:=dampingPowerConstant (1/2)*γ^(-(1/2:ℝ))

theorem measurable (h γ:ℝ):Measurable (kernel h γ):=by
  have hm:Measurable (fun u:ℝ=>Real.exp (-2*γ*u)*u^(-(1/2:ℝ))):=by fun_prop
  exact (ENNReal.continuous_ofReal.measurable.comp hm).indicator measurableSet_Ioc

theorem mass_nonneg {γ:ℝ}(hγ:0≤γ):0≤mass γ:=
  mul_nonneg (dampingPowerConstant_pos (by norm_num : (0:ℝ)<1/2)).le (Real.rpow_nonneg hγ _)

theorem kernel_mass_le (h:ℝ){γ:ℝ}(hγ:0<γ):
    (∫⁻u:ℝ,kernel h γ u)≤ENNReal.ofReal (mass γ):=by
  simp only [kernel,lintegral_indicator measurableSet_Ioc]
  have hi:=damped_power_integrable hγ (by norm_num : (0:ℝ)<1/2)
  have he:=damped_power_integral hγ (by norm_num : (0:ℝ)<1/2)
  norm_num only [show (1/2:ℝ)-1=-(1/2:ℝ) by norm_num] at hi he
  calc
    _≤∫⁻u in Ioi (0:ℝ),ENNReal.ofReal (Real.exp (-2*γ*u)*u^(-(1/2:ℝ))):=
      lintegral_mono_set (fun _ hu=>hu.1)
    _=ENNReal.ofReal (mass γ):=by
      rw [←ofReal_integral_eq_lintegral_ofReal hi]
      · exact congrArg ENNReal.ofReal he
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hu.le _)

theorem causal_energy (h:ℝ){γ:ℝ}(hγ:0<γ)(F:ℝ→ℝ≥0∞)(hF:Measurable F):
    (∫⁻t in Ioc (0:ℝ) h,∫⁻s in Ioc (0:ℝ) t,kernel h γ (t-s)*F s)≤
      ENNReal.ofReal (mass γ)*(∫⁻s in Ioc (0:ℝ) h,F s):=
  (causal_convolution_energy_bound _ F (measurable h γ) hF h).trans (by
    gcongr
    exact kernel_mass_le h hγ)

theorem mass_tends_zero:Tendsto mass atTop (𝓝 0):=by
  change Tendsto (fun γ:ℝ=>dampingPowerConstant (1/2)*γ^(-(1/2:ℝ))) atTop (𝓝 0)
  simpa only [mul_zero] using
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).const_mul (dampingPowerConstant (1/2))

theorem exists_contraction_weight (K:ℝ):∃γ:ℝ,1≤γ ∧ K*mass γ≤1/4:=by
  have hlim:Tendsto (fun γ:ℝ=>K*mass γ) atTop (𝓝 0):=by
    simpa only [mul_zero] using mass_tends_zero.const_mul K
  have hs:∀ᶠγ:ℝ in atTop,K*mass γ<1/4:=
    hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))
  obtain ⟨γ,hγ,hsmall⟩:=(eventually_ge_atTop (1:ℝ)).and hs |>.exists
  exact ⟨γ,hγ,hsmall.le⟩
end SHE.BieleckiKernel
