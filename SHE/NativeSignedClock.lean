module

public import SHE.SignedDamping
public import SHE.NativeHeatObservation
public import SHE.PredictableTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.NativeSignedClock
open Set MeasureTheory Real NativeHeatObservation PredictableL2
open scoped NNReal ENNReal

def constant (ρ:ℝ):ℝ:=1+timeScale^(1/2:ℝ)+timeScale^(1/2+ρ)

theorem constant_nonneg (ρ:ℝ):0≤constant ρ:=by
  unfold constant
  linarith [rpow_nonneg timeScale_pos.le (1/2:ℝ),rpow_nonneg timeScale_pos.le (1/2+ρ)]

theorem div_neg_rpow {t:ℝ} (ht:0≤t) (a:ℝ):
    (t/timeScale)^(-a)=t^(-a)*timeScale^a:=by
  rw [Real.div_rpow ht timeScale_pos.le,Real.rpow_neg timeScale_pos.le,
    div_eq_mul_inv,inv_inv]

theorem majorant {Λ t:ℝ} (hΛ:0≤Λ) (ht:0<t) (ρ:ℝ):
    Λ^ρ*(t/timeScale)^(-(1/2:ℝ))+(t/timeScale)^(-(1/2:ℝ)-ρ)+(Λ^ρ+1)≤
      constant ρ*(Λ^ρ*t^(-(1/2:ℝ))+t^(-(1/2:ℝ)-ρ)+(Λ^ρ+1)):=by
  have hc1:timeScale^(1/2:ℝ)≤constant ρ:=by unfold constant;linarith [rpow_nonneg timeScale_pos.le (1/2:ℝ),rpow_nonneg timeScale_pos.le (1/2+ρ)]
  have hc2:timeScale^(1/2+ρ)≤constant ρ:=by unfold constant;linarith [rpow_nonneg timeScale_pos.le (1/2:ℝ),rpow_nonneg timeScale_pos.le (1/2+ρ)]
  have hc0:1≤constant ρ:=by unfold constant;linarith [rpow_nonneg timeScale_pos.le (1/2:ℝ),rpow_nonneg timeScale_pos.le (1/2+ρ)]
  rw [div_neg_rpow ht.le (1/2),show -(1/2:ℝ)-ρ=-(1/2+ρ) by ring,
    div_neg_rpow ht.le (1/2+ρ)]
  have hA:=mul_le_mul_of_nonneg_left hc1
    (mul_nonneg (rpow_nonneg hΛ ρ) (rpow_nonneg ht.le (-(1/2:ℝ))))
  have hB:=mul_le_mul_of_nonneg_left hc2 (rpow_nonneg ht.le (-(1/2+ρ)))
  have hD:=mul_le_mul_of_nonneg_right hc0 (show 0≤Λ^ρ+1 by positivity)
  calc
    _≤(Λ^ρ*t^(-(1/2:ℝ)))*constant ρ+t^(-(1/2+ρ))*constant ρ+constant ρ*(Λ^ρ+1):=by
      simpa only [mul_assoc,one_mul] using add_le_add (add_le_add hA hB) hD
    _=_:=by ring

def kernel (Λ ρ:ℝ):ℝ→ℝ≥0∞:=
  (Ioi 0).indicator (fun t=>ENNReal.ofReal (exp (-2*Λ*t)*
    (Λ^ρ*(t/timeScale)^(-(1/2:ℝ))+(t/timeScale)^(-(1/2:ℝ)-ρ)+(Λ^ρ+1))))

theorem kernel_measurable (Λ ρ:ℝ):Measurable (kernel Λ ρ):=by
  unfold kernel
  apply Measurable.indicator _ measurableSet_Ioi
  fun_prop

theorem kernel_le {Λ:ℝ} (hΛ:0≤Λ) (ρ t:ℝ):
    kernel Λ ρ t≤ENNReal.ofReal (constant ρ)*signedDampedKernel Λ ρ t:=by
  by_cases ht:0<t
  · rw [kernel,indicator_of_mem (show t∈Ioi (0:ℝ) from ht),signedDampedKernel,indicator_of_mem (show t∈Ioi (0:ℝ) from ht),
      ←ENNReal.ofReal_mul (constant_nonneg ρ)]
    apply ENNReal.ofReal_le_ofReal
    have hb:=mul_le_mul_of_nonneg_left (majorant hΛ ht ρ) (exp_pos (-2*Λ*t)).le
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hb
  · simp only [kernel,signedDampedKernel,indicator_of_notMem (show t∉Ioi (0:ℝ) from ht),mul_zero]
    exact le_refl _

theorem mass {Λ ρ:ℝ} (hΛ:1≤Λ) (hρ0:0≤ρ) (hρ1:ρ<1/2):
    (∫⁻t:ℝ,kernel Λ ρ t)≤
      ENNReal.ofReal (constant ρ*signedDampingConstant ρ*Λ^(ρ-1/2)):=by
  calc
    _≤∫⁻t:ℝ,ENNReal.ofReal (constant ρ)*signedDampedKernel Λ ρ t:=
      lintegral_mono (kernel_le (zero_le_one.trans hΛ) ρ)
    _=ENNReal.ofReal (constant ρ)*(∫⁻t:ℝ,signedDampedKernel Λ ρ t):=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _≤ENNReal.ofReal (constant ρ)*ENNReal.ofReal (signedDampingConstant ρ*Λ^(ρ-1/2)):=
      mul_le_mul' le_rfl (signedDampedKernel_mass hΛ hρ0 hρ1)
    _=_:=by rw [←ENNReal.ofReal_mul (constant_nonneg ρ)];congr 1;ring

/-- Native nonnegative physical time has exactly the same convolution
mass inequality, on the original full horizon in both variables. -/
theorem convolution (K:ℝ→ℝ≥0∞) (F : ℝ≥0 → ℝ≥0∞)
    (hK:Measurable K) (hF:Measurable F) (H:ℝ≥0):
    (∫⁻t,∫⁻s,K ((t:ℝ)-(s:ℝ))*F s ∂timeMeasure H ∂timeMeasure H)≤
      (∫⁻u:ℝ,K u)*(∫⁻s,F s ∂timeMeasure H):=by
  have he:(∫⁻t,∫⁻s,K ((t:ℝ)-(s:ℝ))*F s ∂timeMeasure H ∂timeMeasure H)=
      ∫⁻t in Ioc (0:ℝ) (H:ℝ),∫⁻s in Ioc (0:ℝ) (H:ℝ),K (t-s)*F s.toNNReal:=by
    rw [timeMeasure_lintegral]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [timeMeasure_lintegral,Real.coe_toNNReal _ ht.1.le]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.coe_toNNReal _ hs.1.le]
  rw [he,timeMeasure_lintegral]
  exact finite_time_convolution_energy_bound K _ hK (hF.comp measurable_real_toNNReal) _

end SHE.NativeSignedClock
