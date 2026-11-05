module
public import SHE.PolynomialGaussianTime
public import SHE.HeatTorus
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.GaussianCircleMass
open Set MeasureTheory Real AddCircle
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

def decay (s L r:ℝ):ℝ:=min 1 ((L*r)^(-s))

theorem decay_nonneg {s L r:ℝ}(hL:0≤L)(hr:0≤r):0≤decay s L r:=
  le_min (by norm_num) (Real.rpow_nonneg (mul_nonneg hL hr) _)

theorem mass {s L:ℝ}(hs:1<s)(hL:0<L):
    (∫x:UnitAddCircle,decay s L ‖x‖ ∂haarAddCircle)≤2*(1+1/(s-1))*L⁻¹:=by
  let g:ℝ→ℝ:=decay s L
  let f:ℝ→ℝ:=fun x=>g |x|
  have hgm:Measurable g:=by unfold g decay;fun_prop
  have hfm:Measurable f:=hgm.comp continuous_abs.measurable
  have hfb:∀x,‖f x‖≤1:=by
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (decay_nonneg hL.le (abs_nonneg _))]
    exact min_le_left _ _
  have hfi(a b:ℝ):IntervalIntegrable f volume a b:=by
    apply IntervalIntegrable.mono_fun (intervalIntegrable_const (c:=(1:ℝ))) hfm.aestronglyMeasurable
    exact ae_of_all _ (fun x=>by simpa only [norm_one] using hfb x)
  have hgi:IntegrableOn g (Ioi 0):=by
    have he:PolynomialGaussianTime.kernel 1 s L=g:=by
      funext x
      simp only [PolynomialGaussianTime.kernel,g,decay,sub_self,Real.rpow_zero,one_mul]
    rw [←he]
    exact PolynomialGaussianTime.integrable (γ:=1) (by norm_num) hs hL
  have hgint:(∫x in Ioi (0:ℝ),g x)=(1+1/(s-1))*L⁻¹:=by
    simpa only [PolynomialGaussianTime.kernel,sub_self,Real.rpow_zero,one_mul,div_one,
      Real.rpow_neg_one,g,decay] using
      (PolynomialGaussianTime.integral (γ:=1) (by norm_num) hs hL)
  have hp:(∫x in (0:ℝ)..(1/2:ℝ),f x)≤(1+1/(s-1))*L⁻¹:=by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    have he:(∫x in Ioc (0:ℝ) (1/2),f x)=(∫x in Ioc (0:ℝ) (1/2),g x):=by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      simp only [f,abs_of_pos hx.1]
    rw [he,←hgint]
    exact setIntegral_mono_set hgi
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx; exact decay_nonneg hL.le hx.le)
      (ae_of_all _ (fun x hx=>hx.1))
  have hn:(∫x in (-1/2:ℝ)..0,f x)=(∫x in (0:ℝ)..(1/2:ℝ),f x):=by
    have he:=intervalIntegral.integral_comp_neg f (a:=(0:ℝ)) (b:=(1/2:ℝ))
    simpa only [f,abs_neg,neg_zero,neg_div] using he.symm
  have hsum:(∫x in (-1/2:ℝ)..(1/2:ℝ),f x)≤2*(1+1/(s-1))*L⁻¹:=by
    rw [←intervalIntegral.integral_add_adjacent_intervals (hfi (-1/2) 0) (hfi 0 (1/2)),hn]
    linarith
  have hv:(volume:Measure UnitAddCircle)=haarAddCircle:=by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    norm_num
  rw [←hv]
  have he:=UnitAddCircle.intervalIntegral_preimage (-1/2:ℝ) (fun x:UnitAddCircle=>g ‖x‖)
  have he':(∫x in (-1/2:ℝ)..(1/2:ℝ),g ‖(x:UnitAddCircle)‖)=
      ∫x:UnitAddCircle,g ‖x‖:=by convert! he using 1 <;> norm_num
  rw [←he']
  convert! hsum using 1
  apply intervalIntegral.integral_congr
  intro x hx
  have hx':x∈Icc (-1/2:ℝ) (1/2:ℝ):=by simpa only [uIcc_of_le (by norm_num : (-1/2:ℝ)≤1/2)] using hx
  have hab:|x|≤1/2:=abs_le.mpr (by constructor <;> linarith [hx'.1,hx'.2])
  change g ‖(x:UnitAddCircle)‖=g |x|
  rw [(AddCircle.norm_coe_eq_abs_iff (p:=1) one_ne_zero).mpr (by simpa using hab)]

end SHE.GaussianCircleMass
