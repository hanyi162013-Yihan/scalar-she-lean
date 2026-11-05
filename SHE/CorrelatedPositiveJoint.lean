module

public import SHE.CorrelatedPositiveAverage
public import SHE.ConditionalSquareL1
public import SHE.CorrelatedCurrentHolder
public import SHE.WeightedSpatialMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.CorrelatedPositiveJoint
open Set MeasureTheory ProbabilityTheory Real
open scoped ENNReal
variable {Y W:Type*} [MeasurableSpace Y] [MeasurableSpace W]

/-- Positive spatial averaging of a fractional TRUE current input and
an arbitrarily dependent random Gaussian-word amplitude. Holder is
applied on the ENTIRE sample/output space before old-space averaging;
no pointwise heat-input loss or independence assumption is introduced. -/
theorem energy (μ:Measure Y) [IsProbabilityMeasure μ] (ν:Measure W) [IsProbabilityMeasure ν]
    (F D:Y×W→ℝ) (hF:Measurable F) (hD:Measurable D)
    (H:W→ℝ) (hH:Measurable H) (hHi:Integrable H ν) (hH0:∀w,0≤H w)
    {χ C E:ℝ} (hχ:0≤χ) (hχ1:χ<1) (hC:0≤C) (hE:0≤E)
    (p:ℕ) (hp:0<p) (horder:1≤(p:ℝ)*(1-χ))
    (hD2:∀ᵐ w ∂ν,MemLp (fun y=>D (y,w)) 2 μ ∧ (∫y,D (y,w)^2 ∂μ)≤E)
    (hMom:∀ᵐ w ∂ν,Integrable (fun y=>|F (y,w)|^(2*p)) μ ∧
      (∫y,|F (y,w)|^(2*p) ∂μ)≤C*(H w)^(2*p)) :
    let G:=fun y=>∫w,|D (y,w)|^χ*F (y,w) ∂ν
    Integrable (fun z:Y×W=>|D z|^χ*F z) (μ.prod ν) ∧
    Integrable (fun y=>|G y|^2) μ ∧
      (∫y,|G y|^2 ∂μ)≤C^(1/(p:ℝ))*E^χ*(∫w,H w ∂ν)^2 := by
  intro G
  let V:=fun z:Y×W=>|D z|^χ*F z
  have hVm:Measurable V:=((continuous_abs.measurable.comp hD).pow_const χ).mul hF
  have hp':0<(p:ℝ):=by exact_mod_cast hp
  have hsec:∀ᵐ w ∂ν,Integrable (fun y=>|V (y,w)|^(2*1)) μ ∧
      (∫y,|V (y,w)|^(2*1) ∂μ)≤(C^(1/(p:ℝ))*E^χ)*(H w)^(2*1) := by
    filter_upwards [hD2,hMom] with w hd hm
    have hFm:Measurable (fun y=>F (y,w)):=hF.comp (measurable_id.prodMk measurable_const)
    have he:=ofReal_integral_eq_lintegral_ofReal hm.1
      (ae_of_all μ (fun y=>pow_nonneg (abs_nonneg (F (y,w))) (2*p)))
    have hlin:(∫⁻y,ENNReal.ofReal (‖F (y,w)‖^(2*p)) ∂μ)≤ENNReal.ofReal (C*(H w)^(2*p)) := by
      simp only [Real.norm_eq_abs]
      rw [←he]
      exact ENNReal.ofReal_le_ofReal hm.2
    have hh:=CorrelatedCurrentHolder.energy_of_even_moment (fun y=>D (y,w)) (fun y=>F (y,w))
      hd.1 hFm.aestronglyMeasurable hχ hχ1 (mul_nonneg hC (pow_nonneg (hH0 w) _)) p hp horder hlin
    have hscale:(C*(H w)^(2*p))^(1/(p:ℝ))=C^(1/(p:ℝ))*(H w)^2 := by
      rw [mul_rpow hC (pow_nonneg (hH0 w) _),←rpow_natCast_mul (hH0 w) (2*p) (1/(p:ℝ))]
      have ha:((2*p:ℕ):ℝ)*(1/(p:ℝ))=2 := by push_cast;field_simp
      rw [ha,rpow_two]
    have hb:=hh.2.trans (mul_le_mul_of_nonneg_right
      (rpow_le_rpow (integral_nonneg (fun y=>sq_nonneg _)) hd.2 hχ)
      (rpow_nonneg (mul_nonneg hC (pow_nonneg (hH0 w) _)) _))
    rw [hscale] at hb
    refine ⟨?_,?_⟩
    · simpa only [V,mul_one,sq_abs] using hh.1.integrable_sq
    · simpa only [V,mul_one,one_mul,sq_abs,mul_assoc,mul_left_comm,mul_comm] using hb
  have hj:=ConditionalSquareL1.joint_integrable μ ν V hVm H hHi hH0
    (mul_nonneg (rpow_nonneg hC _) (rpow_nonneg hE _))
    (hsec.mono (fun _ h=>by simpa only [mul_one] using h.1))
    (hsec.mono (fun _ h=>by simpa only [mul_one] using h.2))
  refine ⟨hj.1,?_⟩
  exact CorrelatedPositiveAverage.energy μ ν F D hF hD H hH hHi hH0 hχ hχ1 hC hE p hp horder hD2 hMom

end SHE.CorrelatedPositiveJoint
