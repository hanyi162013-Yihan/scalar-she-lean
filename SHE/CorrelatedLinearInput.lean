module

public import SHE.CorrelatedCurrentHolder

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.CorrelatedLinearInput
open Set MeasureTheory ProbabilityTheory Real
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A linear random input is interpolated using its genuine second
moment and one genuine higher moment. The other factor may depend on
the same noise in an arbitrary way. -/
theorem energy [IsProbabilityMeasure μ]
    (D G : Ω→ℝ) (hD : MemLp D 2 μ) (hG : AEStronglyMeasurable G μ)
    {χ CD CG : ℝ} (hχ0 : 0≤χ) (hχ1 : χ<1)
    (hCD : 0≤CD) (hCG : 0≤CG) (p : ℕ) (hp : 0<p)
    (horder : 1≤(p:ℝ)*(1-χ))
    (hiD : Integrable (fun ω=>|D ω|^((4*(p:ℝ))*(1-χ))) μ)
    (hiG : Integrable (fun ω=>|G ω|^(4*p)) μ)
    (hbD : (∫ ω,|D ω|^((4*(p:ℝ))*(1-χ)) ∂μ)≤CD)
    (hbG : (∫ ω,|G ω|^(4*p) ∂μ)≤CG) :
    MemLp (fun ω=>D ω*G ω) 2 μ ∧
      (∫ ω,(D ω*G ω)^2 ∂μ)≤(∫ ω,D ω^2 ∂μ)^χ*((CD+CG)/2)^(1/(p:ℝ)) := by
  let H : Ω→ℝ := fun ω=>|D ω|^(1-χ)*G ω
  have hHm : AEStronglyMeasurable H μ :=
    (hD.aestronglyMeasurable.norm.aemeasurable.pow_const (1-χ)).aestronglyMeasurable.mul hG
  have hd (ω : Ω) : (|D ω|^(1-χ))^(2*p)=|D ω|^((2*(p:ℝ))*(1-χ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast
    ring
  have hdom (ω : Ω) : |H ω|^(2*p)≤
      (|D ω|^((4*(p:ℝ))*(1-χ))+|G ω|^(4*p))/2 := by
    have ha : 0≤|D ω|^((2*(p:ℝ))*(1-χ)) := rpow_nonneg (abs_nonneg _) _
    have hb : 0≤|G ω|^(2*p) := pow_nonneg (abs_nonneg _) _
    have heD : (|D ω|^((2*(p:ℝ))*(1-χ)))^2=|D ω|^((4*(p:ℝ))*(1-χ)) := by
      rw [←Real.rpow_mul_natCast (abs_nonneg _)]
      congr 1
      ring
    have heG : (|G ω|^(2*p))^2=|G ω|^(4*p) := by rw [←pow_mul];congr 1;omega
    have hh := sq_nonneg (|D ω|^((2*(p:ℝ))*(1-χ))-|G ω|^(2*p))
    change |(|D ω|^(1-χ)*G ω)|^(2*p)≤_
    rw [abs_mul,abs_of_nonneg (rpow_nonneg (abs_nonneg _) _),mul_pow,hd]
    nlinarith [heD,heG]
  have hiH : Integrable (fun ω=>|H ω|^(2*p)) μ := by
    apply ((hiD.add hiG).div_const 2).mono' (hHm.norm.pow (2*p))
    exact ae_of_all _ (fun ω=>by
      change ‖|H ω|^(2*p)‖≤_
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact hdom ω)
  have hbH : (∫ ω,|H ω|^(2*p) ∂μ)≤(CD+CG)/2 := by
    calc
      _≤∫ ω,(|D ω|^((4*(p:ℝ))*(1-χ))+|G ω|^(4*p))/2 ∂μ :=
        integral_mono hiH ((hiD.add hiG).div_const 2) hdom
      _=((∫ ω,|D ω|^((4*(p:ℝ))*(1-χ)) ∂μ)+(∫ ω,|G ω|^(4*p) ∂μ))/2 := by
        rw [integral_div,integral_add hiD hiG]
      _≤_ := div_le_div_of_nonneg_right (add_le_add hbD hbG) (by norm_num)
  have hmH : (∫⁻ ω,ENNReal.ofReal (‖H ω‖^(2*p)) ∂μ)≤ENNReal.ofReal ((CD+CG)/2) := by
    rw [←ofReal_integral_eq_lintegral_ofReal
      (by simpa only [Real.norm_eq_abs] using hiH)
      (ae_of_all _ (fun ω=>pow_nonneg (norm_nonneg (H ω)) _))]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hbH)
  have hh := CorrelatedCurrentHolder.energy_of_even_moment D H hD hHm hχ0 hχ1
    (div_nonneg (add_nonneg hCD hCG) (by norm_num)) p hp horder hmH
  have he (ω : Ω) : (|D ω|^χ*H ω)^2=(D ω*G ω)^2 := by
    have hd' : |D ω|^χ*|D ω|^(1-χ)=|D ω| := by
      rw [←Real.rpow_add_of_nonneg (abs_nonneg _) hχ0 (sub_pos.mpr hχ1).le]
      simp only [add_sub_cancel,Real.rpow_one]
    change (|D ω|^χ*(|D ω|^(1-χ)*G ω))^2=_
    rw [←mul_assoc,hd',mul_pow,mul_pow,sq_abs]
  have hsq : Integrable (fun ω=>(D ω*G ω)^2) μ :=
    hh.1.integrable_sq.congr (ae_of_all _ he)
  refine ⟨(memLp_two_iff_integrable_sq (hD.aestronglyMeasurable.mul hG)).mpr hsq,?_⟩
  exact (integral_congr_ae (ae_of_all _ he)).symm.trans_le hh.2

end SHE.CorrelatedLinearInput
