module

public import SHE.RealMomentBound
public import SHE.ProfileL2
public import SHE.FractionalMoment
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.CorrelatedCurrentHolder
open Set MeasureTheory ProbabilityTheory Real ProfileL2
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Fractional current-input smallness uses only its true L² moment.
Every other (possibly dependent) score and rough displacement remains in
one higher-moment factor. Separate second moments are never multiplied. -/
theorem energy (D G : Ω→ℝ) (hD : MemLp D 2 μ) (hGm : AEStronglyMeasurable G μ)
    {χ : ℝ} (hχ0 : 0≤χ) (hχ1 : χ<1)
    (hG : Integrable (fun ω => |G ω|^(2/(1-χ))) μ) :
    MemLp (fun ω => |D ω|^χ*G ω) 2 μ ∧
      (∫ ω,(|D ω|^χ*G ω)^2 ∂μ) ≤
        (∫ ω,D ω^2 ∂μ)^χ*(∫ ω,|G ω|^(2/(1-χ)) ∂μ)^(1-χ) := by
  have hδ : 0<1-χ := sub_pos.mpr hχ1
  let f := fun ω => ENNReal.ofReal (D ω^2)
  let g := fun ω => ENNReal.ofReal (|G ω|^(2/(1-χ)))
  have hf : AEMeasurable f μ := ENNReal.continuous_ofReal.measurable.comp_aemeasurable
    (hD.aestronglyMeasurable.pow 2).aemeasurable
  have hg : AEMeasurable g μ := ENNReal.continuous_ofReal.measurable.comp_aemeasurable
    (hGm.norm.aemeasurable.pow_const (2/(1-χ)))
  have hh := ENNReal.lintegral_mul_norm_pow_le hf hg hχ0 hδ.le (by ring : χ+(1-χ)=1)
  have he (ω : Ω) : ENNReal.ofReal ((|D ω|^χ*G ω)^2)=f ω^χ*g ω^(1-χ) := by
    dsimp [f,g]
    have hd : (|D ω|^χ)^2=(D ω^2)^χ := by
      rw [←Real.rpow_mul_natCast (abs_nonneg (D ω))]
      change |D ω|^(χ*(2:ℝ))=(D ω^2)^χ
      calc
        _=|D ω|^(((2:ℕ):ℝ)*χ) := congrArg (fun z : ℝ => |D ω|^z) (by norm_num;ring)
        _=(|D ω|^2)^χ := Real.rpow_natCast_mul (abs_nonneg (D ω)) 2 χ
        _=_ := by rw [sq_abs]
    have hg' : (|G ω|^(2/(1-χ)))^(1-χ)=G ω^2 := by
      rw [←Real.rpow_mul (abs_nonneg (G ω)),div_mul_cancel₀ 2 hδ.ne',Real.rpow_two,sq_abs]
    rw [mul_pow,hd,ENNReal.ofReal_mul (rpow_nonneg (sq_nonneg _) _),
      ENNReal.ofReal_rpow_of_nonneg (sq_nonneg (D ω)) hχ0,
      ENNReal.ofReal_rpow_of_nonneg (rpow_nonneg (abs_nonneg (G ω)) _) hδ.le,hg']
  simp_rw [←he] at hh
  have hdf := ofReal_integral_eq_lintegral_ofReal hD.integrable_sq
    (ae_of_all _ (fun ω => sq_nonneg (D ω)))
  have hgf := ofReal_integral_eq_lintegral_ofReal hG
    (ae_of_all _ (fun ω => rpow_nonneg (abs_nonneg (G ω)) _))
  change ENNReal.ofReal (∫ ω,D ω^2 ∂μ)=∫⁻ ω,f ω ∂μ at hdf
  change ENNReal.ofReal (∫ ω,|G ω|^(2/(1-χ)) ∂μ)=∫⁻ ω,g ω ∂μ at hgf
  rw [←hdf,←hgf,ENNReal.ofReal_rpow_of_nonneg
    (integral_nonneg (fun ω => sq_nonneg (D ω))) hχ0,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (fun ω => rpow_nonneg (abs_nonneg (G ω)) _)) hδ.le,
    ←ENNReal.ofReal_mul (rpow_nonneg (integral_nonneg (fun ω => sq_nonneg (D ω))) _)] at hh
  have hzm : AEStronglyMeasurable (fun ω => (|D ω|^χ*G ω)^2) μ :=
    ((hD.aestronglyMeasurable.norm.aemeasurable.pow_const χ).aestronglyMeasurable.mul hGm).pow 2
  have hb := RealMomentBound.integral_bound μ _ hzm (fun ω => sq_nonneg _)
    (mul_nonneg (rpow_nonneg (integral_nonneg (fun ω => sq_nonneg _)) _)
      (rpow_nonneg (integral_nonneg (fun ω => rpow_nonneg (abs_nonneg (G ω)) _)) _)) hh
  exact ⟨(memLp_two_iff_integrable_sq
    ((hD.aestronglyMeasurable.norm.aemeasurable.pow_const χ).aestronglyMeasurable.mul hGm)).mpr hb.1,hb.2⟩

/-- One sufficiently high *integer* moment of the correlated remainder
is enough for the fractional current-input estimate. The distinguished
input still uses only its genuine second moment. -/
theorem energy_of_even_moment [IsProbabilityMeasure μ]
    (D G : Ω→ℝ) (hD : MemLp D 2 μ) (hGm : AEStronglyMeasurable G μ)
    {χ C : ℝ} (hχ0 : 0≤χ) (hχ1 : χ<1) (hC : 0≤C)
    (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (hMoment : (∫⁻ ω,ENNReal.ofReal (‖G ω‖^(2*p)) ∂μ)≤ENNReal.ofReal C) :
    MemLp (fun ω => |D ω|^χ*G ω) 2 μ ∧
      (∫ ω,(|D ω|^χ*G ω)^2 ∂μ) ≤ (∫ ω,D ω^2 ∂μ)^χ*C^(1/(p:ℝ)) := by
  have hp' : 0<(p:ℝ) := by exact_mod_cast hp
  have hδ : 0<1-χ := sub_pos.mpr hχ1
  let δ : ℝ := 1/((p:ℝ)*(1-χ))
  have hδ0 : 0≤δ := div_nonneg (by norm_num) (mul_pos hp' hδ).le
  have hδ1 : δ≤1 := (div_le_iff₀ (mul_pos hp' hδ)).mpr (by simpa using horder)
  have hb : (∫⁻ ω,ENNReal.ofReal (‖G ω‖^(((2*p:ℕ):ℝ))) ∂μ)≤ENNReal.ofReal C := by
    simpa only [Real.rpow_natCast] using hMoment
  have hh := FractionalMoment.moment_fraction hGm hδ0 hδ1 hC hb
  have he : (((2*p:ℕ):ℝ))*δ=2/(1-χ) := by
    dsimp [δ]
    push_cast
    field_simp
  rw [he] at hh
  have hr := RealMomentBound.integral_bound μ (fun ω => |G ω|^(2/(1-χ)))
    (hGm.norm.aemeasurable.pow_const _).aestronglyMeasurable
    (fun _ => rpow_nonneg (abs_nonneg _) _) (rpow_nonneg hC δ)
    (by simpa only [Real.norm_eq_abs] using hh)
  have hz := energy D G hD hGm hχ0 hχ1 hr.1
  refine ⟨hz.1,hz.2.trans ?_⟩
  have hpow := rpow_le_rpow (integral_nonneg (fun ω => rpow_nonneg (abs_nonneg (G ω)) _))
    hr.2 hδ.le
  have heC : (C^δ)^(1-χ)=C^(1/(p:ℝ)) := by
    rw [←Real.rpow_mul hC]
    congr 1
    dsimp [δ]
    field_simp
  exact mul_le_mul_of_nonneg_left (hpow.trans_eq heC)
    (rpow_nonneg (integral_nonneg (fun ω => sq_nonneg (D ω))) χ)

end SHE.CorrelatedCurrentHolder
