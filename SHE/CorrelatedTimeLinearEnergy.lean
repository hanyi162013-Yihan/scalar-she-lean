module

public import SHE.CorrelatedTimeAverage
public import SHE.ScoreSpatialCauchy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.CorrelatedTimeLinearEnergy
open MeasureTheory Real
variable {T Y:Type*} [MeasurableSpace T] [MeasurableSpace Y]

/-- Positive time Cauchy preserves the actual varying energy inside
one unsquared weight. The finite cap is used only for integrability. -/
theorem weighted_square (ν:Measure T) (A E:T→ℝ)
    (hA:Measurable A) (hAi:Integrable A ν) (hA0:∀t,0≤A t)
    (hE:Measurable E) (hE0:∀t,0≤E t)
    {M χ:ℝ} (hM:0≤M) (hχ:0≤χ) (hcap:∀t,E t≤M):
    Integrable (fun t=>A t*(E t)^χ) ν ∧
      (∫t,A t*(E t)^(χ/2) ∂ν)^2≤
        (∫t,A t ∂ν)*(∫t,A t*(E t)^χ ∂ν):=by
  have hi:Integrable (fun t=>A t*(E t)^χ) ν:=by
    apply (hAi.const_mul (M^χ)).mono' ((hA.mul (hE.pow_const _)).aestronglyMeasurable)
    apply ae_of_all
    intro t
    change ‖A t*(E t)^χ‖≤M^χ*A t
    rw [Real.norm_of_nonneg (mul_nonneg (hA0 t) (rpow_nonneg (hE0 t) _))]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (rpow_le_rpow (hE0 t) (hcap t) hχ) (hA0 t)
  have hh:=ScoreSpatialCauchy.weighted_sqrt_integral ν A (fun t=>(E t)^χ)
    hAi hi (hE.pow_const _) (ae_of_all _ hA0) (fun t=>rpow_nonneg (hE0 t) _)
  have he(t):sqrt ((E t)^χ)=(E t)^(χ/2):=by
    rw [sqrt_eq_rpow,←rpow_mul (hE0 t)]
    congr 1
    ring
  simp_rw [he] at hh
  refine ⟨hi,?_⟩
  have h0:0≤∫t,A t*(E t)^(χ/2) ∂ν:=
    integral_nonneg (fun t=>mul_nonneg (hA0 t) (rpow_nonneg (hE0 t) _))
  have hn:=sq_le_sq₀ h0 (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) |>.mpr hh.2
  simpa only [mul_pow,sq_sqrt (integral_nonneg hA0),
    sq_sqrt (integral_nonneg (fun t=>mul_nonneg (hA0 t) (rpow_nonneg (hE0 t) _)))] using hn

/-- Literal time averaging followed by positive Cauchy. This form is
adapted to moving-past Fubini: the true current energy occurs linearly
inside its original deterministic time weight. -/
theorem energy (ν:Measure T) [IsFiniteMeasure ν] (μ:Measure Y) [IsProbabilityMeasure μ]
    (F:T×Y→ℝ) (hF:Measurable F) (A E:T→ℝ)
    (hA:Measurable A) (hAi:Integrable A ν) (hA0:∀t,0≤A t)
    (hE:Measurable E) (hE0:∀t,0≤E t)
    {C M P χ:ℝ} (hC:0≤C) (hM:0≤M) (hP:0≤P) (hχ:0≤χ)
    (hcap:∀t,E t≤M)
    (hMom:∀ᵐ t ∂ν,Integrable (fun y=>|F (t,y)|^2) μ ∧
      (∫y,|F (t,y)|^2 ∂μ)≤C*(A t)^2*((E t)^χ+P^χ)):
    let G:=fun y=>∫t,F (t,y) ∂ν
    Integrable F (ν.prod μ) ∧ Integrable (fun y=>|G y|^2) μ ∧
      (∫y,|G y|^2 ∂μ)≤2*C*(∫t,A t ∂ν)*
        ((∫t,A t*(E t)^χ ∂ν)+(∫t,A t ∂ν)*P^χ):=by
  intro G
  have hh:=CorrelatedTimeAverage.energy ν μ F hF A E hA hAi hA0 hE hE0 hC hM hP hχ hcap hMom
  have hc:=weighted_square ν A E hA hAi hA0 hE hE0 hM hχ hcap
  refine ⟨hh.1,hh.2.1,hh.2.2.trans ?_⟩
  calc
    _≤2*C*((∫t,A t ∂ν)*(∫t,A t*(E t)^χ ∂ν)+(∫t,A t ∂ν)^2*P^χ):=
      mul_le_mul_of_nonneg_left (by linarith [hc.2]) (mul_nonneg (by norm_num) hC)
    _=_:=by ring

end SHE.CorrelatedTimeLinearEnergy
