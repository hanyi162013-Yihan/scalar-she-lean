module
public import SHE.WeightedSFiniteMoments

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.FreshMassInterpolation
open Set MeasureTheory Real
variable {Ω X:Type} [MeasurableSpace Ω] [MeasurableSpace X]

theorem two_caps {E A B:ℝ}(hA:0≤A)(hB:0≤B)(hEA:E≤A^2)(hEB:E≤B^2):E≤A*B:=by
  by_cases h:A≤B
  · exact hEA.trans (by nlinarith [mul_le_mul_of_nonneg_left h hA])
  · exact hEB.trans (by nlinarith [mul_le_mul_of_nonneg_right (le_of_not_ge h) hB])

/-- Spatial Minkowski is applied before the sample square. A genuine
uniform fresh mass cap then interpolates with the old-block moment
bound, without assuming independence of the current mean or input. -/
theorem mass_energy (μ:Measure Ω)[IsProbabilityMeasure μ](ν:Measure X)[SFinite ν]
    (F:Ω×X→ℝ)(hF:Measurable F)(V:X→ℝ)(hV:Measurable V)
    (hVi:Integrable V ν)(hV0:∀x,0≤V x)
    {K C B:ℝ}(hK:0≤K)(hC:0≤C)(hB:0≤B)
    (hi:∀ᵐx∂ν,Integrable (fun ω=>|F (ω,x)|^2) μ)
    (hb:∀ᵐx∂ν,(∫ω,|F (ω,x)|^2 ∂μ)≤C*(V x*K)^2)
    (hfresh:∀ᵐω∂μ,(∫x,|F (ω,x)| ∂ν)≤B):
    Integrable (fun ω=>(∫x,|F (ω,x)| ∂ν)^2) μ ∧
      (∫ω,(∫x,|F (ω,x)| ∂ν)^2 ∂μ)≤
        sqrt C*(K*∫x,V x ∂ν)*B := by
  have hm:=WeightedSFiniteMoments.nonnegative_envelope μ ν (fun z=>|F z|)
    (continuous_abs.measurable.comp hF) (fun x=>V x*K) (hV.mul_const K) (hVi.mul_const K)
    (fun x=>mul_nonneg (hV0 x) hK) 1 (by norm_num) C hC
      (by simpa only [abs_abs,show 2*1=2 by rfl] using hi)
      (by simpa only [abs_abs,show 2*1=2 by rfl] using hb)
  have hnon (ω:Ω):0≤∫x,|F (ω,x)| ∂ν:=integral_nonneg (fun _=>abs_nonneg _)
  have hmi:Integrable (fun ω=>(∫x,|F (ω,x)| ∂ν)^2) μ:=by
    simpa only [show 2*1=2 by rfl,sq_abs] using hm.1
  let G:=K*∫x,V x ∂ν
  have hG:0≤G:=mul_nonneg hK (integral_nonneg hV0)
  have hgood:(∫ω,(∫x,|F (ω,x)| ∂ν)^2 ∂μ)≤(sqrt C*G)^2:=by
    have hh:=hm.2
    simp only [show 2*1=2 by rfl,sq_abs,integral_mul_const] at hh
    rw [mul_pow,Real.sq_sqrt hC]
    simpa only [G,mul_comm] using hh
  have hbad:(∫ω,(∫x,|F (ω,x)| ∂ν)^2 ∂μ)≤B^2:=by
    have hh:=integral_mono_ae hmi (integrable_const (B^2:ℝ)) (hfresh.mono (fun ω h=>
      pow_le_pow_left₀ (hnon ω) h 2))
    simpa only [integral_const,probReal_univ,one_smul] using hh
  exact ⟨hmi,two_caps (mul_nonneg (Real.sqrt_nonneg _) hG) hB hgood hbad⟩

end SHE.FreshMassInterpolation
