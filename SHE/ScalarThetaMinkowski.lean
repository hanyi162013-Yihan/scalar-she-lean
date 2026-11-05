module
public import SHE.HilbertParameterAverage
public import SHE.ProfileL2
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.ScalarThetaMinkowski
open Set MeasureTheory Real ProfileL2
variable {Ω Θ:Type*}[MeasurableSpace Ω][MeasurableSpace Θ]

theorem bound (μ:Measure Ω)[IsProbabilityMeasure μ](τ:Measure Θ)[SFinite τ]
    (F:Θ×Ω→ℝ)(hF:Measurable F)(A:Θ→ℝ)(hAm:Measurable A)(hAi:Integrable A τ)(hA0:∀θ,0≤A θ)
    (hi:∀ᵐθ∂τ,Integrable (fun ω=>‖F (θ,ω)‖^2) μ)
    (hb:∀ᵐθ∂τ,(∫ω,‖F (θ,ω)‖^2 ∂μ)≤A θ^2):
    Integrable F (τ.prod μ) ∧ MemLp (fun ω=>∫θ,F (θ,ω) ∂τ) 2 μ ∧
      normTwo μ (fun ω=>∫θ,F (θ,ω) ∂τ)≤∫θ,A θ ∂τ:=by
  have he:=HilbertParameterAverage.energy μ τ F hF A hAm hAi hA0 hi hb
  have hm:Measurable (fun ω=>∫θ,F (θ,ω) ∂τ):=hF.stronglyMeasurable.integral_prod_left'.measurable
  refine ⟨he.1,(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr he.2.1,?_⟩
  have hsq:(normTwo μ (fun ω=>∫θ,F (θ,ω) ∂τ))^2=
      ∫ω,‖∫θ,F (θ,ω) ∂τ‖^2 ∂μ:=by
    rw [normTwo_sq]
    simp only [Real.norm_eq_abs,sq_abs]
  have hbnd:=he.2.2
  rw [←hsq] at hbnd
  have hAn:0≤∫θ,A θ ∂τ:=integral_nonneg hA0
  nlinarith [normTwo_nonneg μ (fun ω=>∫θ,F (θ,ω) ∂τ)]

/-- A genuine section L2 bound can be integrated over an arbitrary
sigma-finite physical history, with its true L1 envelope mass. -/
theorem of_normTwo (μ : Measure Ω) [IsProbabilityMeasure μ] (τ : Measure Θ) [SFinite τ]
    (F : Θ×Ω → ℝ) (hF : Measurable F) (A : Θ → ℝ) (hAm : Measurable A)
    (hAi : Integrable A τ) (hA0 : ∀ θ,0 ≤ A θ)
    (hm : ∀ᵐ θ ∂τ,MemLp (fun ω => F (θ,ω)) 2 μ)
    (hn : ∀ᵐ θ ∂τ,normTwo μ (fun ω => F (θ,ω)) ≤ A θ) :
    Integrable F (τ.prod μ) ∧ MemLp (fun ω => ∫ θ,F (θ,ω) ∂τ) 2 μ ∧
      normTwo μ (fun ω => ∫ θ,F (θ,ω) ∂τ) ≤ ∫ θ,A θ ∂τ := by
  have hi : ∀ᵐ θ ∂τ,Integrable (fun ω => ‖F (θ,ω)‖^2) μ := by
    filter_upwards [hm] with θ hθ
    exact (memLp_two_iff_integrable_sq_norm hθ.aestronglyMeasurable).mp hθ
  have hb : ∀ᵐ θ ∂τ,(∫ ω,‖F (θ,ω)‖^2 ∂μ) ≤ A θ^2 := by
    filter_upwards [hn] with θ hθ
    simp only [Real.norm_eq_abs,sq_abs]
    rw [←normTwo_sq]
    exact pow_le_pow_left₀ (normTwo_nonneg _ _) hθ 2
  exact bound μ τ F hF A hAm hAi hA0 hi hb

/-- An actual conditional second-moment estimate gives the sharp
sample-L2 theta integral, retaining all dependence of the marked word.
Only the genuine RMS envelope needs theta integrability. -/
theorem scaled_moment (μ:Measure Ω)[IsProbabilityMeasure μ](τ:Measure Θ)[IsProbabilityMeasure τ]
    (F:Θ×Ω→ℝ)(hF:Measurable F)(T:Θ→ℝ)(hTm:Measurable T)(hTi:Integrable T τ)(hT0:∀θ,0≤T θ)
    (C K:ℝ)(hC:0≤C)(hK:0≤K)
    (hp:∀ᵐθ∂τ,Integrable (fun ω=>|F (θ,ω)|^2) μ ∧
      (∫ω,|F (θ,ω)|^2 ∂μ)≤C*(K*T θ)^2):
    Integrable F (τ.prod μ) ∧ MemLp (fun ω=>∫θ,F (θ,ω) ∂τ) 2 μ ∧
      normTwo μ (fun ω=>∫θ,F (θ,ω) ∂τ)≤Real.sqrt C*K*(∫θ,T θ ∂τ):=by
  have hi:∀ᵐθ∂τ,Integrable (fun ω=>‖F (θ,ω)‖^2) μ:=by
    simpa only [Real.norm_eq_abs] using hp.mono (fun _ h=>h.1)
  have hb:∀ᵐθ∂τ,(∫ω,‖F (θ,ω)‖^2 ∂μ)≤(Real.sqrt C*K*T θ)^2:=by
    filter_upwards [hp] with θ hθ
    simpa only [Real.norm_eq_abs,mul_pow,Real.sq_sqrt hC,mul_assoc] using hθ.2
  have hh:=bound μ τ F hF (fun θ=>Real.sqrt C*K*T θ)
    (hTm.const_mul _) (hTi.const_mul _) (fun θ=>mul_nonneg (mul_nonneg (Real.sqrt_nonneg C) hK) (hT0 θ)) hi hb
  simpa only [integral_const_mul] using hh
end SHE.ScalarThetaMinkowski
