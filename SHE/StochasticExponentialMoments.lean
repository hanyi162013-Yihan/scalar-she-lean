module
public import SHE.StandardTerminalNovikov
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.StochasticExponential
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E][InnerProductSpace ℝ E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (J:StandardTerminalIto (C:=E) (E:=ℝ) 𝓕 μ H)

theorem bracket_smul (c:ℝ)(u:Process (E:=E) 𝓕 μ H):
    bracket 𝓕 μ H (c • u)=ᵐ[μ] (fun ω=>c^2*bracket 𝓕 μ H u ω):=by
  have he:(c • u)=ᵐ[energyMeasure μ H] (fun p=>c • u p):=
    ae_eq_of_ae_eq_trim (Lp.coeFn_smul c u)
  filter_upwards [Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae he)] with ω hω
  unfold bracket
  calc
    _ = ∫t,c^2*‖u (t,ω)‖^2 ∂timeMeasure H:=by
      apply integral_congr_ae
      filter_upwards [hω] with t ht
      change (c • u) (t,ω)=c • u (t,ω) at ht
      rw [ht,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    _ = _:=integral_const_mul _ _

theorem integral_smul (c:ℝ)(u:Process (E:=E) 𝓕 μ H):
    J.integral (c • u)=ᵐ[μ] (fun ω=>c*J.integral u ω):=by
  rw [map_smul]
  exact Lp.coeFn_smul c (J.integral u)

theorem density_measurable (u:Process (E:=E) 𝓕 μ H):Measurable (density 𝓕 μ H J u):=
  (((Lp.stronglyMeasurable (J.integral u)).measurable.neg).sub
    ((bracket_measurable 𝓕 μ H u).div_const 2)).exp

theorem mean_one_of_bound (hNovikov:StandardTerminalNovikov J)
    (u:Process (E:=E) 𝓕 μ H)(C:ℝ)(hcap:∀ᵐω∂μ,bracket 𝓕 μ H u ω≤C):
    Integrable (density 𝓕 μ H J u) μ ∧ (∫ω,density 𝓕 μ H J u ω ∂μ)=1:=by
  apply hNovikov u
  apply Integrable.of_bound (((bracket_measurable 𝓕 μ H u).div_const 2).exp).aestronglyMeasurable (Real.exp (C/2))
  filter_upwards [hcap] with ω hω
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The bounded-energy exponential has a genuine second moment bounded
by exp(1). This derives from Novikov for the scaled actual input; it is
not an extra stochastic input or an assumed density-moment estimate. -/
theorem second_moment (hNovikov:StandardTerminalNovikov J)
    (u:Process (E:=E) 𝓕 μ H)(hcap:∀ᵐω∂μ,bracket 𝓕 μ H u ω≤1):
    MemLp (density 𝓕 μ H J u) 2 μ ∧
      (∫ω,(density 𝓕 μ H J u ω)^2 ∂μ)≤Real.exp 1:=by
  have hB:=bracket_smul 𝓕 μ H (2:ℝ) u
  have hI:=integral_smul 𝓕 μ H J (2:ℝ) u
  have hcap2:∀ᵐω∂μ,bracket 𝓕 μ H ((2:ℝ) • u) ω≤4:=by
    filter_upwards [hB,hcap] with ω hb hc
    rw [hb]
    nlinarith
  have hmean:=mean_one_of_bound 𝓕 μ H J hNovikov ((2:ℝ) • u) 4 hcap2
  have hbound:∀ᵐω∂μ,(density 𝓕 μ H J u ω)^2≤Real.exp 1*density 𝓕 μ H J ((2:ℝ) • u) ω:=by
    filter_upwards [hB,hI,hcap] with ω hb hi hc
    have he:(density 𝓕 μ H J u ω)^2=
        density 𝓕 μ H J ((2:ℝ) • u) ω*Real.exp (bracket 𝓕 μ H u ω):=by
      unfold density
      rw [pow_two,←Real.exp_add,←Real.exp_add,hi,hb]
      congr 1
      ring
    rw [he,mul_comm (Real.exp 1)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hc) (Real.exp_pos _).le
  have hi:Integrable (fun ω=>(density 𝓕 μ H J u ω)^2) μ:=by
    apply (hmean.1.const_mul (Real.exp 1)).mono'
      ((density_measurable 𝓕 μ H J u).pow_const 2).aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (density 𝓕 μ H J u ω))]
    exact hω
  refine ⟨(memLp_two_iff_integrable_sq ((density_measurable 𝓕 μ H J u).aestronglyMeasurable)).mpr hi,?_⟩
  calc
    _ ≤ ∫ω,Real.exp 1*density 𝓕 μ H J ((2:ℝ) • u) ω ∂μ:=
      integral_mono_ae hi (hmean.1.const_mul (Real.exp 1)) hbound
    _ = Real.exp 1:=by rw [integral_const_mul,hmean.2,mul_one]
end SHE.StochasticExponential
