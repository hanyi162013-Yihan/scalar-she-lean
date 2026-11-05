module
public import SHE.ParametricStoppedHaarEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ParametricStoppedHaarVersion
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier ParametricStoppedHaarRows
open scoped NNReal ENNReal
local instance parametricStoppedHaarVersion_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance parametricStoppedHaarVersion_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance parametricStoppedHaarVersion_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω:Type*}{X:Type}[MeasurableSpace Ω][MeasurableSpace X]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable {ell M:ℝ}(hell:0<ell)(hM:0≤M)
variable (v b q:X→ℝ≥0)(center:X→HeatCircle)(f:X×(ℝ≥0×Ω)→EllipticField ell M)
variable (hf:StronglyMeasurable[((inferInstance:MeasurableSpace X).prod 𝓕.predictable)] f)
variable (hv:Measurable v)(hb:Measurable b)(hq:Measurable q)(hc:Measurable center)
variable (hqb:∀x,q x≤b x)(hbH:∀x,b x≤H)(hH:(H:ℝ)≤1)
local notation "Raw"=>ParametricStoppedHaarRows.raw hell v b q center f
local notation "Input"=>ParametricStoppedHaarRows.process 𝓕 μ H hell hM v b q center f hf hqb hbH

include hv hb hq hc hH in
/-- Ordinary parameterized stochastic Fubini has ALL analytic
applicability derived for the genuine moving stopped native rows.
The jointly Borel output is a version of the SAME original J. -/
theorem exists_version (ν:Measure X)[IsFiniteMeasure ν]
    (J:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoParameterFubini J):
    ∃Y:X×Ω→ℝ,Measurable Y ∧
      (∀ᵐx∂ν,(fun ω=>Y (x,ω))=ᵐ[μ] J.integral (Input x)) ∧
      (∫⁻x,∫⁻ω,ENNReal.ofReal (|Y (x,ω)|^2) ∂μ ∂ν)=
        (∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw (x,(t,ω))‖^2) ∂μ ∂timeMeasure H ∂ν) ∧
      (∫⁻x,∫⁻ω,ENNReal.ofReal (|Y (x,ω)|^2) ∂μ ∂ν)≤
        ENNReal.ofReal (ParametricStoppedHaarEnergy.constant M H)*ν Set.univ ∧
      (∫⁻x,∫⁻ω,ENNReal.ofReal (|Y (x,ω)|^2) ∂μ ∂ν)<∞:=by
  have hbound:(∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw (x,(t,ω))‖^2) ∂μ ∂timeMeasure H ∂ν)≤
      ENNReal.ofReal (ParametricStoppedHaarEnergy.constant M H)*ν Set.univ:=by
    calc
      _≤∫⁻_:X,ENNReal.ofReal (ParametricStoppedHaarEnergy.constant M H) ∂ν:=
        lintegral_mono (ParametricStoppedHaarEnergy.energy_bound 𝓕 μ H hell hM v b q center f hqb hbH hH)
      _=_:=by simp
  have hfinite:(∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw (x,(t,ω))‖^2) ∂μ ∂timeMeasure H ∂ν)<∞:=
    lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν Set.univ))
  obtain ⟨Y,hY,hYa,hYe⟩:=StandardItoParameterFubini.energy J hF ν Input Raw
    (ParametricStoppedHaarRows.raw_predictable 𝓕 hell v b q center f hf hv hb hq hc)
    (ParametricStoppedHaarRows.process_ae 𝓕 μ H hell hM v b q center f hf hqb hbH) hfinite
  exact ⟨Y,hY,hYa,hYe,hYe.trans_le hbound,hYe.trans_lt hfinite⟩
end SHE.ParametricStoppedHaarVersion
