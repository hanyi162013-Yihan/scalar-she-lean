module
public import SHE.ExponentialChangeMeasure
public import SHE.StochasticExponentialMoments
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.CappedControlMeasureComparison
open MeasureTheory PredictableL2 PredictableEnergyCap
open scoped NNReal ENNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E][InnerProductSpace ℝ E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (U:ℝ≥0→Ω→E)(ha:StronglyAdapted 𝓕 U)(hc:∀ω,Continuous (fun t=>U t ω))
variable (J:StandardTerminalIto (C:=E) (E:=ℝ) 𝓕 μ H)

include ha hc in
/-- Actual cap, mean-one density, equivalent changed probability and
all bounded-test comparison estimates from the ORIGINAL control cost.
No solution law or canonical continuation is an input or conclusion. -/
theorem exists_witness(hNovikov:StandardTerminalNovikov J)
    (hi:Integrable (fun p:ℝ≥0×Ω=>‖U p.1 p.2‖^2) (energyMeasure μ H)):
    ∃(u:Process (E:=E) 𝓕 μ H)(V:Ω→ℝ),
      u=ᵐ[energyMeasure μ H] Function.uncurry (capped U) ∧
      Measurable V ∧ V=ᵐ[μ] StochasticExponential.bracket 𝓕 μ H u ∧
      let Q:=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω) V
      let cost:=∫p,‖U p.1 p.2‖^2 ∂energyMeasure μ H
      IsProbabilityMeasure Q ∧ μ≪Q ∧ Q≪μ ∧
      μ.real {ω|1≤accumulated U H ω}≤cost ∧
      (∀(f:Ω→ℝ)(B:ℝ),AEStronglyMeasurable f μ→0≤B→(∀ω,|f ω|≤B)→
        |(∫ω,f ω ∂Q)-(∫ω,f ω ∂μ)|≤2*B*Real.sqrt cost) ∧
      (∀(f g:Ω→ℝ)(B:ℝ),AEStronglyMeasurable f μ→AEStronglyMeasurable g μ→
        0≤B→(∀ω,|f ω|≤B)→(∀ω,|g ω|≤B)→
        (∀ω,ω∉{ω|1≤accumulated U H ω}→f ω=g ω)→
        |(∫ω,f ω ∂μ)-(∫ω,g ω ∂Q)|≤2*B*(Real.sqrt cost+cost)):=by
  obtain ⟨u,V,hu,hmV,heV,hcap,hiV,hiZ,hmean,hcost⟩:=
    CappedStochasticExponential.exists_witness 𝓕 μ H U ha hc J hNovikov hi
  obtain ⟨hmR,hiR,hR0,hR,hB,hBcost⟩:=
    CappedStochasticExponential.original_cost 𝓕 μ H U ha hc hi
  obtain ⟨hiLog,hLog⟩:=CappedStochasticExponential.entropy_identity 𝓕 μ H J u V heV hiV
  let Z:Ω→ℝ:=fun ω=>Real.exp (-J.integral u ω-V ω/2)
  have hZpos:∀ω,0<Z ω:=fun _=>Real.exp_pos _
  have hcost0:0≤∫p,‖U p.1 p.2‖^2 ∂energyMeasure μ H:=
    integral_nonneg (fun _=>sq_nonneg _)
  have hEntropy:-(∫ω,Real.log (Z ω) ∂μ)≤
      (∫p,‖U p.1 p.2‖^2 ∂energyMeasure μ H)/2:=by
    rw [hLog]
    exact div_le_div_of_nonneg_right hcost (by norm_num)
  refine ⟨u,V,hu,hmV,heV,?_,?_,?_,hBcost,?_,?_⟩
  · exact ExponentialChangeMeasure.probability μ (fun ω=>J.integral u ω) V hiZ hmean
  · exact ExponentialChangeMeasure.original_absolutelyContinuous μ (fun ω=>J.integral u ω) V hiZ
  · exact ExponentialChangeMeasure.changed_absolutelyContinuous μ (fun ω=>J.integral u ω) V
  · intro f B hf hB0 hbf
    exact SHE.density_test_bound μ hZpos hiZ hmean hiLog hcost0 hEntropy hf hB0 hbf
  · intro f g B hf hg hB0 hbf hbg hagree
    exact SHE.stopped_measure_comparison μ hZpos hiZ hmean hiLog hcost0 hEntropy hB hBcost
      hf hg hB0 hbf hbg hagree
end SHE.CappedControlMeasureComparison
