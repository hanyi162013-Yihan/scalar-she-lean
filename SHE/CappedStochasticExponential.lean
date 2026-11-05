module
public import SHE.PredictableEnergyCapInput
public import SHE.StandardTerminalNovikov
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.CappedStochasticExponential
open Set MeasureTheory PredictableL2 PredictableEnergyCap
open scoped NNReal ENNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E][InnerProductSpace ℝ E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (U:ℝ≥0→Ω→E)(ha:StronglyAdapted 𝓕 U)(hc:∀ω,Continuous (fun t=>U t ω))
variable (J:StandardTerminalIto (C:=E) (E:=ℝ) 𝓕 μ H)

include ha hc in
/-- The actual uncapped cost and actual exit event, on the original
probability space, with their exact expectation and Markov bound. -/
theorem original_cost (hi:Integrable (fun p:ℝ≥0×Ω=>‖U p.1 p.2‖^2) (energyMeasure μ H)):
    Measurable (accumulated U H) ∧ Integrable (accumulated U H) μ ∧
      (∀ω,0≤accumulated U H ω) ∧
      (∫ω,accumulated U H ω ∂μ)=∫p,‖U p.1 p.2‖^2 ∂energyMeasure μ H ∧
      MeasurableSet {ω|1≤accumulated U H ω} ∧
      μ.real {ω|1≤accumulated U H ω}≤∫p,‖U p.1 p.2‖^2 ∂energyMeasure μ H:=by
  have hm:Measurable (accumulated U H):=
    (accumulated_adapted 𝓕 U ha hc H).measurable.mono (𝓕.le H) le_rfl
  have hR:Integrable (accumulated U H) μ:=by
    convert! hi.integral_prod_right using 1
    funext ω
    exact PredictableEnergyCapInput.accumulated_eq H U ω
  have he:(∫ω,accumulated U H ω ∂μ)=∫p,‖U p.1 p.2‖^2 ∂energyMeasure μ H:=by
    simp_rw [PredictableEnergyCapInput.accumulated_eq H U]
    exact (integral_prod_symm _ hi).symm
  obtain ⟨hB,hBcost⟩:=PredictableEnergyCapInput.exit_bound 𝓕 μ H U ha hc hi
  refine ⟨hm,hR,?_,he,hB,hBcost⟩
  intro ω
  rw [PredictableEnergyCapInput.accumulated_eq H U ω]
  exact integral_nonneg (fun _=>sq_nonneg _)

/-- The everywhere repaired bracket version retains the exact expected
reverse entropy of the original Ito input. -/
theorem entropy_identity (u:Process (E:=E) 𝓕 μ H)(V:Ω→ℝ)
    (heV:V=ᵐ[μ] StochasticExponential.bracket 𝓕 μ H u)(hiV:Integrable V μ):
    Integrable (fun ω=>Real.log (Real.exp (-J.integral u ω-V ω/2))) μ ∧
      -(∫ω,Real.log (Real.exp (-J.integral u ω-V ω/2)) ∂μ)=‖u‖^2/2:=by
  have hW:Integrable (fun ω=>J.integral u ω) μ:=(Lp.memLp (J.integral u)).integrable (by norm_num)
  have hh:=exponential_entropy_identity μ hW hiV (J.centered u)
  have he:(∫ω,V ω ∂μ)=‖u‖^2:=
    (integral_congr_ae heV).trans (StochasticExponential.expected_bracket 𝓕 μ H u)
  simpa only [he] using hh

include ha hc in
/-- A genuine clipped predictable input and an everywhere bounded version
of its bracket provide the actual mean-one density. Only ordinary Novikov
is external; the control cost, version and applicability are proved. -/
theorem exists_witness (hNovikov:StandardTerminalNovikov J)
    (hi:Integrable (fun p:ℝ≥0×Ω=>‖U p.1 p.2‖^2) (energyMeasure μ H)):
    ∃(u:Process (E:=E) 𝓕 μ H)(V:Ω→ℝ),
      u=ᵐ[energyMeasure μ H] Function.uncurry (capped U) ∧
      Measurable V ∧ V=ᵐ[μ] StochasticExponential.bracket 𝓕 μ H u ∧
      (∀ω,0≤V ω ∧ V ω≤1 ∧ V ω≤accumulated U H ω) ∧
      Integrable V μ ∧
      Integrable (fun ω=>Real.exp (-J.integral u ω-V ω/2)) μ ∧
      (∫ω,Real.exp (-J.integral u ω-V ω/2) ∂μ)=1 ∧
      ‖u‖^2≤∫p,‖U p.1 p.2‖^2 ∂energyMeasure μ H:=by
  obtain ⟨u,hua,hcap,hcost⟩:=PredictableEnergyCapInput.exists_input 𝓕 μ H U ha hc hi
  have hp:=PredictableEnergyCap.predictable 𝓕 U ha hc
  have hm:StronglyMeasurable (Function.uncurry (capped U)):=hp.mono (predictable_le_product 𝓕)
  have hbr:∀ᵐω∂μ,StochasticExponential.bracket 𝓕 μ H u ω≤accumulated U H ω:=by
    filter_upwards [hi.prod_left_ae,
      Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae hua)] with ω hraw hω
    have hcm:StronglyMeasurable (fun t=>capped U t ω):=
      hm.comp_measurable (measurable_id.prodMk measurable_const)
    have hci:Integrable (fun t=>‖capped U t ω‖^2) (timeMeasure H):=by
      apply hraw.mono' (hcm.norm.pow 2).aestronglyMeasurable
      exact ae_of_all _ (fun t=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact PredictableEnergyCapInput.cap_le U (t,ω))
    have he:StochasticExponential.bracket 𝓕 μ H u ω=∫t,‖capped U t ω‖^2 ∂timeMeasure H:=by
      apply integral_congr_ae
      filter_upwards [hω] with t ht
      change u (t,ω)=capped U t ω at ht
      exact congrArg (fun v:E=>‖v‖^2) ht
    rw [he,PredictableEnergyCapInput.accumulated_eq H U ω]
    exact integral_mono hci hraw (fun t=>PredictableEnergyCapInput.cap_le U (t,ω))
  have hmR:Measurable (accumulated U H):=
    (accumulated_adapted 𝓕 U ha hc H).measurable.mono (𝓕.le H) le_rfl
  have hR0:∀ω,0≤accumulated U H ω:=by
    intro ω
    rw [PredictableEnergyCapInput.accumulated_eq H U ω]
    exact integral_nonneg (fun _=>sq_nonneg _)
  let V:Ω→ℝ:=fun ω=>min 1 (min (StochasticExponential.bracket 𝓕 μ H u ω) (accumulated U H ω))
  have hmV:Measurable V:=measurable_const.min ((StochasticExponential.bracket_measurable 𝓕 μ H u).min hmR)
  have heV:V=ᵐ[μ] StochasticExponential.bracket 𝓕 μ H u:=by
    filter_upwards [hcap,hbr] with ω hω hωR
    change StochasticExponential.bracket 𝓕 μ H u ω≤1 at hω
    dsimp only [V]
    rw [min_eq_left hωR,min_eq_right hω]
  have hiV:Integrable V μ:=(StochasticExponential.bracket_integrable 𝓕 μ H u).congr heV.symm
  have hmean:=StochasticExponential.mean_one_of_cap 𝓕 μ H J hNovikov u hcap
  have heZ:(fun ω=>Real.exp (-J.integral u ω-V ω/2))=ᵐ[μ]
      StochasticExponential.density 𝓕 μ H J u:=by
    filter_upwards [heV] with ω hω
    simp only [StochasticExponential.density,hω]
  refine ⟨u,V,hua,hmV,heV,?_,hiV,hmean.1.congr heZ.symm,?_,hcost⟩
  · intro ω
    refine ⟨le_min (by norm_num) (le_min ?_ (hR0 ω)),min_le_left _ _,(min_le_right _ _).trans (min_le_right _ _)⟩
    exact integral_nonneg (fun _=>sq_nonneg _)
  · exact (integral_congr_ae heZ).trans hmean.2
end SHE.CappedStochasticExponential
