module
public import SHE.PredictableEnergyCap
public import SHE.ProcessEnergy
public import SHE.StoppedComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.PredictableEnergyCapInput
open Set MeasureTheory PredictableL2 PredictableEnergyCap
open scoped NNReal ENNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E][InnerProductSpace ℝ E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (U:ℝ≥0→Ω→E)(ha:StronglyAdapted 𝓕 U)(hc:∀ω,Continuous (fun t=>U t ω))

theorem cap_le (p:ℝ≥0×Ω):‖capped U p.1 p.2‖^2≤‖U p.1 p.2‖^2:=by
  unfold capped
  split_ifs <;> simp only [norm_zero,zero_pow (by decide:2≠0),le_refl,sq_nonneg]

include ha hc in
/-- The original predictable capped field has a genuine L2 input,
one pathwise bracket event, and expected cost bounded by the ORIGINAL
uncapped control energy. These are actual applicability hypotheses of
ordinary bounded-energy Novikov/Girsanov, not new external inputs. -/
theorem exists_input (hi:Integrable (fun p:ℝ≥0×Ω=>‖U p.1 p.2‖^2) (energyMeasure μ H)):
    ∃u:Process (E:=E) 𝓕 μ H,
      u=ᵐ[energyMeasure μ H] Function.uncurry (capped U) ∧
      (∀ᵐω∂μ,(∫t,‖u (t,ω)‖^2 ∂timeMeasure H)≤1) ∧
      ‖u‖^2≤∫p,‖U p.1 p.2‖^2 ∂energyMeasure μ H:=by
  have hp:=PredictableEnergyCap.predictable 𝓕 U ha hc
  have hm:(Measurable (fun p:ℝ≥0×Ω=>‖capped U p.1 p.2‖^2)):=
    ((hp.mono (predictable_le_product 𝓕)).norm.pow 2).measurable
  have hci:Integrable (fun p:ℝ≥0×Ω=>‖capped U p.1 p.2‖^2) (energyMeasure μ H):=by
    apply hi.mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun p=>by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)];exact cap_le U p)
  have hmem:MemLp (Function.uncurry (capped U)) 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm (hp.mono (predictable_le_product 𝓕)).aestronglyMeasurable).mpr hci
  have htrim:@MemLp _ _ 𝓕.predictable _ _ (Function.uncurry (capped U)) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)):=by
    change eLpNorm (Function.uncurry (capped U)) 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))<⊤
    rw [eLpNorm_trim (predictable_le_product 𝓕) hp]
    exact hmem
  let u:Process (E:=E) 𝓕 μ H:=htrim.toLp (Function.uncurry (capped U))
  have hua:u=ᵐ[energyMeasure μ H] Function.uncurry (capped U):=ae_eq_of_ae_eq_trim htrim.coeFn_toLp
  refine ⟨u,hua,?_,?_⟩
  · filter_upwards [Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae hua)] with ω hω
    have he:(∫t,‖u (t,ω)‖^2 ∂timeMeasure H)=∫t,‖capped U t ω‖^2 ∂timeMeasure H:=by
      apply integral_congr_ae
      filter_upwards [hω] with t ht
      change u (t,ω)=capped U t ω at ht
      exact congrArg (fun v:E=>‖v‖^2) ht
    rw [he]
    exact path_energy U hc H ω
  · rw [subsigma_norm_sq (energyMeasure μ H) (predictable_le_product 𝓕) u,
      integral_congr_ae (hua.mono (fun p hp=>by rw [hp]))]
    exact integral_mono hci hi (cap_le U)

/-- The actual final accumulated energy is the literal time integral. -/
theorem accumulated_eq (ω:Ω):accumulated U H ω=∫t,‖U t ω‖^2 ∂timeMeasure H:=by
  rw [timeMeasure_integral]
  unfold accumulated CumulativeEnergyCap.cumulative realEnergy
  exact intervalIntegral.integral_of_le H.2

include ha hc in
/-- The exit event is measurable in the original terminal past and its
probability is bounded by the original expected control energy. -/
theorem exit_bound (hi:Integrable (fun p:ℝ≥0×Ω=>‖U p.1 p.2‖^2) (energyMeasure μ H)):
    MeasurableSet {ω|1≤accumulated U H ω} ∧
      μ.real {ω|1≤accumulated U H ω}≤∫p,‖U p.1 p.2‖^2 ∂energyMeasure μ H:=by
  have haA:=accumulated_adapted 𝓕 U ha hc H
  have hm:Measurable (accumulated U H):=haA.measurable.mono (𝓕.le H) le_rfl
  have hs:MeasurableSet {ω|1≤accumulated U H ω}:=measurableSet_le measurable_const hm
  have hA:Integrable (accumulated U H) μ:=by
    have hh:=hi.integral_prod_right
    convert! hh using 1
    funext ω
    exact accumulated_eq H U ω
  have hb:=exit_probability_le_energy μ hs hA
    (fun ω=>by rw [accumulated_eq H U ω];exact integral_nonneg (fun _=>sq_nonneg _))
    (fun ω hω=>hω)
  refine ⟨hs,hb.trans_eq ?_⟩
  simp_rw [accumulated_eq H U]
  exact (integral_prod_symm _ hi).symm
end SHE.PredictableEnergyCapInput
