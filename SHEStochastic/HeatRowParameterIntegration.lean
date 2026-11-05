module

public import SHEStochastic.UnboundedHeatJointMoments
public import SHE.TerminalItoFubini
public import SHEStochastic.LpVersionIntegration
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.HeatRowParameterIntegration
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter Set
open HeatParameterCover HeatParameterCoordinates UnboundedHeatJointMoments UnboundedHeatIncrementCaps
open scoped NNReal ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

private theorem energy_swap
    (v : Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H) :
    ENNReal.ofReal (‖v‖ ^ 2) = ∫⁻ ω, ∫⁻ s,
      ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure H ∂μ := by
  rw [process_lintegral_energy]
  exact lintegral_lintegral_swap
    (((Lp.stronglyMeasurable v).mono (predictable_le_product F)).norm.pow 2).measurable.ennreal_ofReal.aemeasurable

/-- The already proved bracket estimate also controls distances in the
actual predictable-input Hilbert space, before applying any integral. -/
theorem input_squared_bound {R : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R) (p q : Parameter) :
    ‖parameterInput F U hU hG hβ hβ1 μ H hbound p -
      parameterInput F U hU hG hβ hβ1 μ H hbound q‖ ^ 2 ≤
        (jointConstant G C β R).toReal * dist p q ^ exponent β := by
  have hb : ENNReal.ofReal (‖parameterInput F U hU hG hβ hβ1 μ H hbound p -
      parameterInput F U hU hG hβ hβ1 μ H hbound q‖ ^ 2) ≤
      jointConstant G C β R * ENNReal.ofReal (dist p q ^ exponent β) := by
    rw [energy_swap F μ H]
    exact (lintegral_mono_ae
      (input_bracket_bound F U hU hG hβ hβ1 μ H p q hbound)).trans_eq (by simp)
  have hf : jointConstant G C β R * ENNReal.ofReal (dist p q ^ exponent β) ≠ ⊤ :=
    ENNReal.mul_ne_top (jointConstant_finite G C β R).ne ENNReal.ofReal_ne_top
  have hh := ENNReal.toReal_mono hf hb
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist p q) _)] using hh

/-- The true heat-row family is continuous as a map into predictable
L2, hence admits ordinary Bochner integration over its parameters. -/
theorem continuous_input {R : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R) :
    Continuous (parameterInput F U hU hG hβ hβ1 μ H hbound) := by
  rw [continuous_iff_continuousAt]
  intro q
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hq := exponent_pos hβ1
  have hd : Continuous (fun p : Parameter ↦ dist p q ^ exponent β) :=
    (continuous_id.dist continuous_const).rpow_const (fun _ ↦ Or.inr hq.le)
  have hcap : Tendsto (fun p : Parameter ↦ (jointConstant G C β R).toReal * dist p q ^ exponent β)
      (𝓝 q) (𝓝 0) := by
    have hc : Continuous (fun p : Parameter ↦ (jointConstant G C β R).toReal * dist p q ^ exponent β) :=
      continuous_const.mul hd
    have hh := hc.tendsto q
    change Tendsto (fun p : Parameter ↦ (jointConstant G C β R).toReal * dist p q ^ exponent β)
      (𝓝 q) (𝓝 ((jointConstant G C β R).toReal * dist q q ^ exponent β)) at hh
    simpa only [dist_self, Real.zero_rpow hq.ne', mul_zero] using hh
  have hs := squeeze_zero (fun p : Parameter ↦ sq_nonneg
    (‖parameterInput F U hU hG hβ hβ1 μ H hbound p -
      parameterInput F U hU hG hβ hβ1 μ H hbound q‖))
    (input_squared_bound F U hU hG hβ hβ1 μ H hbound · q) hcap
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  change Tendsto (fun p : Parameter ↦ Real.sqrt (‖parameterInput F U hU hG hβ hβ1 μ H hbound p -
      parameterInput F U hU hG hβ hβ1 μ H hbound q‖ ^ 2)) (𝓝 q) (𝓝 (Real.sqrt 0)) at hh
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

theorem integrable_input {R : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)
    (ν : Measure Parameter) [IsFiniteMeasure ν] :
    Integrable (parameterInput F U hU hG hβ hβ1 μ H hbound) ν := by
  let K : C(Parameter, Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H) :=
    ⟨_, continuous_input F U hU hG hβ hβ1 μ H hbound⟩
  exact Integrable.of_bound K.continuous.aestronglyMeasurable_of_compactSpace ‖K‖
    (Eventually.of_forall fun p ↦ K.norm_coe_le_norm p)

/-- The given continuous native convolution version commutes with
parameter integration. All version integrability is proved from the
actual predictable-input family and terminal isometry. -/
theorem integral_ae {R : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (ν : Measure Parameter) [IsFiniteMeasure ν]
    (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ ω, Continuous (fun p ↦ Y p ω))
    (he : ∀ p, Y p =ᵐ[μ] J.integral (parameterInput F U hU hG hβ hβ1 μ H hbound p)) :
    J.integral (∫ p, parameterInput F U hU hG hβ hβ1 μ H hbound p ∂ν) =ᵐ[μ]
      fun ω ↦ ∫ p, Y p ω ∂ν := by
  let K := parameterInput F U hU hG hβ hβ1 μ H hbound
  have hK : Integrable K ν := integrable_input F U hU hG hβ hβ1 μ H hbound ν
  let Q (ω : Ω) : C(Parameter, ℝ) := ⟨fun p ↦ Y p ω, hc ω⟩
  have hQ : Measurable Q := ContinuousMap.measurable_iff_eval.mpr hm
  have hraw : Measurable (fun z : Parameter × Ω ↦ Y z.1 z.2) :=
    continuous_eval.measurable.comp ((hQ.comp measurable_snd).prodMk measurable_fst)
  have hRep : ∀ᵐ p ∂ν, J.integral (K p) =ᵐ[μ] fun ω ↦ Y p ω :=
    Eventually.of_forall fun p ↦ (he p).symm
  have hY := LpVersionIntegration.integrable μ ν (fun p ↦ J.integral (K p))
    (J.integral.toContinuousLinearMap.integrable_comp hK)
    (fun z : Parameter × Ω ↦ Y z.1 z.2) hraw.aestronglyMeasurable hRep
  exact TerminalItoFubini.integral_ae F μ H J ν K hK
    (fun z : Parameter × Ω ↦ Y z.1 z.2) hY hRep

end SHEStochastic.HeatRowParameterIntegration
