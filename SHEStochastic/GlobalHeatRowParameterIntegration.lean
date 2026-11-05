module

public import SHEStochastic.UnboundedGlobalJointMoments
public import SHEStochastic.HeatRowParameterIntegration
public import SHEStochastic.SquaredIncrementContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.GlobalHeatRowParameterIntegration
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open HeatParameterCover UnboundedGlobalJointMoments UnboundedHeatIncrementCaps
open scoped NNReal ENNReal Topology

local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2*Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem input_squared_bound {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R) (p q : Parameter) :
    ‖parameterInput F U hU hG hβ hβ1 μ H hbound p-parameterInput F U hU hG hβ hβ1 μ H hbound q‖^2≤
      (jointConstant G C β R H).toReal*dist p q^exponent β := by
  let v := parameterInput F U hU hG hβ hβ1 μ H hbound p-parameterInput F U hU hG hβ hβ1 μ H hbound q
  have he : ENNReal.ofReal (‖v‖^2)=∫⁻ ω, ∫⁻ s, ENNReal.ofReal (‖v (s,ω)‖^2) ∂timeMeasure H ∂μ := by
    rw [process_lintegral_energy]
    exact lintegral_lintegral_swap
      (((Lp.stronglyMeasurable v).mono (predictable_le_product F)).norm.pow 2).measurable.ennreal_ofReal.aemeasurable
  have hb : ENNReal.ofReal (‖v‖^2)≤jointConstant G C β R H*ENNReal.ofReal (dist p q^exponent β) := by
    rw [he]
    exact (lintegral_mono_ae (input_bracket F U hU hG hβ hβ1 μ H p q hbound)).trans_eq (by simp)
  have hf : jointConstant G C β R H*ENNReal.ofReal (dist p q^exponent β)≠⊤ :=
    ENNReal.mul_ne_top (jointConstant_finite G C β R H).ne ENNReal.ofReal_ne_top
  have hh := ENNReal.toReal_mono hf hb
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (dist_nonneg : 0≤dist p q) _)] using hh

theorem continuous_input {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R) :
    Continuous (parameterInput F U hU hG hβ hβ1 μ H hbound) :=
  SquaredIncrementContinuity.continuous _ _ _ (exponent_pos hβ1)
    (input_squared_bound F U hU hG hβ hβ1 μ H hbound)

theorem integrable_input {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R)
    (ν : Measure Parameter) [IsFiniteMeasure ν] : Integrable (parameterInput F U hU hG hβ hβ1 μ H hbound) ν := by
  let K : C(Parameter, Process (E := Lp V 2 (haarAddCircle (T := 2*Real.pi))) F μ H) :=
    ⟨_,continuous_input F U hU hG hβ hβ1 μ H hbound⟩
  exact Integrable.of_bound K.continuous.aestronglyMeasurable_of_compactSpace ‖K‖ (Eventually.of_forall K.norm_coe_le_norm)

end SHEStochastic.GlobalHeatRowParameterIntegration
