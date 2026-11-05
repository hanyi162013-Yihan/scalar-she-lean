module

public import SHEStochastic.GlobalSmoothedHeatInput
public import SHEStochastic.NativeRemainderObservation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.GlobalRemainderObservation
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open HeatParameterCover HeatParameterPullback UnboundedGlobalJointMoments GlobalHeatRowPhysicalIntegration
open scoped NNReal ENNReal

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
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) (hH : 0<H) {R : ℝ}
  (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R)

/-- The continuous full-horizon remainder has exactly the original
positive-heat stochastic observations. This identifies the actual native
integral after physical spatial averaging. -/
theorem stochastic_observation
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2*Real.pi))) (E := ℝ) F μ H)
    (T δ : ℝ≥0) (hTH : T≤H) (hδ : 0<δ) (hTD : T+δ≤H) (x : HeatCircle)
    (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p)) (hc : ∀ ω, Continuous (fun p ↦ Y p ω))
    (he : ∀ p, Y p=ᵐ[μ] J.integral (parameterInput F U hU hG hβ hβ1 μ H hbound p)) :
    (fun ω ↦ NativeHeatObservation.functional δ x
      (NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω,hc ω⟩ (unitTime H hH T hTH)))=ᵐ[μ]
      J.integral (StoppedItoInputs.stop F μ H T
        (UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H (T+δ) hTD x hbound)) := by
  have hh := GlobalHeatRowPhysicalIntegration.integral_ae F U hU hG hβ hβ1 μ H hH hbound J T hTH
    (PhysicalHeatKernelMeasure.measure δ hδ x) Y hm hc he
  rw [GlobalSmoothedHeatInput.average_eq_stopped F U hU hG hβ hβ1 μ H hH hbound T δ hδ hTH hTD x] at hh
  filter_upwards [hh] with ω hω
  exact (NativeRemainderObservation.observation hδ x ⟨fun p ↦ Y p ω,hc ω⟩ (unitTime H hH T hTH)).trans hω.symm

end SHEStochastic.GlobalRemainderObservation
