module

public import SHEStochastic.NativePhysicalState
public import SHEStochastic.SmoothedHeatInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.NativeRemainderObservation
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback UnboundedHeatJointMoments
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The constructed continuous physical convolution as a literal state
in the original native real L2 space. -/
def remainder (Y : C(Parameter, ℝ)) (t : ShortTime) : RealL2 :=
  NativePhysicalState.pull (PhysicalHeatParameterSection.value 2 Y t)

theorem continuous_remainder (Y : C(Parameter, ℝ)) : Continuous (remainder Y) :=
  NativePhysicalState.pull.continuous.comp (PhysicalHeatParameterSection.uniformContinuous_value 2 Y).continuous

theorem push_mild {r : ℝ} (hr : 0 ≤ r) (u : RealL2) (Y : C(Parameter, ℝ)) (t : ShortTime) :
    NativePhysicalState.push (NativeHeatObservation.heat r u + remainder Y t) =
      PhysicalHeatState.state r (NativeHeatObservation.embed u) + PhysicalHeatParameterSection.value 2 Y t := by
  change NativePhysicalState.push (NativeHeatObservation.heat r u +
    NativePhysicalState.pull (PhysicalHeatParameterSection.value 2 Y t)) = _
  rw [map_add, NativePhysicalState.push_heat hr, NativePhysicalState.push_pull]

theorem observation {r : ℝ} (hr : 0 < r) (x : HeatCircle) (Y : C(Parameter, ℝ)) (t : ShortTime) :
    NativeHeatObservation.functional r x (remainder Y t) =
      ∫ a : HeatCircle, Y (point t a) ∂PhysicalHeatKernelMeasure.measure r hr x := by
  rw [NativePhysicalState.functional_integral hr, PhysicalHeatKernelMeasure.integral]
  change (∫ a : HeatCircle, RealCausalHeatKernel.value x r a *
    NativePhysicalState.push (NativePhysicalState.pull (PhysicalHeatParameterSection.value 2 Y t)) a ∂haarAddCircle) = _
  rw [NativePhysicalState.push_pull]
  apply integral_congr_ae
  filter_upwards [PhysicalHeatParameterSection.value_ae 2 Y t] with a ha
  change RealCausalHeatKernel.value x r a * PhysicalHeatParameterSection.value 2 Y t a =
    RealCausalHeatKernel.value x r a * Y (point t a)
  rw [ha]

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) {R : ℝ}
  (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)

/-- The actual continuous native remainder has the same positive heat
observations as the original stopped future-target stochastic row. This
uses the previously constructed native integral and ordinary Fubini. -/
theorem stochastic_observation
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (T δ : ℝ≥0) (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (hδ : 0 < δ)
    (hTD : T + δ ≤ H) (hTD1 : ((T + δ : ℝ≥0) : ℝ) ≤ 1) (x : HeatCircle)
    (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ ω, Continuous (fun p ↦ Y p ω))
    (he : ∀ p, Y p =ᵐ[μ] J.integral (parameterInput F U hU hG hβ hβ1 μ H hbound p)) :
    (fun ω ↦ NativeHeatObservation.functional δ x
      (remainder ⟨fun p ↦ Y p ω, hc ω⟩ ⟨T, T.property, hT⟩)) =ᵐ[μ]
      J.integral (StoppedItoInputs.stop F μ H T
        (UnboundedHeatFamily.input F U hU hG hβ hβ1 μ H (T + δ) hTD hTD1 x hbound)) := by
  let t : ShortTime := ⟨T, T.property, hT⟩
  have hh := HeatRowPhysicalIntegration.integral_ae F U hU hG hβ hβ1 μ H hbound J t hTH
    (PhysicalHeatKernelMeasure.measure δ hδ x) Y hm hc he
  change J.integral (∫ a : HeatCircle, UnboundedHeatFamily.input F U hU hG hβ hβ1 μ H
    T hTH hT a hbound ∂PhysicalHeatKernelMeasure.measure δ hδ x) =ᵐ[μ]
      (fun ω ↦ ∫ a : HeatCircle, Y (point t a) ω ∂PhysicalHeatKernelMeasure.measure δ hδ x) at hh
  rw [SmoothedHeatInput.average_eq_stopped F U hU hG hβ hβ1 μ H hbound T δ hδ hTH hT hTD hTD1 x] at hh
  filter_upwards [hh] with ω hω
  exact (observation hδ x ⟨fun p ↦ Y p ω, hc ω⟩ t).trans hω.symm

end SHEStochastic.NativeRemainderObservation
