module

public import SHEStochastic.FourierHeatInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.NativeFourierRemainder
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open HeatParameterCover HeatParameterPullback NativeFourierHeatCoordinate UnboundedHeatJointMoments
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

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

/-- The literal Fourier coefficient of the continuous native remainder
is a heat factor times one stopped native martingale input. No separate
Fourier stochastic integral or stochastic Fubini assumption is used. -/
theorem coordinate
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) (T : ℝ≥0) (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1)
    (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ ω, Continuous (fun p ↦ Y p ω))
    (he : ∀ p, Y p =ᵐ[μ] J.integral (parameterInput F U hU hG hβ hβ1 μ H hbound p)) :
    (fun ω ↦ NativeFourierHeatCoordinate.coordinate a n
      (NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hc ω⟩ ⟨T, T.property, hT⟩)) =ᵐ[μ]
      fun ω ↦ Real.exp (-(T : ℝ) * (n : ℝ) ^ 2) *
        J.integral (StoppedItoInputs.stop F μ H T
          (FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound a n)) ω := by
  let t : ShortTime := ⟨T, T.property, hT⟩
  have hh := HeatRowPhysicalIntegration.weighted_integral_ae F U hU hG hβ hβ1 μ H hbound J t hTH
    haarAddCircle (weight a n) Y hm hc he
  change J.integral (∫ x : HeatCircle, weight a n x • UnboundedHeatFamily.input F U hU hG hβ hβ1 μ H T hTH hT x hbound ∂haarAddCircle) =ᵐ[μ]
    (fun ω ↦ ∫ x : HeatCircle, weight a n x * Y (point t x) ω ∂haarAddCircle) at hh
  rw [FourierHeatInput.average_eq_stopped F U hU hG hβ hβ1 μ H hbound a n T hTH hT, map_smul] at hh
  filter_upwards [hh, Lp.coeFn_smul (Real.exp (-(T : ℝ) * (n : ℝ) ^ 2))
    (J.integral (StoppedItoInputs.stop F μ H T
      (FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound a n)))] with ω hω hs
  exact (coordinate_remainder a n ⟨fun p ↦ Y p ω, hc ω⟩ t).trans (hω.symm.trans hs)

end SHEStochastic.NativeFourierRemainder
