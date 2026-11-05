module

public import SHEStochastic.BoundedFourierInput
public import SHEStochastic.GlobalBoundedHeatCoefficientLift
public import SHEStochastic.GlobalNativeFourierRemainder
public import SHEStochastic.BoundedFourierLift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.GlobalBoundedFourierLift
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open UnboundedNativeHeatEquation NativeFourierHeatCoordinate BoundedHeatCoefficientLift
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) (hH : 0<H)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

/-- The bounded native convolution's Fourier coefficients use exactly
the Fourier inputs identified at the weak limit. This is the existing
parameter Fubini theorem applied to the bounded coefficient lift. -/
theorem coordinate
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) (T : ℝ≥0) (hTH : T ≤ H)
    (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ sample, Continuous (fun p ↦ Y p sample))
    (he : ∀ p, Y p =ᵐ[μ] J.integral (GlobalBoundedHeatCoefficientLift.input F (physical W)
      (physical_predictable F W hW) hG hβ hβ1.le B hb μ H (GlobalHeatParameter.time H p)
        (GlobalHeatParameter.time_le_horizon H p) (center p))) :
    (fun sample ↦ NativeFourierHeatCoordinate.coordinate a n
      (NativeRemainderObservation.remainder ⟨fun p ↦ Y p sample, hc sample⟩ (GlobalHeatRowPhysicalIntegration.unitTime H hH T hTH))) =ᵐ[μ]
      fun sample ↦ Real.exp (-(T : ℝ)*(n : ℝ)^2)*J.integral
        (StoppedItoInputs.stop F μ H T (BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n)) sample := by
  have hh := GlobalNativeFourierRemainder.coordinate F (field (physical W) hG hβ hβ1.le)
    (predictable F (physical W) (physical_predictable F W hW) hG hβ hβ1.le)
    (projection_holder B) (by norm_num) (by norm_num) μ H hH
    (Filter.Eventually.of_forall (norm_bound (physical W) hG hβ hβ1.le B hb))
    J a n T hTH Y hm hc he
  rw [BoundedFourierLift.growing_eq F μ H W hW hG hβ hβ1 B hb a n] at hh
  exact hh

end SHEStochastic.GlobalBoundedFourierLift
