module

public import SHEStochastic.BoundedFourierInput
public import SHEStochastic.BoundedHeatCoefficientLift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.BoundedFourierLift
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open UnboundedNativeHeatEquation NativeFourierHeatCoordinate BoundedHeatCoefficientLift
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

include hb in
theorem row (a : ℂ →L[ℝ] ℝ) (n : ℤ) (p : ℝ≥0 × Ω) :
    FourierHeatRowAverage.row F (field (physical W) hG hβ hβ1.le)
      (predictable F (physical W) (physical_predictable F W hW) hG hβ hβ1.le)
      (projection_holder B) (by norm_num) (by norm_num) a n p =
    StateNoiseCovariance.row haarAddCircle hβ hβ1.le hG (weight a n) (physical W p) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.ext
  filter_upwards [HolderStateRows.row_ae (field (physical W) hG hβ hβ1.le)
    (predictable F (physical W) (physical_predictable F W hW) hG hβ hβ1.le)
    (projection_holder B) (by norm_num) (by norm_num) (fun _ ↦ weight a n) p,
    projection_agrees (physical W) hG hβ hβ1.le B hb p,
    StateNoiseCovariance.row_ae haarAddCircle hβ hβ1.le hG (weight a n) (physical W p)]
    with x hl hp hr
  change HolderStateRows.row _ _ _ _ _ _ p x = _
  rw [hl, hp, hr]

theorem growing_eq (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    FourierHeatInput.growingInput F (field (physical W) hG hβ hβ1.le)
      (predictable F (physical W) (physical_predictable F W hW) hG hβ hβ1.le)
      (projection_holder B) (by norm_num) (by norm_num) μ H
      (Filter.Eventually.of_forall (norm_bound (physical W) hG hβ hβ1.le B hb)) a n =
        BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n := by
  apply Lp.ext
  filter_upwards [FourierHeatInput.growing_ae_trim F (field (physical W) hG hβ hβ1.le)
    (predictable F (physical W) (physical_predictable F W hW) hG hβ hβ1.le)
    (projection_holder B) (by norm_num) (by norm_num) μ H
    (Filter.Eventually.of_forall (norm_bound (physical W) hG hβ hβ1.le B hb)) a n,
    BoundedFourierInput.input_ae_trim F μ H W hW hG hβ hβ1 B hb a n] with p hl hr
  rw [hl, hr]
  change _ = FourierHeatInput.multiplier H n p • _
  rw [row F W hW hG hβ hβ1 B hb a n p]

/-- The bounded native convolution's Fourier coefficients use exactly
the Fourier inputs identified at the weak limit. This is the existing
parameter Fubini theorem applied to the bounded coefficient lift. -/
theorem coordinate
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) (T : ℝ≥0) (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1)
    (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ sample, Continuous (fun p ↦ Y p sample))
    (he : ∀ p, Y p =ᵐ[μ] J.integral (BoundedHeatCoefficientLift.input F (physical W)
      (physical_predictable F W hW) hG hβ hβ1.le B hb μ H (time H p)
        (time_le_horizon H p) (time_le_one H p) (center p))) :
    (fun sample ↦ NativeFourierHeatCoordinate.coordinate a n
      (NativeRemainderObservation.remainder ⟨fun p ↦ Y p sample, hc sample⟩ ⟨T, T.property, hT⟩)) =ᵐ[μ]
      fun sample ↦ Real.exp (-(T : ℝ)*(n : ℝ)^2)*J.integral
        (StoppedItoInputs.stop F μ H T (BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n)) sample := by
  have hh := NativeFourierRemainder.coordinate F (field (physical W) hG hβ hβ1.le)
    (predictable F (physical W) (physical_predictable F W hW) hG hβ hβ1.le)
    (projection_holder B) (by norm_num) (by norm_num) μ H
    (Filter.Eventually.of_forall (norm_bound (physical W) hG hβ hβ1.le B hb))
    J a n T hTH hT Y hm hc he
  rw [growing_eq F μ H W hW hG hβ hβ1 B hb a n] at hh
  exact hh

end SHEStochastic.BoundedFourierLift
