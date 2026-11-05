module

public import SHEStochastic.FourierHeatInput
public import SHEStochastic.GlobalHeatRowInputIntegration
public import SHEStochastic.HeatRowInputIntegration
public import SHEStochastic.PredictableMultiplier
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.GlobalFourierHeatInput
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open NativeFourierHeatCoordinate FourierHeatInput
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) (hH : 0<H) {R : ℝ}
  (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

include hH in
/-- The Fourier average of the actual heat-convolution input is the
stopped integrating-factor input times the heat eigenvalue. -/
theorem average_eq_stopped (a : ℂ →L[ℝ] ℝ) (n : ℤ) (T : ℝ≥0)
    (hTH : T ≤ H) :
    (∫ x : HeatCircle, weight a n x • UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H T hTH x hbound ∂haarAddCircle) =
      Real.exp (-(T : ℝ) * (n : ℝ) ^ 2) •
        StoppedItoInputs.stop F μ H T (growingInput F U hU hG hβ hβ1 μ H hbound a n) := by
  have hav := GlobalHeatRowInputIntegration.weighted_integral_ae_trim F U hU hG hβ hβ1 μ H hH hbound T hTH haarAddCircle (weight a n)
  change (∫ x : HeatCircle, weight a n x • UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H T hTH x hbound ∂haarAddCircle) =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
    (fun p ↦ ∫ x : HeatCircle, weight a n x • UnboundedHeatFamily.family F U hU hG hβ hβ1 T x p ∂haarAddCircle) at hav
  have hrow := (FourierHeatRowAverage.memLp F U hU hG hβ hβ1 μ H a n hbound).coeFn_toLp
  have hg := PredictableMultiplier.process_ae_trim
    (FourierHeatRowAverage.input F U hU hG hβ hβ1 μ H a n hbound)
    (multiplier H n) (multiplier_measurable F H n)
    (Real.exp ((H : ℝ) * (n : ℝ) ^ 2)) (multiplier_bound H n)
  change growingInput F U hU hG hβ hβ1 μ H hbound a n =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
    (fun p ↦ multiplier H n p • FourierHeatRowAverage.input F U hU hG hβ hβ1 μ H a n hbound p) at hg
  change FourierHeatRowAverage.input F U hU hG hβ hβ1 μ H a n hbound =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
    FourierHeatRowAverage.row F U hU hG hβ hβ1 a n at hrow
  apply Lp.ext
  filter_upwards [hav, hrow, hg,
    StoppedInputParameter.stop_ae_trim F μ H (growingInput F U hU hG hβ hβ1 μ H hbound a n) T,
    Lp.coeFn_smul (Real.exp (-(T : ℝ) * (n : ℝ) ^ 2))
      (StoppedItoInputs.stop F μ H T (growingInput F U hU hG hβ hβ1 μ H hbound a n))] with p hav hr hg hs he
  rw [hav, FourierHeatRowAverage.family_average, he]
  change _ = Real.exp (-(T : ℝ) * (n : ℝ) ^ 2) •
    (StoppedItoInputs.stop F μ H T (growingInput F U hU hG hβ hβ1 μ H hbound a n) p)
  rw [hs]
  by_cases hp : p.1 < T
  · rw [if_pos hp, Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (Ω := Ω) T from hp), hg, hr, smul_smul]
    congr 1
    dsimp [multiplier]
    rw [min_eq_left (show (p.1 : ℝ) ≤ H from hp.le.trans hTH), ← Real.exp_add]
    congr 1
    ring
  · rw [if_neg hp, Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (Ω := Ω) T from hp), smul_zero]

end SHEStochastic.GlobalFourierHeatInput
