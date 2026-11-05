module

public import SHEStochastic.FourierHeatRowAverage
public import SHEStochastic.HeatRowInputIntegration
public import SHEStochastic.PredictableMultiplier
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.FourierHeatInput
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open NativeFourierHeatCoordinate
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
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) {R : ℝ}
  (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

def multiplier (H : ℝ≥0) (n : ℤ) (p : ℝ≥0 × Ω) : ℝ :=
  Real.exp (min (p.1 : ℝ) (H : ℝ) * (n : ℝ) ^ 2)

theorem multiplier_measurable (n : ℤ) :
    StronglyMeasurable[F.predictable] (multiplier (Ω := Ω) H n) :=
  (((PredictableClock.real_time_measurable F).min measurable_const).mul_const _).exp.stronglyMeasurable

theorem multiplier_bound (n : ℤ) (p : ℝ≥0 × Ω) :
    |multiplier H n p| ≤ Real.exp ((H : ℝ) * (n : ℝ) ^ 2) := by
  unfold multiplier
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))

/-- A single predictable Fourier input represents the integrating-factor
martingale at every observation time. The time weight is capped only
outside the original integration horizon. -/
def growingInput (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H :=
  PredictableMultiplier.process (FourierHeatRowAverage.input F U hU hG hβ hβ1 μ H a n hbound)
    (multiplier H n) (multiplier_measurable F H n)
    (Real.exp ((H : ℝ) * (n : ℝ) ^ 2)) (multiplier_bound H n)

theorem growing_ae_trim (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    growingInput F U hU hG hβ hβ1 μ H hbound a n =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
      fun p ↦ multiplier H n p • FourierHeatRowAverage.row F U hU hG hβ hβ1 a n p := by
  have hg := PredictableMultiplier.process_ae_trim
    (FourierHeatRowAverage.input F U hU hG hβ hβ1 μ H a n hbound)
    (multiplier H n) (multiplier_measurable F H n)
    (Real.exp ((H : ℝ) * (n : ℝ) ^ 2)) (multiplier_bound H n)
  change growingInput F U hU hG hβ hβ1 μ H hbound a n =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
    (fun p ↦ multiplier H n p • FourierHeatRowAverage.input F U hU hG hβ hβ1 μ H a n hbound p) at hg
  filter_upwards [hg, FourierHeatRowAverage.input_ae_trim F U hU hG hβ hβ1 μ H a n hbound] with p hg hr
  exact hg.trans (congrArg (fun v ↦ multiplier H n p • v) hr)

/-- The Fourier average of the actual heat-convolution input is the
stopped integrating-factor input times the heat eigenvalue. -/
theorem average_eq_stopped (a : ℂ →L[ℝ] ℝ) (n : ℤ) (T : ℝ≥0)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) :
    (∫ x : HeatCircle, weight a n x • UnboundedHeatFamily.input F U hU hG hβ hβ1 μ H T hTH hT x hbound ∂haarAddCircle) =
      Real.exp (-(T : ℝ) * (n : ℝ) ^ 2) •
        StoppedItoInputs.stop F μ H T (growingInput F U hU hG hβ hβ1 μ H hbound a n) := by
  let t : HeatParameterPullback.ShortTime := ⟨T, T.property, hT⟩
  have hav := HeatRowInputIntegration.weighted_integral_ae_trim F U hU hG hβ hβ1 μ H hbound t hTH haarAddCircle (weight a n)
  change (∫ x : HeatCircle, weight a n x • UnboundedHeatFamily.input F U hU hG hβ hβ1 μ H T hTH hT x hbound ∂haarAddCircle) =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
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

end SHEStochastic.FourierHeatInput
