module

public import SHEStochastic.FourierHeatInput
public import SHEStochastic.StateNoiseCovariance
public import SHEStochastic.StateDriverCovariance
public import SHEStochastic.NativeBrownianCoordinates
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.FourierNoiseCovariance
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open NativeFourierHeatCoordinate
open scoped ENNReal NNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

theorem row_eq (a : ℂ →L[ℝ] ℝ) (n : ℤ) (p : ℝ≥0 × Ω) :
    FourierHeatRowAverage.row F U hU hG hβ hβ1 a n p =
      StateNoiseCovariance.row haarAddCircle hβ hβ1.le hG (weight a n) (U p) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  convert HolderStateRows.row_operator U hU hG hβ hβ1.le (fun _ ↦ weight a n) p using 1 <;> rfl

theorem row_covariance (a b : ℂ →L[ℝ] ℝ) (n m : ℤ) (p : ℝ≥0 × Ω) :
    inner ℝ (FourierHeatRowAverage.row F U hU hG hβ hβ1 a n p)
      (FourierHeatRowAverage.row F U hU hG hβ hβ1 b m p) =
      StateNoiseCovariance.value haarAddCircle hβ hβ1.le hG hG (weight a n) (weight b m) (U p) := by
  rw [row_eq, row_eq]
  rfl

/-- The actual native integrating-factor rows have precisely the
canonical physical Fourier covariance, times the two heat weights. -/
theorem growing_covariance (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) {R : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)
    (a b : ℂ →L[ℝ] ℝ) (n m : ℤ) :
    ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F),
      inner ℝ (FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound a n p)
        (FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound b m p) =
        Real.exp (min (p.1 : ℝ) (H : ℝ) * ((n : ℝ) ^ 2 + (m : ℝ) ^ 2)) *
          StateNoiseCovariance.value haarAddCircle hβ hβ1.le hG hG (weight a n) (weight b m) (U p) := by
  filter_upwards [FourierHeatInput.growing_ae_trim F U hU hG hβ hβ1 μ H hbound a n,
    FourierHeatInput.growing_ae_trim F U hU hG hβ hβ1 μ H hbound b m] with p hn hm
  rw [hn, hm, real_inner_smul_left, real_inner_smul_right, row_covariance]
  dsimp only [FourierHeatInput.multiplier]
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  ring

/-- The mixed state/driver bracket is the canonical cross covariance
with exactly one heat weight. This retains the actual Brownian driver
when passing the native Fourier equations to a joint weak limit. -/
theorem growing_driver_covariance (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) {R : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) {ι : Type*} [Countable ι] [DecidableEq ι]
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (i : ι) :
    ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F),
      inner ℝ (FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound a n p)
        (RawCylindricalCoordinates.row F μ H (e : ι → Lp V 2 haarAddCircle) i p) =
        Real.exp (min (p.1 : ℝ) (H : ℝ) * (n : ℝ) ^ 2) *
          StateDriverCovariance.value haarAddCircle hβ hβ1.le hG (weight a n) (e i) (U p) := by
  have hc : RawCylindricalCoordinates.row F μ H (e : ι → Lp V 2 haarAddCircle) i =ᵐ[
      (energyMeasure μ H).trim (predictable_le_product F)] fun _ ↦ e i :=
    (RotatedCylindricalCoordinates.constant_memLp F μ H (e i)).coeFn_toLp
  filter_upwards [FourierHeatInput.growing_ae_trim F U hU hG hβ hβ1 μ H hbound a n, hc]
    with p hn hi
  rw [hn, hi, real_inner_smul_left, row_eq]
  rfl

end SHEStochastic.FourierNoiseCovariance
