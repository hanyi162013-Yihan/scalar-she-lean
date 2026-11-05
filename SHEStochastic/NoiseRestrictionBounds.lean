module

public import SHEStochastic.NoiseRestriction
public import SHEStochastic.WeightedBracketBound
public import SHE.PredictableItoRotation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NoiseRestrictionBounds
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω A C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

def input (r : A →ₗᵢ[ℝ] C) : Process (E := A) F μ H →ₗᵢ[ℝ] Process (E := C) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact L2HilbertSum.lift ((energyMeasure μ H).trim (predictable_le_product F)) r

theorem input_ae_trim (r : A →ₗᵢ[ℝ] C) (u : Process (E := A) F μ H) :
    input r u =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)] (fun p ↦ r (u p)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact L2HilbertSum.lift_ae _ r u

theorem bounded (r : A →ₗᵢ[ℝ] C) (u : Process (E := A) F μ H) (M : ℝ)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M) :
    ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖input r u p‖ ≤ M := by
  filter_upwards [input_ae_trim r u, hu] with p hp hq
  rw [hp, r.norm_map]
  exact hq

theorem bracket_eq (r : A →ₗᵢ[ℝ] C) (u : Process (E := A) F μ H) :
    StochasticExponential.bracket F μ H (input r u) =ᵐ[μ]
      StochasticExponential.bracket F μ H u := by
  have hh := ae_eq_of_ae_eq_trim (input_ae_trim r u)
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hh
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  apply integral_congr_ae
  filter_upwards [hω] with t ht
  change input r u (t, ω) = r (u (t, ω)) at ht
  rw [ht, r.norm_map]

theorem integral_eq_rotation [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
    (J : StandardTerminalIto (C := C) (E := ℝ) F μ H) (r : A →ₗᵢ[ℝ] C)
    (hr : @Measurable ((ℝ≥0 × Ω) × A) C
      (F.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p ↦ r p.2))
    (u : Process (E := A) F μ H) :
    (restrictNoise J r).integral u =
      (PredictableItoRotation.integral F μ H (fun _ ↦ r) hr J).integral u := by
  apply congrArg J.integral
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  exact (ae_eq_of_ae_eq_trim (input_ae_trim r u)).trans
    (PredictableItoRotation.processIsometry_ae F μ H (fun _ ↦ r) hr u).symm

end SHEStochastic.NoiseRestrictionBounds
