module

public import SHE.StandardTerminalIto
public import SHEStochastic.L2HilbertSum

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal

variable {Ω A C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}

/-- Restrict one integral to any fixed isometric noise subspace. -/
def restrictNoise (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H)
    (e : A →ₗᵢ[ℝ] C) : StandardTerminalIto (C := A) (E := ℝ) 𝓕 μ H where
  integral := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
    exact J.integral.comp (L2HilbertSum.lift ((energyMeasure μ H).trim (predictable_le_product 𝓕)) e)
  adapted l v hv := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
    apply J.adapted l _
    filter_upwards [ae_eq_of_ae_eq_trim
      (L2HilbertSum.lift_ae ((energyMeasure μ H).trim (predictable_le_product 𝓕)) e v), hv]
      with p hp hs hl
    change L2HilbertSum.lift ((energyMeasure μ H).trim (predictable_le_product 𝓕)) e v p = 0
    rw [hp, hs hl, map_zero]
  centered v := J.centered _

/-- Restriction to the identity noise space changes no input or integral. -/
theorem restrictNoise_id (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H)
    (u : Process (E := C) 𝓕 μ H) :
    (restrictNoise J (LinearIsometry.id : C →ₗᵢ[ℝ] C)).integral u = J.integral u := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  apply congrArg J.integral
  apply Lp.ext
  exact L2HilbertSum.lift_ae ((energyMeasure μ H).trim (predictable_le_product 𝓕))
    (LinearIsometry.id : C →ₗᵢ[ℝ] C) u

end SHEStochastic
