module

public import SHE.StoppedInputAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.StoppedInputAlgebra
open MeasureTheory PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem stop_lipschitz (t : ℝ) : LipschitzWith 1 (stop (C := C) 𝓕 μ H t) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [dist_eq_norm,dist_eq_norm,← StoppedDampingClock.stop_sub,NNReal.coe_one,one_mul]
  exact StoppedInputResolvent.stop_norm_le 𝓕 μ H (v-w) t

theorem stop_continuous (t : ℝ) : Continuous (stop (C := C) 𝓕 μ H t) :=
  (stop_lipschitz 𝓕 μ H t).continuous

end SHE.StoppedInputAlgebra
