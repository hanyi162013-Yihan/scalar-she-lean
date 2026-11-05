module

public import SHE.PredictableScalarField

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PredictableWordState
open MeasureTheory PredictableL2 NativeHeatObservation
open scoped NNReal
local instance : MeasurableSpace DyadicApproximation.RealL2 := borel _
local instance : BorelSpace DyadicApproximation.RealL2 := ⟨rfl⟩
local instance : MeasurableSpace StoppedFourier.CircleL2 := borel _
local instance : BorelSpace StoppedFourier.CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The spatial approximation argument only needs a predictable L²
state. Its scalar field is the proved joint representative, independently
of the number of noise channels or the equation producing the state. -/
structure Data (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0) where
  state : ℝ≥0×Ω→DyadicApproximation.RealL2
  state_predictable : StronglyMeasurable[𝓕.predictable] state

namespace Data
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {h : ℝ≥0} (m : Data 𝓕 μ h)

def physicalState (p : Ω×ℝ) : StoppedFourier.CircleL2 := embed (m.state (p.2.toNNReal,p.1))
def physicalField (p : Ω×(ℝ×StoppedFourier.HeatCircle)) : ℝ :=
  PredictableScalarField.wordField m.state p.1 p.2

theorem physicalState_measurable : Measurable m.physicalState := by
  have hU : Measurable m.state := (m.state_predictable.mono (predictable_le_product 𝓕)).measurable
  exact embed.continuous.measurable.comp (hU.comp
    ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))

theorem physicalField_measurable : Measurable m.physicalField :=
  PredictableScalarField.wordField_measurable 𝓕 m.state_predictable

end Data
end SHE.PredictableWordState
