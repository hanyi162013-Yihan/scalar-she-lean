module

public import SHE.TwoChannelCutoffModel
public import SHE.PredictableWordState

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.TwoChannelCutoffModel.Model
open MeasureTheory
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω]
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {h : ℝ≥0}
variable {κ : ℝ} {a : ℝ→ℝ} {ell M : ℝ} (m : TwoChannelCutoffModel.Model 𝓕 μ h κ a ell M)

def wordState : PredictableWordState.Data 𝓕 μ h := ⟨m.state,m.state_predictable⟩

theorem wordState_physicalState : m.wordState.physicalState=m.physicalState := rfl
theorem wordState_physicalField : m.wordState.physicalField=m.physicalField := rfl

end SHE.TwoChannelCutoffModel.Model
