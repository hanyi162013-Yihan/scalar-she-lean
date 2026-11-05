module

public import SHE.PredictableClock
public import SHE.ProcessEnergy

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatInitialProcess
open MeasureTheory Set PredictableL2 LowBands
open scoped NNReal ENNReal
local instance heatInitialProcess_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance heatInitialProcess_stateSigma : MeasurableSpace StateL2 := borel StateL2
local instance heatInitialProcess_stateBorel : BorelSpace StateL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)

def function (u₀ : StateL2) (p : ℝ≥0 × Ω) : StateL2 := RealHeat.realHeat p.1 u₀

theorem predictable (u₀ : StateL2) : StronglyMeasurable[𝓕.predictable] (function u₀ (Ω := Ω)) :=
  (RealHeat.continuous_realHeat_action.measurable.comp
    ((PredictableClock.real_time_measurable 𝓕).prodMk measurable_const)).stronglyMeasurable

theorem memLp (u₀ : StateL2) :
    @MemLp _ _ 𝓕.predictable _ _ (function u₀ (Ω := Ω)) 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)) := by
  have : IsFiniteMeasure (energyMeasure μ h) := by dsimp only [energyMeasure]; infer_instance
  exact MemLp.of_bound (predictable 𝓕 u₀).aestronglyMeasurable ‖u₀‖
    (Filter.Eventually.of_forall (fun p => RealHeat.realHeat_contraction p.1 u₀))

/-- The genuine deterministic heat evolution as a complete predictable
L² process, for arbitrary real spatial L² initial data. -/
def process (u₀ : StateL2) : Process (E := StateL2) 𝓕 μ h :=
  (memLp 𝓕 μ h u₀).toLp (function u₀ (Ω := Ω))

theorem process_ae (u₀ : StateL2) :
    process 𝓕 μ h u₀ =ᵐ[energyMeasure μ h] function u₀ :=
  ae_eq_of_ae_eq_trim (memLp 𝓕 μ h u₀).coeFn_toLp

end SHE.HeatInitialProcess
