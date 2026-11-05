module

public import SHE.InverseClockLocality
public import SHEStochastic.FiniteCylindricalLocality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeClockLocality
open MeasureTheory SHE SHE.PredictableL2 SHE.PredictableTimeDilation SHE.PastItoInputs
open scoped NNReal ENNReal

variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
  (c : ℝ≥0) (hc : 0 < c) (H : ℝ≥0)

local notation "FN" => filtration F (clock c hc)

/-- Forward deterministic clock locality is the inverse of the existing
input identity; no second stochastic pullout argument is needed. -/
theorem event (t : ℝ≥0) (S : Set Ω) (hS : MeasurableSet[FN t] S)
    (u : Process (E := C) FN μ (c*H)) :
    processIsometry F μ c hc H (eventProcess FN μ (c*H) t S hS u) =
      eventProcess F μ H ((clock c hc).symm t) S hS (processIsometry F μ c hc H u) := by
  let e := processEquivalence (C := C) F μ c hc H
  have hh := InverseClockLocality.event_input F μ c hc H ((clock c hc).symm t) S hS (e u)
  have he := congrArg e hh
  dsimp only [e] at he
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply] at he
  simpa only [OrderIso.apply_symm_apply, processEquivalence_apply] using he.symm

theorem locality (J : StandardTerminalIto (C := C) (E := E) F μ H)
    (hlocal : StandardTerminalPastLocality J) :
    StandardTerminalPastLocality (PredictableTimeDilation.integral F μ c hc H J) := by
  intro t S hS u
  have hh := hlocal ((clock c hc).symm t) S hS (processIsometry F μ c hc H u)
  change J.integral (processIsometry F μ c hc H (eventProcess FN μ (c*H) t S hS u)) =ᵐ[μ]
    S.indicator (J.integral (processIsometry F μ c hc H (post FN μ (c*H) t u)))
  have hp : processIsometry F μ c hc H (post FN μ (c*H) t u) =
      post F μ H ((clock c hc).symm t) (processIsometry F μ c hc H u) :=
    event F μ c hc H t Set.univ MeasurableSet.univ u
  rw [event, hp]
  exact hh

end SHEStochastic.NativeClockLocality
