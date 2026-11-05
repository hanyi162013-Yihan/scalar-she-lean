module

public import SHE.PastItoAlgebra
public import SHE.StandardTerminalPastLocality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.PredictableRotationLocality
open MeasureTheory SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω A C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
  [SecondCountableTopology C]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)
  (Φ : ℝ≥0 × Ω → A →ₗᵢ[ℝ] C)
  (hΦ : @Measurable ((ℝ≥0 × Ω) × A) C
    (F.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p ↦ Φ p.1 p.2))

/-- Predictable rotations commute with stopping on the original input
space, including the endpoint convention of its actual L2 process. -/
theorem stop (t : ℝ) (u : Process (E := A) F μ H) :
    PredictableItoRotation.processIsometry F μ H Φ hΦ (StoppedItoInputs.stop F μ H t u) =
      StoppedItoInputs.stop F μ H t (PredictableItoRotation.processIsometry F μ H Φ hΦ u) := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [PredictableItoRotation.processIsometry_ae F μ H Φ hΦ (StoppedItoInputs.stop F μ H t u),
    StoppedItoInputs.stop_ae F μ H t u,
    StoppedItoInputs.stop_ae F μ H t (PredictableItoRotation.processIsometry F μ H Φ hΦ u),
    PredictableItoRotation.processIsometry_ae F μ H Φ hΦ u] with p hp hs ht hu
  rw [hp, hs, ht]
  by_cases hb : p ∈ StoppedItoInputs.before (Ω := Ω) t
  · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb, hu]
  · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb, map_zero]

theorem event (t : ℝ≥0) (S : Set Ω) (hS : MeasurableSet[F t] S) (u : Process (E := A) F μ H) :
    PredictableItoRotation.processIsometry F μ H Φ hΦ (eventProcess F μ H t S hS u) =
      eventProcess F μ H t S hS (PredictableItoRotation.processIsometry F μ H Φ hΦ u) := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [PredictableItoRotation.processIsometry_ae F μ H Φ hΦ (eventProcess F μ H t S hS u),
    eventProcess_ae F μ H t S hS u,
    eventProcess_ae F μ H t S hS (PredictableItoRotation.processIsometry F μ H Φ hΦ u),
    PredictableItoRotation.processIsometry_ae F μ H Φ hΦ u] with p hp hs ht hu
  rw [hp, hs, ht]
  by_cases hb : p ∈ eventAfter t S
  · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb, hu]
  · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb, map_zero]

/-- Ordinary deterministic-past pullout transfers to the SAME rotated
integral. No independent choice of a new stochastic integral is made. -/
theorem pastLocality (I : StandardTerminalIto (C := C) (E := E) F μ H)
    (hlocal : StandardTerminalPastLocality I) :
    StandardTerminalPastLocality (PredictableItoRotation.integral F μ H Φ hΦ I) := by
  intro t S hS u
  change I.integral (PredictableItoRotation.processIsometry F μ H Φ hΦ (eventProcess F μ H t S hS u)) =ᵐ[μ]
    S.indicator (I.integral (PredictableItoRotation.processIsometry F μ H Φ hΦ (post F μ H t u)))
  rw [event]
  have hh := hlocal t S hS (PredictableItoRotation.processIsometry F μ H Φ hΦ u)
  rw [PastItoAlgebra.post_isometry] at hh
  exact hh

end SHEStochastic.PredictableRotationLocality
