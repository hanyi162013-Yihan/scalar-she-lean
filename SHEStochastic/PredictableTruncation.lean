module

public import SHEStochastic.PredictableMultiplier

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.PredictableTruncation
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

def multiplier (u : Process (E := C) F μ H) (n : ℕ) (p : ℝ≥0 × Ω) : ℝ :=
  if ‖u p‖ ≤ (n : ℝ) then 1 else 0

theorem predictable (u : Process (E := C) F μ H) (n : ℕ) :
    StronglyMeasurable[F.predictable] (multiplier u n) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact stronglyMeasurable_const.ite
    (measurableSet_le (Lp.stronglyMeasurable u).norm.measurable measurable_const)
    stronglyMeasurable_const

theorem bound (u : Process (E := C) F μ H) (n : ℕ) (p : ℝ≥0 × Ω) :
    |multiplier u n p| ≤ 1 := by
  simp only [multiplier]
  split_ifs <;> norm_num

def process (u : Process (E := C) F μ H) (n : ℕ) : Process (E := C) F μ H :=
  PredictableMultiplier.process u (multiplier u n) (predictable u n) 1 (bound u n)

theorem process_ae_trim (u : Process (E := C) F μ H) (n : ℕ) :
    process u n =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
      (fun p ↦ if ‖u p‖ ≤ (n : ℝ) then u p else 0) := by
  filter_upwards [PredictableMultiplier.process_ae_trim u _ (predictable u n) 1 (bound u n)] with p hp
  change process u n p = multiplier u n p • u p at hp
  rw [hp]
  by_cases h : ‖u p‖ ≤ (n : ℝ) <;> simp [multiplier, h]

theorem norm_le (u : Process (E := C) F μ H) (n : ℕ) :
    ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖process u n p‖ ≤ ‖u p‖ := by
  filter_upwards [process_ae_trim u n] with p hp
  rw [hp]
  split_ifs <;> simp

theorem bounded (u : Process (E := C) F μ H) (n : ℕ) :
    ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖process u n p‖ ≤ (n : ℝ) := by
  filter_upwards [process_ae_trim u n] with p hp
  rw [hp]
  split_ifs with h
  · exact h
  · simp

/-- Pointwise norm truncation converges in the original predictable L²
space and never increases the pathwise energy. -/
theorem tendsto (u : Process (E := C) F μ H) :
    Filter.Tendsto (process u) Filter.atTop (𝓝 u) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply LpDominatedLimit.tendsto u u (process u) (norm_le u)
    (Filter.Eventually.of_forall fun _ ↦ le_rfl)
  filter_upwards [ae_all_iff.mpr (process_ae_trim u)] with p hp
  have hn : ∀ᶠ n : ℕ in Filter.atTop, ‖u p‖ ≤ (n : ℝ) := by
    exact Filter.eventually_atTop.2 ⟨⌈‖u p‖⌉₊, fun n hn ↦
      (Nat.le_ceil _).trans (by exact_mod_cast hn)⟩
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [hn] with n hn
  exact ((hp n).trans (if_pos hn)).symm

theorem energy_le (u : Process (E := C) F μ H) (n : ℕ) :
    ∀ᵐ ω ∂μ,
      (∫⁻ r, ENNReal.ofReal (‖process u n (r, ω)‖ ^ 2) ∂timeMeasure H) ≤
        ∫⁻ r, ENNReal.ofReal (‖u (r, ω)‖ ^ 2) ∂timeMeasure H := by
  have hp := ae_eq_of_ae_eq_trim (process_ae_trim u n)
  have h := hp.mono (fun p hp ↦ by
    change process u n p = if ‖u p‖ ≤ (n : ℝ) then u p else 0 at hp
    have hn : ‖process u n p‖ ≤ ‖u p‖ := by rw [hp]; split_ifs <;> simp
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hn 2))
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae h
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  exact lintegral_mono_ae hω

end SHEStochastic.PredictableTruncation
