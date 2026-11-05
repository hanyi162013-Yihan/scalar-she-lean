module

public import SHEStochastic.PredictableTruncation
public import SHE.StandardTerminalBDGPower
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.BDGBoundedReduction
open MeasureTheory SHE SHE.PredictableL2 Filter
open scoped NNReal ENNReal Topology

variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- To prove the original BDG bound for every L² input it suffices to
prove it on bounded predictable rows. Truncation preserves each sample
path's energy; Fatou supplies the exact same constant in the limit.
This is a reduction, not a proof of the bounded-row BDG premise. -/
theorem of_bounded (p : ℕ) (I : StandardTerminalIto (C := C) (E := E) F μ H) (B : ℝ≥0)
    (hb : ∀ (v : Process (E := C) F μ H) (n : ℕ),
      (∀ᵐ x ∂(energyMeasure μ H).trim (predictable_le_product F), ‖v x‖ ≤ (n : ℝ)) →
      (∫⁻ ω, ENNReal.ofReal (‖I.integral v ω‖ ^ (2 * p)) ∂μ) ≤
        (B : ℝ≥0∞) * ∫⁻ ω, (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure H) ^ p ∂μ) :
    StandardTerminalBDGPower p I B := by
  intro u
  have ht := tendstoInMeasure_of_tendsto_Lp
    (I.integral.continuous.tendsto u |>.comp (PredictableTruncation.tendsto u))
  obtain ⟨ns, hns, hlim⟩ := ht.exists_seq_tendsto_ae
  have hbound (n : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (‖I.integral (PredictableTruncation.process u n) ω‖ ^ (2 * p)) ∂μ) ≤
        (B : ℝ≥0∞) * ∫⁻ ω, (∫⁻ s, ENNReal.ofReal (‖u (s, ω)‖ ^ 2) ∂timeMeasure H) ^ p ∂μ := by
    refine (hb _ n (PredictableTruncation.bounded u n)).trans ?_
    refine mul_le_mul_right ?_ (B : ℝ≥0∞)
    apply lintegral_mono_ae
    filter_upwards [PredictableTruncation.energy_le u n] with ω hω
    exact pow_le_pow_left₀ zero_le hω p
  calc
    _ = ∫⁻ ω, liminf (fun k ↦ ENNReal.ofReal
        (‖I.integral (PredictableTruncation.process u (ns k)) ω‖ ^ (2 * p))) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with ω hω
      exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hω.norm.pow (2 * p))).liminf_eq.symm
    _ ≤ liminf (fun k ↦ ∫⁻ ω, ENNReal.ofReal
        (‖I.integral (PredictableTruncation.process u (ns k)) ω‖ ^ (2 * p)) ∂μ) atTop :=
      lintegral_liminf_le (fun k ↦ ((Lp.stronglyMeasurable _).norm.pow (2 * p)).measurable.ennreal_ofReal)
    _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall (fun k ↦ hbound (ns k))).frequently

end SHEStochastic.BDGBoundedReduction
