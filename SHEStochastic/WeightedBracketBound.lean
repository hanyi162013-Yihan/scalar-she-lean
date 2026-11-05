module

public import SHEStochastic.PredictableEnvelopeMultiplier
public import SHE.StandardTerminalNovikov

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.WeightedBracketBound
open MeasureTheory SHE SHE.PredictableL2 Filter
open scoped NNReal ENNReal

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

theorem bracket_nonneg (u : Process (E := C) F μ H) (ω : Ω) :
    0 ≤ StochasticExponential.bracket F μ H u ω := integral_nonneg fun _ ↦ sq_nonneg _

theorem lintegral_eq (u : Process (E := C) F μ H) :
    ∀ᵐ ω ∂μ, (∫⁻ r, ENNReal.ofReal (‖u (r, ω)‖ ^ 2) ∂timeMeasure H) =
      ENNReal.ofReal (StochasticExponential.bracket F μ H u ω) := by
  have hi := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq
  filter_upwards [hi.prod_left_ae] with ω hω
  exact (ofReal_integral_eq_lintegral_ofReal hω (Eventually.of_forall fun _ ↦ sq_nonneg _)).symm

/-- The bracket of a scalar-weighted row is bounded by the squared
path envelope times the original bracket, with the original clock. -/
theorem weighted (u v : Process (E := C) F μ H) (w : ℝ≥0 × Ω → ℝ)
    (hv : v =ᵐ[energyMeasure μ H] (fun p ↦ w p • u p))
    (D : Ω → ℝ) (hD0 : ∀ ω, 0 ≤ D ω) (hb : ∀ᵐ p ∂energyMeasure μ H, |w p| ≤ D p.2) :
    ∀ᵐ ω ∂μ, StochasticExponential.bracket F μ H v ω ≤
      D ω ^ 2 * StochasticExponential.bracket F μ H u ω := by
  have hiu := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq
  have hiv := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)).norm.integrable_sq
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hv
  have hbs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hb
  filter_upwards [hiu.prod_left_ae, hiv.prod_left_ae, Measure.ae_ae_of_ae_prod hs,
    Measure.ae_ae_of_ae_prod hbs] with ω hu hv hr hbr
  change (∫ r, ‖v (r, ω)‖ ^ 2 ∂timeMeasure H) ≤ D ω ^ 2 * ∫ r, ‖u (r, ω)‖ ^ 2 ∂timeMeasure H
  rw [← integral_const_mul]
  apply integral_mono_ae hv (hu.const_mul (D ω ^ 2))
  filter_upwards [hr, hbr] with r hr hbω
  change v (r, ω) = w (r, ω) • u (r, ω) at hr
  rw [hr, norm_smul, Real.norm_eq_abs, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) hbω 2) (sq_nonneg _)

/-- A bounded input has a deterministic bracket cap. This cap supplies
finite moments during BDG induction; it does not enter its final constant. -/
theorem bounded (u : Process (E := C) F μ H) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M) :
    ∀ᵐ ω ∂μ, StochasticExponential.bracket F μ H u ω ≤
      (timeMeasure H).real Set.univ * M ^ 2 := by
  have hh := ae_of_ae_trim (predictable_le_product F) hu
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hh
  have hi := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq
  filter_upwards [hi.prod_left_ae, Measure.ae_ae_of_ae_prod hs] with ω hi hr
  calc
    _ ≤ ∫ _r : ℝ≥0, M ^ 2 ∂timeMeasure H := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [hr] with r hr
      exact pow_le_pow_left₀ (norm_nonneg _) hr 2
    _ = _ := by rw [integral_const, smul_eq_mul]

end SHEStochastic.WeightedBracketBound
