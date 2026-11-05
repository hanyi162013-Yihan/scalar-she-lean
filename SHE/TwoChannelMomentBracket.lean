module

public import SHE.TwoChannelItoRows
public import SHE.StandardTerminalConditionalBDG

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.TwoChannelMomentBracket
open MeasureTheory PredictableL2 OrthogonalItoChannels
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (h : ℝ≥0)

/-- The actual block input has the sum of the two pathwise brackets.
This uses its concrete orthogonal-channel construction. -/
theorem bracket_block_eq (v w : Process (E := C) 𝓕 μ h) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖TwoChannelItoRows.block 𝓕 μ h v w (s, ω)‖ ^ 2) ∂timeMeasure h) =
      (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure h) +
      (∫⁻ s, ENNReal.ofReal (‖w (s, ω)‖ ^ 2) ∂timeMeasure h) := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure h)).quasiMeasurePreserving.ae
    (TwoChannelItoRows.block_ae 𝓕 μ h v w)
  have hvm : Measurable (fun p => ENNReal.ofReal (‖v p‖ ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (((Lp.stronglyMeasurable v).mono (predictable_le_product 𝓕)).norm.measurable.pow_const 2)
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  calc
    _ = ∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) + ENNReal.ofReal (‖w (s, ω)‖ ^ 2) ∂timeMeasure h := by
      apply lintegral_congr_ae
      filter_upwards [hω] with s hs
      simp only [Prod.swap] at hs
      rw [hs]
      have hn : ‖WithLp.toLp 2 (v (s, ω), w (s, ω))‖ ^ 2 =
          ‖v (s, ω)‖ ^ 2 + ‖w (s, ω)‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 _
      rw [hn, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    _ = _ := by
      have hm : Measurable (fun s : ℝ≥0 => ENNReal.ofReal (‖v (s, ω)‖ ^ 2)) :=
        hvm.comp (show Measurable (fun s : ℝ≥0 => (s, ω)) from measurable_id.prodMk measurable_const)
      exact lintegral_add_left hm _

theorem bracket_block_bound (v w : Process (E := C) 𝓕 μ h) {K₀ K₁ : ℝ}
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hv : ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖v (s, ω)‖ ^ 2) ∂timeMeasure h) ≤ ENNReal.ofReal K₀)
    (hw : ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖w (s, ω)‖ ^ 2) ∂timeMeasure h) ≤ ENNReal.ofReal K₁) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖TwoChannelItoRows.block 𝓕 μ h v w (s, ω)‖ ^ 2) ∂timeMeasure h) ≤
      ENNReal.ofReal (K₀ + K₁) := by
  filter_upwards [bracket_block_eq 𝓕 μ h v w, hv, hw] with ω he hv hw
  rw [he, ENNReal.ofReal_add hK₀ hK₁]
  exact add_le_add hv hw

end SHE.TwoChannelMomentBracket
