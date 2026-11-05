module

public import SHE.PredictableBracketDifference

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHE.PredictableBracketAdd
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)

theorem bracket_neg (v : Process (E := C) 𝓕 μ H) :
    ∀ᵐ ω ∂μ, (∫⁻ s,ENNReal.ofReal (‖(-v : Process (E := C) 𝓕 μ H) (s,ω)‖^2) ∂timeMeasure H) =
      (∫⁻ s,ENNReal.ofReal (‖v (s,ω)‖^2) ∂timeMeasure H) := by
  have he : ∀ᵐ p ∂energyMeasure μ H, (-v : Process (E := C) 𝓕 μ H) p = -v p :=
    ae_eq_of_ae_eq_trim (Lp.coeFn_neg v)
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  apply lintegral_congr_ae
  filter_upwards [hω] with s hs
  simp only [Prod.swap] at hs
  rw [hs,norm_neg]

/-- Actual predictable sum brackets require no independence of the two
inputs and are computed in one fixed full-horizon integration space. -/
theorem bracket_add_bound (v w : Process (E := C) 𝓕 μ H) {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hv : ∀ᵐ ω ∂μ, (∫⁻ s,ENNReal.ofReal (‖v (s,ω)‖^2) ∂timeMeasure H) ≤ ENNReal.ofReal K)
    (hw : ∀ᵐ ω ∂μ, (∫⁻ s,ENNReal.ofReal (‖w (s,ω)‖^2) ∂timeMeasure H) ≤ ENNReal.ofReal L) :
    ∀ᵐ ω ∂μ, (∫⁻ s,ENNReal.ofReal (‖(v+w : Process (E := C) 𝓕 μ H) (s,ω)‖^2) ∂timeMeasure H) ≤
      ENNReal.ofReal (2*K+2*L) := by
  have hs := PredictableBracketDifference.bracket_sub_le 𝓕 μ H v (-w)
  simp only [sub_neg_eq_add] at hs
  filter_upwards [hs,bracket_neg 𝓕 μ H w,hv,hw] with ω hs hn hv hw
  rw [hn] at hs
  apply hs.trans
  calc
    _ ≤ 2*ENNReal.ofReal K+2*ENNReal.ofReal L :=
      add_le_add (mul_le_mul_right hv _) (mul_le_mul_right hw _)
    _ = _ := by
      rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) hK) (mul_nonneg (by norm_num) hL)]
      simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat]

end SHE.PredictableBracketAdd
