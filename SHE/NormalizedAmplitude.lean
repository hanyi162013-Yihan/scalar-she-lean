module

public import SHE.SignedKernelTruncation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NormalizedKernelSplit
open Set Filter MeasureTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance normalizedAmplitude_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The normalized amplitude is constructed from the actual scalar
kernel, rather than supplied as an independent random field. -/
def normalize (H : Space → ℝ) (F : Ω × Space → ℂ) (p : Ω × Space) : ℝ := (F p).re/H p.2

theorem normalize_measurable {H : Space → ℝ} {F : Ω × Space → ℂ}
    (hH : Measurable H) (hF : Measurable F) : Measurable (normalize H F) :=
  (Complex.continuous_re.measurable.comp hF).div (hH.comp measurable_snd)

theorem fullKernel_normalize {H : Space → ℝ} {F : Ω × Space → ℂ}
    (hH : ∀ p, 0 < H p) (hreal : ∀ p, (F p).im=0) : fullKernel H (normalize H F)=F := by
  funext p
  apply Complex.ext
  · change H p.2*((F p).re/H p.2)=(F p).re
    field_simp [(hH p.2).ne']
  · exact (hreal p).symm

/-- A genuine relative kernel moment gives the corresponding normalized
amplitude moment, with no independence and no spatial supremum. -/
theorem normalize_moment (μ : Measure Ω) {H : Space → ℝ} {F : Ω × Space → ℂ}
    (hF : Measurable F) (p : Space) (hH : 0 < H p) (n : ℕ)
    (hFn : Integrable (fun ω => ‖F (ω,p)‖^n) μ) {C : ℝ}
    (hbound : (∫ ω, ‖F (ω,p)‖^n ∂μ) ≤ C*(H p)^n) :
    Integrable (fun ω => |normalize H F (ω,p)|^n) μ ∧
      (∫ ω, |normalize H F (ω,p)|^n ∂μ) ≤ C := by
  have hslice : Measurable (fun ω => F (ω,p)) := hF.comp (measurable_id.prodMk measurable_const)
  have hm : Measurable (fun ω => |normalize H F (ω,p)|^n) :=
    (continuous_abs.measurable.comp ((Complex.continuous_re.measurable.comp hslice).div_const (H p))).pow_const n
  have hp (ω : Ω) : |normalize H F (ω,p)|^n ≤ ‖F (ω,p)‖^n/(H p)^n := by
    change |(F (ω,p)).re/H p|^n≤_
    rw [abs_div,abs_of_pos hH,div_pow]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (F (ω,p))) n) (pow_nonneg hH.le _)
  have hi : Integrable (fun ω => |normalize H F (ω,p)|^n) μ := by
    apply (hFn.div_const ((H p)^n)).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun ω => by rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]; exact hp ω)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω, ‖F (ω,p)‖^n/(H p)^n ∂μ := integral_mono hi (hFn.div_const _) hp
    _ = (∫ ω, ‖F (ω,p)‖^n ∂μ)/(H p)^n := integral_div _ _
    _ ≤ C := (div_le_iff₀ (pow_pos hH _)).mpr hbound

theorem heatEnvelope_pos {D δ w : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hw : 0 < w) (p : Space) :
    0 < heatEnvelope D δ w p := by
  have hk : 0 < ‖ProfileVariance.heatPhysical (8*w) p.1 p.2‖ := by
    rw [← NativeHeatSpan.kernel_eq_physical (by positivity : 0 < 8*w)]
    exact NodeKernelLocal.kernel_norm_pos (NativeHeatSpan.clock_pos (by positivity : 0 < 8*w)) _
  exact mul_pos (mul_pos (mul_pos hD (Real.rpow_pos_of_pos hδ _)) (Real.rpow_pos_of_pos hw _)) hk

end SHE.NormalizedKernelSplit
