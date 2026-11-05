module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.GeometricUniformIntegrability
open MeasureTheory
open scoped ENNReal Topology

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α}

theorem lintegral_geometric {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∫⁻ x, f x ^ θ * g x ^ (1 - θ) ∂μ) ≤
      (∫⁻ x, f x ∂μ) ^ θ * (∫⁻ x, g x ∂μ) ^ (1 - θ) := by
  have hα : 0 < 1 - θ := sub_pos.mpr hθ1
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (Real.HolderConjugate.inv_one_sub_inv hθ0 hθ1) (hf.pow_const θ) (hg.pow_const (1 - θ))
  simpa only [Pi.mul_apply, ← ENNReal.rpow_mul, mul_inv_cancel₀ hθ0.ne', mul_inv_cancel₀ hα.ne',
    ENNReal.rpow_one, one_div, inv_inv] using hh

/-- A geometric interpolation between a family with mass at most one
and a single integrable majorant is uniformly integrable. This avoids
requiring an arbitrary p-moment producer for the Novikov limit. -/
theorem of_geometric_bound {f : ι → α → ℝ} {w : ι → α → ℝ≥0∞} {g : α → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hw : ∀ i, AEMeasurable (w i) μ)
    (hmass : ∀ i, (∫⁻ x, w i x ∂μ) ≤ 1) (hg : Integrable g μ)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hdom : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ₑ ≤ w i x ^ θ * ‖g x‖ₑ ^ (1 - θ)) :
    UnifIntegrable f 1 μ := by
  have hα : 0 < 1 - θ := sub_pos.mpr hθ1
  have hgUI : UnifIntegrable (fun _ : ι ↦ g) 1 μ :=
    unifIntegrable_const le_rfl ENNReal.one_ne_top (memLp_one_iff_integrable.mpr hg)
  let G (ε : ℝ≥0∞) := ⨆ (i : ι) (s : Set α) (_ : μ s ≤ ε), eLpNorm g 1 (μ.restrict s)
  change Filter.Tendsto G (𝓝 0) (𝓝 0) at hgUI
  have hlim : Filter.Tendsto (fun ε ↦ G ε ^ (1 - θ)) (𝓝 0) (𝓝 0) := by
    simpa only [ENNReal.zero_rpow_of_pos hα] using hgUI.ennrpow_const (1 - θ)
  apply tendsto_nhds_bot_mono hlim
  exact Filter.Eventually.of_forall fun ε ↦ by
    apply iSup_le
    intro i
    apply iSup_le
    intro s
    apply iSup_le
    intro hs
    calc
      eLpNorm (f i) 1 (μ.restrict s) = ∫⁻ x, ‖f i x‖ₑ ∂μ.restrict s :=
        eLpNorm_one_eq_lintegral_enorm (hf i).restrict
      _ ≤ ∫⁻ x, w i x ^ θ * ‖g x‖ₑ ^ (1 - θ) ∂μ.restrict s :=
        lintegral_mono_ae (ae_restrict_of_ae (hdom i))
      _ ≤ (∫⁻ x, w i x ∂μ.restrict s) ^ θ * (∫⁻ x, ‖g x‖ₑ ∂μ.restrict s) ^ (1 - θ) :=
        lintegral_geometric (hw i).restrict hg.aestronglyMeasurable.enorm.restrict hθ0 hθ1
      _ ≤ 1 ^ θ * eLpNorm g 1 (μ.restrict s) ^ (1 - θ) := by
        rw [eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable.restrict]
        gcongr
        exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans (hmass i)
      _ = eLpNorm g 1 (μ.restrict s) ^ (1 - θ) := by rw [ENNReal.one_rpow, one_mul]
      _ ≤ G ε ^ (1 - θ) := ENNReal.rpow_le_rpow
        (le_iSup_of_le i (le_iSup_of_le s (le_iSup_of_le hs le_rfl))) hα.le

end SHEStochastic.GeometricUniformIntegrability
