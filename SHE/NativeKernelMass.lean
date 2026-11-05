module

public import SHE.NativeKernelAction

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRandomKernel
open Set Filter MeasureTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance nativeKernelMass_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance nativeKernelMass_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance nativeKernelMass_exponentLower : Fact (1 ≤ (2:ℝ≥0∞)) := ⟨by norm_num⟩
local instance nativeKernelMass_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance nativeKernelMass_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

theorem column_norm_sq {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) {B : ℝ} (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B)
    (ω : Ω) (y : HeatCircle) : ‖column F (ω,y)‖^2=∫ x, ‖F (ω,(y,x))‖^2 ∂haarAddCircle := by
  rw [L2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [column_ae hF hb ω y] with x hx
  change ‖column F (ω,y) x‖^2=‖F (ω,(y,x))‖^2
  rw [hx]

/-- The Hilbert-valued kernel mass is exactly the scalar spatial product
mass of the original representative. -/
theorem kernel_norm_sq {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (ω : Ω) :
    ‖kernel F ω‖^2=∫ p : HeatCircle × HeatCircle, ‖F (ω,p)‖^2
      ∂(haarAddCircle (T:=2*π)).prod haarAddCircle := by
  rw [kernel,HilbertL2Fields.realize_norm_sq _ (column_memLp hF hB hb)]
  have hi : Integrable (fun p : HeatCircle × HeatCircle => ‖F (ω,p)‖^2)
      ((haarAddCircle (T:=2*π)).prod haarAddCircle) := by
    apply (integrable_const (B^2)).mono'
      ((hF.comp (measurable_const.prodMk measurable_id)).norm.pow_const (2:ℕ)).aestronglyMeasurable
    exact ae_of_all _ (fun p => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb ω p.1 p.2) 2)
  rw [integral_prod _ hi]
  exact integral_congr_ae (ae_of_all _ (column_norm_sq hF hb ω))

theorem kernel_mass_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) :
    Integrable (fun ω => ‖kernel F ω‖^2) μ := by
  have hsharp (y : HeatCircle) : (∫ ω, ‖column F (ω,y)‖^2 ∂μ) ≤ B^2 := by
    have hm : Measurable (fun ω => ‖column F (ω,y)‖^2) :=
      (((column_measurable hF hb).comp (measurable_id.prodMk measurable_const)).norm.pow_const (2:ℕ))
    have hbound (ω : Ω) : ‖column F (ω,y)‖^2 ≤ B^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (column_norm_le hF hB hb (ω,y)) 2
    have hi : Integrable (fun ω => ‖column F (ω,y)‖^2) μ :=
      (integrable_const (B^2)).mono' hm.aestronglyMeasurable (ae_of_all _ (fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hbound ω))
    exact (integral_mono hi (integrable_const (B^2)) hbound).trans_eq (by simp)
  exact (HilbertL2Fields.expected_norm_sq_bound (ν:=haarAddCircle (T:=2*π)) μ
    (column_measurable hF hb) (fun ω y => column_norm_le hF hB hb (ω,y)) hsharp).1

end SHE.NativeRandomKernel
