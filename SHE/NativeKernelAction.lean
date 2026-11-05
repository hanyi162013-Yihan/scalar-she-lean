module

public import SHE.NativeRandomKernel
public import SHE.LpIntegralFubini

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRandomKernel
open Set Filter MeasureTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance nativeKernelAction_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance nativeKernelAction_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance nativeKernelAction_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance nativeKernelAction_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The canonical bounded operator has exactly the original scalar
kernel action, proved by L² Bochner Fubini rather than point evaluation
on L². -/
theorem integralOperator_ae {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (ω : Ω) (v : CircleL2) :
    (integralOperator F ω v : HeatCircle → ℂ)=ᵐ[haarAddCircle]
      fun x => ∫ y : HeatCircle, F (ω,(y,x))*v y ∂haarAddCircle := by
  have hv : Integrable (v : HeatCircle → ℂ) haarAddCircle :=
    (Lp.memLp v).integrable (by norm_num : (1:ENNReal)≤2)
  have hc : Measurable (fun y => column F (ω,y)) :=
    (column_measurable hF hb).comp (measurable_const.prodMk measurable_id)
  have hcols : Integrable (fun y => v y • column F (ω,y)) haarAddCircle := by
    apply (hv.norm.mul_const B).mono'
      ((Lp.memLp v).aestronglyMeasurable.smul hc.aestronglyMeasurable)
    exact ae_of_all _ (fun y => by
      change ‖v y • column F (ω,y)‖≤‖v y‖*B
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (column_norm_le hF hB hb (ω,y)) (norm_nonneg _))
  let H : HeatCircle × HeatCircle → ℂ := fun p => v p.1*F (ω,(p.1,p.2))
  have hH : Integrable H ((haarAddCircle (T:=2*π)).prod haarAddCircle) := by
    apply ((hv.norm.mul_const B).comp_fst (haarAddCircle (T:=2*π))).mono'
      ((Lp.memLp v).aestronglyMeasurable.comp_fst.mul
        (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    exact ae_of_all _ (fun p => by
      change ‖v p.1*F (ω,(p.1,p.2))‖≤‖v p.1‖*B
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb ω p.1 p.2) (norm_nonneg _))
  have he := LpIntegralFubini.integral_ae (E:=ℂ) (haarAddCircle (T:=2*π))
    (haarAddCircle (T:=2*π)) (fun y => v y • column F (ω,y)) hcols H hH
    (ae_of_all _ (fun y => by
      filter_upwards [Lp.coeFn_smul (v y) (column F (ω,y)),column_ae hF hb ω y] with x hs hx
      change (v y • column F (ω,y)) x=H (y,x)
      rw [hs,Pi.smul_apply,hx]
      rfl))
  rw [← integralOperator_eq_integral hF hB hb ω v] at he
  exact he.mono (fun x hx => hx.trans (integral_congr_ae (ae_of_all _ (fun y => mul_comm _ _))))

end SHE.NativeRandomKernel
