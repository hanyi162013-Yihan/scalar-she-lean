module

public import SHE.NativeKernelAction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRandomKernel
open MeasureTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance nativeKernelAlgebra_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance nativeKernelAlgebra_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- An exact scalar kernel splitting is an exact signed difference of the actual
bounded integral operators, before any right factor is applied. -/
theorem integralOperator_eq_sub
    {F G H : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H)
    {B : ℝ} (hB : 0 ≤ B) (hbF : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B)
    (hbG : ∀ ω y x, ‖G (ω,(y,x))‖ ≤ B) (hbH : ∀ ω y x, ‖H (ω,(y,x))‖ ≤ B)
    (hsplit : ∀ ω y x, F (ω,(y,x))=G (ω,(y,x))-H (ω,(y,x))) (ω : Ω) :
    integralOperator F ω=integralOperator G ω-integralOperator H ω := by
  apply ContinuousLinearMap.ext
  intro v
  have hv := ((Lp.memLp v).integrable (by norm_num : (1:ENNReal)≤2)).norm
  have hi {J : Ω × (HeatCircle × HeatCircle) → ℂ} (hJ : Measurable J)
      (hbJ : ∀ ω y x, ‖J (ω,(y,x))‖ ≤ B) (x : HeatCircle) :
      Integrable (fun y : HeatCircle => J (ω,(y,x))*v y) haarAddCircle := by
    apply (hv.const_mul B).mono'
      ((hJ.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))).aestronglyMeasurable.mul
        (Lp.memLp v).aestronglyMeasurable)
    exact ae_of_all _ (fun y => by
      change ‖J (ω,(y,x))*v y‖≤B*‖v y‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbJ ω y x) (norm_nonneg _))
  apply Lp.ext
  filter_upwards [integralOperator_ae hF hB hbF ω v,integralOperator_ae hG hB hbG ω v,
    integralOperator_ae hH hB hbH ω v,Lp.coeFn_sub (integralOperator G ω v) (integralOperator H ω v)]
    with x hf hg hh hs
  change integralOperator F ω v x=(integralOperator G ω v-integralOperator H ω v) x
  rw [hf,hs,Pi.sub_apply,hg,hh]
  simp_rw [hsplit ω,sub_mul]
  exact integral_sub (hi hG hbG x) (hi hH hbH x)

end SHE.NativeRandomKernel
