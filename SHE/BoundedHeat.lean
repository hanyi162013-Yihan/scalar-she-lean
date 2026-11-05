module

public import SHE.HeatKernelLocal

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.BoundedHeat
open Set MeasureTheory AddCircle CircleHeat HeatMarkov
local instance boundedHeat_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance boundedHeat_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩

def value (t : ℝ) (ht : 0 < t) (f : CircleL2) (x : AddCircle (1:ℝ)) : ℂ :=
  ∫ y : AddCircle (1:ℝ),kernel t ht (y-x)*f y ∂haarAddCircle

theorem product_integrable {t : ℝ} (ht : 0 < t) (f : CircleL2) (x : AddCircle (1:ℝ)) :
    Integrable (fun y : AddCircle (1:ℝ) => kernel t ht (y-x)*f y) haarAddCircle := by
  have hf := ((Lp.memLp f).integrable (by norm_num : (1:ENNReal) ≤ 2)).norm
  apply (hf.const_mul ‖kernel t ht‖).mono'
  · exact (((kernel t ht).continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)
  · filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((kernel t ht).norm_coe_le_norm _) (norm_nonneg _)

theorem shifted_mass {t : ℝ} (ht : 0 < t) (x : AddCircle (1:ℝ)) :
    (∫ y : AddCircle (1:ℝ),‖kernel t ht (y-x)‖ ∂haarAddCircle)=1 :=
  (integral_sub_right_eq_self (fun y : AddCircle (1:ℝ) => ‖kernel t ht y‖)
    (μ := haarAddCircle) x).trans (kernel_norm_mass ht)

theorem shifted_norm_integrable {t : ℝ} (ht : 0 < t) (x : AddCircle (1:ℝ)) :
    Integrable (fun y : AddCircle (1:ℝ) => ‖kernel t ht (y-x)‖) haarAddCircle := by
  have hc : Continuous (fun y : AddCircle (1:ℝ) => ‖kernel t ht (y-x)‖) :=
    ((kernel t ht).continuous.comp (continuous_id.sub continuous_const)).norm
  simpa only [IntegrableOn,Measure.restrict_univ] using
    hc.continuousOn.integrableOn_compact (K := univ) isCompact_univ

theorem norm_bound {t : ℝ} (ht : 0 < t) (f : CircleL2) {M : ℝ}
    (hf : ∀ᵐ y ∂haarAddCircle,‖f y‖ ≤ M) (x : AddCircle (1:ℝ)) : ‖value t ht f x‖ ≤ M := by
  calc
    _ ≤ ∫ y : AddCircle (1:ℝ),‖kernel t ht (y-x)*f y‖ ∂haarAddCircle := norm_integral_le_integral_norm _
    _ ≤ ∫ y : AddCircle (1:ℝ),‖kernel t ht (y-x)‖*M ∂haarAddCircle := by
      apply integral_mono_ae (product_integrable ht f x).norm ((shifted_norm_integrable ht x).mul_const M)
      filter_upwards [hf] with y hy
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ = M := by rw [integral_mul_const,shifted_mass ht x,one_mul]

theorem local_difference {t : ℝ} (ht : 0 < t) (f : CircleL2) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ᵐ y ∂haarAddCircle,‖f y‖ ≤ M) (x w : AddCircle (1:ℝ))
    (hnear : dist x w ≤ Real.sqrt t) :
    ‖value t ht f x-value t ht f w‖ ≤ (localConstant/Real.sqrt t)*M*dist x w := by
  have hC : 0 ≤ localConstant := localConstant_pos.le
  let F : AddCircle (1:ℝ) → ℂ := fun y => (kernel t ht (y-x)-kernel t ht (y-w))*f y
  have hi : Integrable F haarAddCircle := by
    have hs := (product_integrable ht f x).sub (product_integrable ht f w)
    apply hs.congr
    filter_upwards with y
    change kernel t ht (y-x)*f y-kernel t ht (y-w)*f y=
      (kernel t ht (y-x)-kernel t ht (y-w))*f y
    ring
  have he : value t ht f x-value t ht f w=∫ y,F y ∂haarAddCircle := by
    rw [value,value,← integral_sub (product_integrable ht f x) (product_integrable ht f w)]
    apply integral_congr_ae
    filter_upwards with y
    change _=(kernel t ht (y-x)-kernel t ht (y-w))*f y
    ring
  have hker (y : AddCircle (1:ℝ)) :
      ‖kernel t ht (y-x)-kernel t ht (y-w)‖ ≤
        (localConstant/Real.sqrt t)*‖kernel (8*t) (by positivity) (y-x)‖*dist x w := by
    have hh := kernel_translation_bound ht (y-x) (x-w) (by simpa only [dist_eq_norm] using hnear)
    simpa only [show y-x+(x-w)=y-w by abel,← dist_eq_norm] using hh
  rw [he]
  calc
    _ ≤ ∫ y,‖F y‖ ∂haarAddCircle := norm_integral_le_integral_norm _
    _ ≤ ∫ y,((localConstant/Real.sqrt t)*M*dist x w)*
        ‖kernel (8*t) (by positivity) (y-x)‖ ∂haarAddCircle := by
      apply integral_mono_ae hi.norm ((shifted_norm_integrable (by positivity : 0 < 8*t) x).const_mul _)
      filter_upwards [hf] with y hy
      change ‖(kernel t ht (y-x)-kernel t ht (y-w))*f y‖ ≤ _
      rw [norm_mul]
      have hb := mul_le_mul (hker y) hy (norm_nonneg (f y)) (by positivity :
        0 ≤ (localConstant/Real.sqrt t)*‖kernel (8*t) (by positivity) (y-x)‖*dist x w)
      exact hb.trans_eq (by ring)
    _ = _ := by rw [integral_const_mul,shifted_mass (by positivity : 0 < 8*t) x,mul_one]

def lipConstant (t M : ℝ) : ℝ := (localConstant+2)*M/Real.sqrt t

theorem lipConstant_nonneg {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M) : 0 ≤ lipConstant t M := by
  unfold lipConstant
  exact div_nonneg (mul_nonneg (by linarith [localConstant_pos]) hM) (Real.sqrt_nonneg t)

/-- Actual bounded Fourier heat evolution has a continuous
representative with the correct global inverse-square-root Lipschitz gain. -/
theorem difference_bound {t : ℝ} (ht : 0 < t) (f : CircleL2) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ᵐ y ∂haarAddCircle,‖f y‖ ≤ M) (x w : AddCircle (1:ℝ)) :
    ‖value t ht f x-value t ht f w‖ ≤ lipConstant t M*dist x w := by
  by_cases hnear : dist x w ≤ Real.sqrt t
  · apply (local_difference ht f hM hf x w hnear).trans
    have hC : (localConstant/Real.sqrt t)*M ≤ lipConstant t M := by
      unfold lipConstant
      have hh : localConstant*M ≤ (localConstant+2)*M := by nlinarith
      have hm := div_le_div_of_nonneg_right hh (Real.sqrt_nonneg t)
      simpa only [div_mul_eq_mul_div] using hm
    exact mul_le_mul_of_nonneg_right hC dist_nonneg
  · have hnorm : ‖value t ht f x-value t ht f w‖ ≤ 2*M :=
      (norm_sub_le _ _).trans (by linarith [norm_bound ht f hf x,norm_bound ht f hf w])
    apply hnorm.trans
    have hspos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    unfold lipConstant
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hspos).mpr
    have hr : Real.sqrt t ≤ dist x w := (le_of_not_ge hnear)
    have hc : 2*M ≤ (localConstant+2)*M := by nlinarith [localConstant_pos]
    exact (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2*M)).trans
      (mul_le_mul_of_nonneg_right hc dist_nonneg)

theorem lipschitzWith {t : ℝ} (ht : 0 < t) (f : CircleL2) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ᵐ y ∂haarAddCircle,‖f y‖ ≤ M) :
    LipschitzWith (Real.nnabs (lipConstant t M)) (value t ht f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x w
  simpa only [dist_eq_norm,Real.coe_nnabs,abs_of_nonneg (lipConstant_nonneg ht hM)] using
    difference_bound ht f hM hf x w

def representative {t : ℝ} (ht : 0 < t) (f : CircleL2) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ᵐ y ∂haarAddCircle,‖f y‖ ≤ M) : C(AddCircle (1:ℝ),ℂ) :=
  ⟨value t ht f,(lipschitzWith ht f hM hf).continuous⟩

theorem representative_ae {t : ℝ} (ht : 0 < t) (f : CircleL2) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ᵐ y ∂haarAddCircle,‖f y‖ ≤ M) :
    representative ht f M hM hf =ᵐ[haarAddCircle] heat t f := (heat_convolution_ae ht f).symm

end SHE.BoundedHeat
