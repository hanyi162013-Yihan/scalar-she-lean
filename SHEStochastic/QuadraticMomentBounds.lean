module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.QuadraticMomentBounds
open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
local instance : ENNReal.HolderTriple 4 4 2 := ⟨by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have ht : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
  rw [show (4 : ℝ≥0∞) = 2*2 from by norm_num,
    ENNReal.mul_inv (Or.inl h2) (Or.inl ht), ← two_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel h2 ht, one_mul]⟩

theorem fourth_integrable {f : Ω → ℝ} (hf : MemLp f 4 μ) :
    Integrable (fun sample ↦ f sample^4) μ :=
  (hf.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)).mono'
    (hf.aestronglyMeasurable.pow 4) (Filter.Eventually.of_forall fun sample ↦ by rw [norm_pow])

theorem product_memLp {f g : Ω → ℝ} (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    MemLp (fun sample ↦ f sample*g sample) 2 μ := hf.mul hg

theorem product_sub_memLp {f g A : Ω → ℝ} (hf : MemLp f 4 μ) (hg : MemLp g 4 μ)
    (hA : AEStronglyMeasurable A μ) (K : ℝ) (hb : ∀ sample, ‖A sample‖ ≤ K) :
    MemLp (fun sample ↦ f sample*g sample-A sample) 2 μ :=
  (hf.mul hg).sub (MemLp.of_bound hA K (Filter.Eventually.of_forall hb))

/-- Fourth moments of two processes control the second moment of
their product minus any bounded compensator. No independence of the
two processes is required. Taking g=f covers square compensators. -/
theorem product_sub_bounded {f g A : Ω → ℝ} (hf : MemLp f 4 μ) (hg : MemLp g 4 μ)
    (hA : AEStronglyMeasurable A μ) (K : ℝ) (hb : ∀ sample, ‖A sample‖ ≤ K)
    (Cf Cg : ℝ) (hCf : (∫ sample, f sample^4 ∂μ) ≤ Cf)
    (hCg : (∫ sample, g sample^4 ∂μ) ≤ Cg) :
    MemLp (fun sample ↦ f sample*g sample-A sample) 2 μ ∧
      (∫ sample, (f sample*g sample-A sample)^2 ∂μ) ≤ Cf+Cg+2*K^2 := by
  have hAm : MemLp A 2 μ := MemLp.of_bound hA K (Filter.Eventually.of_forall hb)
  have hm : MemLp (fun sample ↦ f sample*g sample-A sample) 2 μ := (hf.mul hg).sub hAm
  have hiF := fourth_integrable μ hf
  have hiG := fourth_integrable μ hg
  refine ⟨hm, ?_⟩
  calc
    _ ≤ ∫ sample, (f sample^4+g sample^4)+2*K^2 ∂μ := by
      apply integral_mono hm.integrable_sq ((hiF.add hiG).add (integrable_const _))
      intro sample
      change (f sample*g sample-A sample)^2 ≤ f sample^4+g sample^4+2*K^2
      have hAsq : A sample^2 ≤ K^2 := by
        simpa only [Real.norm_eq_abs, sq_abs] using
          pow_le_pow_left₀ (norm_nonneg _) (hb sample) 2
      nlinarith [sq_nonneg (f sample*g sample+A sample), sq_nonneg (f sample^2-g sample^2)]
    _ = ((∫ sample, f sample^4 ∂μ)+(∫ sample, g sample^4 ∂μ))+2*K^2 := by
      have he := (integral_add (hiF.add hiG) (integrable_const (2*K^2))).trans
        (congrArg (fun z : ℝ ↦ z+(∫ _ : Ω, 2*K^2 ∂μ)) (integral_add hiF hiG))
      simpa only [Pi.add_apply, integral_const, probReal_univ, smul_eq_mul, one_mul] using he
    _ ≤ _ := by linarith

end SHEStochastic.QuadraticMomentBounds
