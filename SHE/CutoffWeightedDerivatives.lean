module

public import SHE.CutoffUncutComparison

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.CutoffWeightedDerivatives
open Set MeasureTheory StoppedFourier WordRecursion
open CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffUncutComparison NormalizedInsertion
open Classical

theorem norm_hessian_smul_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ℝ) (F : E→ℝ) (z : E) :
    ‖GaussianTaylor.hessian (w • F) z‖≤|w| * ‖GaussianTaylor.hessian F z‖ := by
  rw [congrFun (NormalizedInsertion.hessian_smul w F) z]
  exact ContinuousLinearMap.opNorm_smul_le w (GaussianTaylor.hessian F z)

variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

theorem fderiv_bound (k : ℕ) : ∃ D : ℝ, 0≤D ∧
    ∀ (δ : ℝ) (hδ : 0<δ) p z,
      ‖fderiv ℝ ((RecursiveHeatBounds.level L δ hδ 0 k).test p) z‖≤
        D*UncutSmoothWords.weight L k p := by
  obtain ⟨D,hDn,hD⟩ := (UncutSmoothWords.normalized_uniform L k).fderiv.norm_bound
  refine ⟨D,hDn,fun δ hδ p z => ?_⟩
  rw [test_eq_active L hδ k p]
  by_cases hp : Active L δ k p
  · rw [if_pos hp,UncutSmoothWords.test_eq_weight_normalized,fderiv_const_smul_field]
    simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (UncutSmoothWords.weight_nonneg L k p)]
    nlinarith [hD p z,UncutSmoothWords.weight_nonneg L k p]
  · rw [if_neg hp,fderiv_zero]
    simp only [Pi.zero_apply,norm_zero]
    exact mul_nonneg hDn (UncutSmoothWords.weight_nonneg L k p)

/-- A uniform Hessian bound for the genuinely δ-dependent recursive
test, with its integrable uncut history weight explicitly retained. -/
theorem hessian_bound (k : ℕ) : ∃ B : ℝ, 0≤B ∧
    ∀ (δ : ℝ) (hδ : 0<δ) p z,
      ‖GaussianTaylor.hessian ((RecursiveHeatBounds.level L δ hδ 0 k).test p) z‖≤
        B*UncutSmoothWords.weight L k p := by
  obtain ⟨B,hBn,hB⟩ := (UncutSmoothWords.normalized_uniform L k).fderiv.fderiv.norm_bound
  refine ⟨B,hBn,fun δ hδ p z => ?_⟩
  rw [test_eq_active L hδ k p]
  by_cases hp : Active L δ k p
  · rw [if_pos hp,UncutSmoothWords.test_eq_weight_normalized]
    have hh := norm_hessian_smul_le (UncutSmoothWords.weight L k p) (UncutSmoothWords.normalized L k p) z
    rw [abs_of_nonneg (UncutSmoothWords.weight_nonneg L k p)] at hh
    have hb : ‖GaussianTaylor.hessian (UncutSmoothWords.normalized L k p) z‖≤B := hB p z
    exact hh.trans ((mul_le_mul_of_nonneg_left hb (UncutSmoothWords.weight_nonneg L k p)).trans_eq (mul_comm _ _))
  · rw [if_neg hp]
    have hh := norm_hessian_smul_le 0 (UncutSmoothWords.normalized L k p) z
    simp only [zero_smul,abs_zero,zero_mul] at hh
    exact hh.trans (mul_nonneg hBn (UncutSmoothWords.weight_nonneg L k p))

end SHE.CutoffWeightedDerivatives
