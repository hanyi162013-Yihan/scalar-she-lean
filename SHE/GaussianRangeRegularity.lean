module

public import SHE.GaussianRangeJetBounds

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianRangeSmooth
open MeasureTheory ProbabilityTheory GaussianIncrement GaussianTaylor MeasurableGeneralizedInverse
open scoped InnerProductSpace
variable {n : ℕ}

theorem extension_gradient_bound {A : Mat n} (hA : A.PosSemidef)
    (F : State n → ℝ) (hF : Measurable F) {M : ℝ} (hM : ∀ y, |F y| ≤ M) (z : State n) :
    ‖fderiv ℝ (roughAverageExtension A F) z‖ ≤ M * extensionJetConstant A 1 := by
  simpa only [norm_iteratedFDeriv_one] using norm_extension_jet hA F hF hM 1 z

theorem extension_hessian_bound {A : Mat n} (hA : A.PosSemidef)
    (F : State n → ℝ) (hF : Measurable F) {M : ℝ} (hM : ∀ y, |F y| ≤ M) (z : State n) :
    ‖hessian (roughAverageExtension A F) z‖ ≤ M * extensionJetConstant A 2 := by
  have he : ‖hessian (roughAverageExtension A F) z‖ =
      ‖iteratedFDeriv ℝ 2 (roughAverageExtension A F) z‖ := by
    change ‖fderiv ℝ (fderiv ℝ (roughAverageExtension A F)) z‖ = _
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  rw [he]
  exact norm_extension_jet hA F hF hM 2 z

theorem extension_hessian_lipschitz {A : Mat n} (hA : A.PosSemidef)
    (F : State n → ℝ) (hF : Measurable F) {M : ℝ} (hM : ∀ y, |F y| ≤ M) (z w : State n) :
    ‖hessian (roughAverageExtension A F) w - hessian (roughAverageExtension A F) z‖ ≤
      (M * extensionJetConstant A 3) * ‖w - z‖ := by
  let : NormedAddCommGroup (State n →L[ℝ] State n →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (State n →L[ℝ] State n →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (State n →L[ℝ] State n →L[ℝ] State n →L[ℝ] ℝ) := inferInstance
  have hc := contDiff_roughAverageExtension hA F hF M hM 3
  have hcH : ContDiff ℝ 1 (hessian (roughAverageExtension A F)) :=
    (hc.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).fderiv_right
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := Set.univ) (fun x _ => hcH.differentiable (by norm_num) x)
    _ convex_univ (Set.mem_univ z) (Set.mem_univ w)
  intro x _
  have he : ‖fderiv ℝ (hessian (roughAverageExtension A F)) x‖ =
      ‖iteratedFDeriv ℝ 3 (roughAverageExtension A F) x‖ := by
    change ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (roughAverageExtension A F))) x‖ = _
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
  rw [he]
  exact norm_extension_jet hA F hF hM 3 x

/-- All regularity and uniform derivative premises of the existing
Gaussian covariance differentiation theorem hold for the constructed
range extension of a bounded Borel test. -/
theorem extension_covariance_regularity {A : Mat n} (hA : A.PosSemidef)
    (F : State n → ℝ) (hF : Measurable F) {M : ℝ} (hM : ∀ y, |F y| ≤ M) :
    ContDiff ℝ 2 (roughAverageExtension A F) ∧
      (∀ z, ‖roughAverageExtension A F z‖ ≤ M) ∧
      (∀ z, ‖fderiv ℝ (roughAverageExtension A F) z‖ ≤ M * extensionJetConstant A 1) ∧
      (∀ z, ‖hessian (roughAverageExtension A F) z‖ ≤ M * extensionJetConstant A 2) ∧
      0 ≤ M * extensionJetConstant A 3 ∧
      (∀ z w, ‖hessian (roughAverageExtension A F) w - hessian (roughAverageExtension A F) z‖ ≤
        (M * extensionJetConstant A 3) * ‖w - z‖) := by
  have hM0 : 0 ≤ M := (abs_nonneg (F 0)).trans (hM 0)
  exact ⟨contDiff_roughAverageExtension hA F hF M hM 2,
    fun z => extension_bound A F M hM z,
    extension_gradient_bound hA F hF hM, extension_hessian_bound hA F hF hM,
    mul_nonneg hM0 (extensionJetConstant_nonneg A 3), extension_hessian_lipschitz hA F hF hM⟩

end SHE.GaussianRangeSmooth
