module

public import SHE.BackwardRegularity
public import SHE.GaussianMovingMean

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.GaussianTimeLipschitz
open MeasureTheory Set GaussianIncrement GaussianConvolution GaussianContinuity
open GaussianTaylor GaussianCovariancePath BackwardRegularity
open scoped MatrixOrder NNReal ENNReal

theorem mean_lipschitz {n : ℕ} (A : Mat n) {F : State n→ℝ}
    (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z,‖F z‖≤M) (hD : ∀ z,‖fderiv ℝ F z‖≤L)
    (hDD : ∀ z,‖hessian F z‖≤B) (hL : 0≤L) :
    LipschitzWith ⟨L,hL⟩ (gaussianAverage A F) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm,dist_eq_norm]
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (GaussianSmooth.contDiff_average_two (ProbabilityTheory.multivariateGaussian 0 A)
      hF hbound hD hDD).differentiable (by norm_num) x)
    (fun x _ => gaussian_state_gradient_bound A hF hbound hD x)
    convex_univ (mem_univ w) (mem_univ z)

/-- Ordered covariance variation and a moving mean give an actual time
Lipschitz bound for the Gaussian reserve, including singular laws. -/
theorem value_lipschitz {n : ℕ} (C : ℝ→PositiveCovariance n)
    (horder : ∀ u v,u≤v → ((C u).val-(C v).val).PosSemidef)
    (Kc : ℝ≥0) (htrace : LipschitzWith Kc (fun t => (C t).val.trace))
    (m : ℝ→State n) (Km : ℝ≥0) (hm : LipschitzWith Km m)
    {F : State n→ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z,‖F z‖≤M) (hD : ∀ z,‖fderiv ℝ F z‖≤L)
    (hDD : ∀ z,‖hessian F z‖≤B) (hL : 0≤L) (hB : 0≤B) :
    LipschitzWith ⟨L*(Km:ℝ)+B*(Kc:ℝ),by positivity⟩
      (fun t => gaussianAverage (C t).val F (m t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hord : ((C u).val-(C v).val).PosSemidef ∨ ((C v).val-(C u).val).PosSemidef := by
    rcases le_total u v with h|h
    · exact Or.inl (horder u v h)
    · exact Or.inr (horder v u h)
  have hc := ordered_covariance_lipschitz (C u).property (C v).property hord hF hbound hD hDD hB (m v)
  have hmean := (mean_lipschitz (C u).val hF hbound hD hDD hL).dist_le_mul (m u) (m v)
  rw [dist_eq_norm] at hmean
  have hc' : ‖gaussianAverage (C u).val F (m v)-gaussianAverage (C v).val F (m v)‖≤
      B*((Kc:ℝ)*dist u v) := hc.trans (mul_le_mul_of_nonneg_left (htrace.dist_le_mul u v) hB)
  rw [dist_eq_norm]
  calc
    _≤‖gaussianAverage (C u).val F (m u)-gaussianAverage (C u).val F (m v)‖+
      ‖gaussianAverage (C u).val F (m v)-gaussianAverage (C v).val F (m v)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤L*((Km:ℝ)*dist u v)+B*((Kc:ℝ)*dist u v) :=
      add_le_add (hmean.trans (mul_le_mul_of_nonneg_left (hm.dist_le_mul u v) hL)) hc'
    _=_ := by
      change L*((Km:ℝ)*dist u v)+B*((Kc:ℝ)*dist u v)=(L*(Km:ℝ)+B*(Kc:ℝ))*dist u v
      ring

end SHE.GaussianTimeLipschitz
