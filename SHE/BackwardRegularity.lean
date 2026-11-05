module

public import SHE.GaussianBackward
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

@[expose] public section
set_option autoImplicit false

/-! The actual regularity needed when applying finite-dimensional Itô to
the backward Gaussian test, including terminally singular covariance. -/
noncomputable section
namespace SHE.BackwardRegularity
open Set MeasureTheory ProbabilityTheory Filter
open GaussianIncrement GaussianTaylor GaussianTaylorAverage GaussianConvolution GaussianContinuity GaussianCovariancePath

theorem absolutelyContinuous_of_dist_domination {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : ℝ → Y} {a b C : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hdom : ∀ u ∈ uIcc a b, ∀ v ∈ uIcc a b, dist (f u) (f v) ≤ C * dist (g u) (g v)) :
    AbsolutelyContinuousOnInterval f a b := by
  apply squeeze_zero' ?_ ?_ (by simpa using Tendsto.const_mul C hg)
  · exact Eventually.of_forall (fun _ => by positivity)
  rw [eventually_inf_principal]
  filter_upwards with E hE
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => hdom _ (hE.left i hi).left _ (hE.left i hi).right)

theorem gaussian_time_absolutelyContinuous {n : ℕ} (C : ℝ → PositiveCovariance n)
    (horder : ∀ u v, u ≤ v → ((C u).val - (C v).val).PosSemidef)
    {a b : ℝ} (htrace : AbsolutelyContinuousOnInterval (fun t => (C t).val.trace) a b)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hB : 0 ≤ B) (z : State n) :
    AbsolutelyContinuousOnInterval (fun t => gaussianAverage (C t).val F z) a b := by
  apply absolutelyContinuous_of_dist_domination htrace
  intro u _ v _
  have hh := ordered_covariance_lipschitz (C u).property (C v).property
    (by rcases le_total u v with huv | hvu
        · exact Or.inl (horder u v huv)
        · exact Or.inr (horder v u hvu)) hF hbound hD hDD hB z
  simpa only [Real.dist_eq, Real.norm_eq_abs] using hh

theorem gaussian_state_contDiff_two {n : ℕ} (A : Mat n) {F : State n → ℝ}
    (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) : ContDiff ℝ 2 (gaussianAverage A F) :=
  GaussianSmooth.contDiff_average_two (multivariateGaussian 0 A) hF hbound hD hDD

theorem gaussian_state_gradient_bound {n : ℕ} (A : Mat n) {F : State n → ℝ}
    (hF : ContDiff ℝ 2 F) {M L : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L) (z : State n) :
    ‖fderiv ℝ (gaussianAverage A F) z‖ ≤ L :=
  GaussianSmooth.average_fderiv_bound (multivariateGaussian 0 A) (hF.of_le (by norm_num)) hbound hD z

theorem gaussian_state_hessian_bound {n : ℕ} (A : Mat n) {F : State n → ℝ}
    (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (z : State n) :
    ‖hessian (gaussianAverage A F) z‖ ≤ B :=
  GaussianSmooth.average_hessian_bound (multivariateGaussian 0 A) hF hbound hD hDD z

theorem gaussian_gradient_joint_continuous {n : ℕ} (C : ℝ → PositiveCovariance n)
    (hC : Continuous C) {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L) :
    Continuous (fun p : ℝ × State n => fderiv ℝ (gaussianAverage (C p.1).val F) p.2) := by
  have hc := hF.continuous_fderiv (by norm_num)
  have hm := (continuous_gaussian_average (n := n) (fderiv ℝ F) hc hD).comp
    ((hC.comp continuous_fst).prodMk continuous_snd)
  have heq : (fun p : ℝ × State n => fderiv ℝ (gaussianAverage (C p.1).val F) p.2) =
      fun p => ∫ y : State n, fderiv ℝ F (p.2 + y) ∂multivariateGaussian 0 (C p.1).val := by
    funext p
    rw [show gaussianAverage (C p.1).val F = GaussianSmooth.average (multivariateGaussian 0 (C p.1).val) F from rfl,
      GaussianSmooth.fderiv_average _ (hF.of_le (by norm_num)) hbound hD]
  rw [heq]
  exact hm

theorem gaussian_hessian_joint_continuous {n : ℕ} (C : ℝ → PositiveCovariance n)
    (hC : Continuous C) {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) :
    Continuous (fun p : ℝ × State n => hessian (gaussianAverage (C p.1).val F) p.2) := by
  have hc : Continuous (hessian F) := (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
  have hm := (continuous_gaussian_average (n := n) (hessian F) hc hDD).comp
    ((hC.comp continuous_fst).prodMk continuous_snd)
  have heq : (fun p : ℝ × State n => hessian (gaussianAverage (C p.1).val F) p.2) =
      fun p => ∫ y : State n, hessian F (p.2 + y) ∂multivariateGaussian 0 (C p.1).val := by
    funext p
    unfold hessian
    rw [show gaussianAverage (C p.1).val F = GaussianSmooth.average (multivariateGaussian 0 (C p.1).val) F from rfl,
      GaussianSmooth.fderiv_fderiv_average _ hF hbound hD hDD]
    rfl
  rw [heq]
  exact hm

theorem observation_trace_lipschitz {n : ℕ} (W : ClippedCovariance.ObservationWindow n) :
    LipschitzWith ⟨(n : ℝ) * W.upper * CovarianceMatrix.heatRowBound W.gap ^ 2,
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) W.upper_nonneg) (sq_nonneg _)⟩
      (fun t => (W.path t).val.trace) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change |(W.path u).val.trace - (W.path v).val.trace| ≤
    ((n : ℝ) * W.upper * CovarianceMatrix.heatRowBound W.gap ^ 2) * |u - v|
  have hb (s t : ℝ) (hst : s ≤ t) : |(W.path s).val.trace - (W.path t).val.trace| ≤
      ((n : ℝ) * W.upper * CovarianceMatrix.heatRowBound W.gap ^ 2) * |s - t| := by
    have hn : 0 ≤ (W.path s).val.trace - (W.path t).val.trace := by
      simpa only [Matrix.trace_sub] using (W.path_antitone hst).trace_nonneg
    rw [abs_of_nonneg hn, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
    simpa only [Matrix.trace_sub] using W.path_increment_trace_bound hst
  rcases le_total u v with huv | hvu
  · simpa only [Real.dist_eq, NNReal.coe_mk] using hb u v huv
  · simpa only [Real.dist_eq, NNReal.coe_mk, abs_sub_comm] using hb v u hvu

theorem observation_trace_absolutelyContinuous {n : ℕ} (W : ClippedCovariance.ObservationWindow n) :
    AbsolutelyContinuousOnInterval (fun t => (W.path t).val.trace) W.left W.right :=
  (observation_trace_lipschitz W).lipschitzOnWith.absolutelyContinuousOnInterval

theorem observation_test_time_absolutelyContinuous {n : ℕ} (W : ClippedCovariance.ObservationWindow n)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hB : 0 ≤ B) (z : State n) :
    AbsolutelyContinuousOnInterval (fun t => gaussianAverage (W.path t).val F z) W.left W.right :=
  gaussian_time_absolutelyContinuous W.path (fun u v huv => W.path_antitone huv)
    (observation_trace_absolutelyContinuous W) hF hbound hD hDD hB z

end SHE.BackwardRegularity
