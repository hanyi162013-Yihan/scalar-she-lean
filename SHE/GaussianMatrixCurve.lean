module

public import SHE.GaussianItoTest
public import SHE.SmoothWords

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SHE.GaussianMatrixCurve
open Set MeasureTheory ProbabilityTheory Filter
open GaussianTaylor GaussianTaylorAverage GaussianContinuity GaussianCovariancePath GaussianConvolution
open BackwardRegularity GaussianItoTest
open scoped Matrix.Norms.Elementwise

abbrev State (n : ℕ) := WordRecursion.State n

/-- A finite deterministic covariance curve and its actual bracket density.
These are deterministic analytic data, rather than a Gaussian law premise. -/
structure Curve (n : ℕ) where
  left : ℝ
  right : ℝ
  ordered : left ≤ right
  path : ℝ → PositiveCovariance n
  continuous_path : Continuous path
  path_order : ∀ u v, u ≤ v → ((path u).val - (path v).val).PosSemidef
  trace_ac : AbsolutelyContinuousOnInterval (fun t => (path t).val.trace) left right
  density : ℝ → Mat n
  density_measurable : Measurable density
  path_derivative : ∀ᵐ q : ℝ, q ∈ Ioo left right →
    HasDerivAt (fun t => (path t).val) (-density q) q
  envelope : ℝ → ℝ
  envelope_integrable : IntervalIntegrable envelope volume left right
  envelope_nonneg : ∀ t ∈ Ioo left right, 0 ≤ envelope t
  density_bound : ∀ t ∈ Ioo left right, ∀ i j, |density t i j| ≤ envelope t
  terminal : (path right).val = 0

def backward {n : ℕ} (W : Curve n) (F : State n → ℝ) (t : ℝ) : State n → ℝ :=
  gaussianAverage (W.path t).val F

def timeDerivative {n : ℕ} (W : Curve n) (F : State n → ℝ)
    (t : ℝ) (z : State n) : ℝ :=
  -(1 / 2 : ℝ) * covarianceAction (W.density t) (hessian (backward W F t) z)

theorem backward_terminal {n : ℕ} (W : Curve n) (F : State n → ℝ) :
    backward W F W.right = F := by
  funext z
  simp only [backward, W.terminal, gaussianAverage,
    CovarianceMatrix.multivariateGaussian_zero_covariance, integral_dirac, add_zero]

theorem boundedSmooth {n : ℕ} (W : Curve n) {F : State n → ℝ}
    (hF : SmoothCylinders.BoundedSmooth F) (t : ℝ) :
    SmoothCylinders.BoundedSmooth (backward W F t) :=
  SmoothCylinders.BoundedSmooth.average (multivariateGaussian 0 (W.path t).val) hF

theorem derivative_measurable {n : ℕ} (W : Curve n)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) :
    Measurable (fun p : ℝ × State n => timeDerivative W F p.1 p.2) := by
  have hH := gaussian_hessian_joint_continuous W.path W.continuous_path hF hbound hD hDD
  apply Measurable.const_mul
  unfold covarianceAction
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp W.density_measurable)).comp measurable_fst).mul
    (((hH.clm_apply continuous_const).clm_apply continuous_const).measurable)

theorem derivative_bound {n : ℕ} (W : Curve n)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B)
    {t : ℝ} (ht : t ∈ Ioo W.left W.right) (z : State n) :
    ‖timeDerivative W F t z‖ ≤ (1 / 2 : ℝ) * (n : ℝ)^2 * B * W.envelope t := by
  have hb := action_entry_bound (W.density t) (hessian (backward W F t) z)
    (W.envelope_nonneg t ht) (W.density_bound t ht)
  have hh : ‖hessian (backward W F t) z‖ ≤ B :=
    gaussian_state_hessian_bound (W.path t).val hF hbound hD hDD z
  unfold timeDerivative
  rw [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  apply (mul_le_mul_of_nonneg_left hb (by norm_num)).trans
  have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (mul_nonneg (sq_nonneg (n : ℝ)) (W.envelope_nonneg t ht)))
  nlinarith only [hh']

theorem regular {n : ℕ} (W : Curve n)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖) :
    RegularTest W.left W.right (backward W F) (timeDerivative W F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc := continuous_gaussian_average (n := n) F hF.continuous hbound
    have hp : Continuous (fun p : ℝ × State n => (W.path p.1, p.2)) :=
      (W.continuous_path.comp continuous_fst).prodMk continuous_snd
    have hh := hc.comp hp
    change Continuous (fun p : ℝ × State n => ∫ y : State n, F (p.2 + y) ∂multivariateGaussian 0 (W.path p.1).val)
    exact hh
  · intro t
    exact gaussian_state_contDiff_two _ hF hbound hD hDD
  · exact gaussian_gradient_joint_continuous W.path W.continuous_path hF hbound hD
  · exact gaussian_hessian_joint_continuous W.path W.continuous_path hF hbound hD hDD
  · intro z
    exact gaussian_time_absolutelyContinuous W.path W.path_order W.trace_ac
      hF hbound hD hDD hB z
  · filter_upwards [W.path_derivative] with t ht
    intro htin z
    have hd := hasDerivAt_monotone_gaussian_average W.path (ht htin)
      W.path_order hF hbound hD hDD hK hH z
    rw [GaussianBackward.covarianceAction_neg, mul_neg] at hd
    change HasDerivAt (fun u => gaussianAverage (W.path u).val F z)
      (-(1 / 2 : ℝ) * covarianceAction (W.density t)
        (hessian (gaussianAverage (W.path t).val F) z)) t
    convert hd using 1 <;> ring
  · exact derivative_measurable W hF hbound hD hDD
  · intro t
    have hH := (gaussian_hessian_joint_continuous W.path W.continuous_path hF hbound hD hDD).comp
      ((continuous_const (y := t)).prodMk (continuous_id : Continuous (fun z : State n => z)))
    unfold timeDerivative covarianceAction
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul ((hH.clm_apply continuous_const).clm_apply continuous_const)
  · refine ⟨fun t => (1 / 2 : ℝ) * (n : ℝ)^2 * B * W.envelope t,
      W.envelope_integrable.const_mul _, ?_⟩
    exact fun t ht z => derivative_bound W hF hbound hD hDD ht z
  · exact ⟨M, L, B, fun t z => ⟨GaussianSmooth.average_norm_bound _ hbound z,
      gaussian_state_gradient_bound _ hF hbound hD z,
      gaussian_state_hessian_bound _ hF hbound hD hDD z⟩⟩

theorem regular_boundedSmooth {n : ℕ} (W : Curve n) {F : State n → ℝ}
    (hF : SmoothCylinders.BoundedSmooth F) :
    RegularTest W.left W.right (backward W F) (timeDerivative W F) := by
  obtain ⟨M, hM⟩ := hF.norm_bound
  obtain ⟨L, hL⟩ := hF.fderiv.norm_bound
  obtain ⟨B, hB⟩ := hF.hessian_norm_bound
  obtain ⟨K, hKn, hK⟩ := hF.hessian_lipschitz
  exact regular W (hF.smooth.of_le (by simp)) hM hL hB
    ((norm_nonneg (hessian F 0)).trans (hB 0)) hKn hK

end SHE.GaussianMatrixCurve
