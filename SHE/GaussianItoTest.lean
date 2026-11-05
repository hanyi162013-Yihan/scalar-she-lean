module

public import SHE.BackwardRegularity
public import SHE.CovarianceEndpointPath

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-! Complete deterministic regularity of the actual backward Gaussian test.
Terminal heat ages may vanish and the observation covariance may be singular. -/
noncomputable section
namespace SHE.GaussianItoTest
open Set MeasureTheory ProbabilityTheory Filter StoppedFourier
open GaussianIncrement GaussianTaylor GaussianTaylorAverage GaussianConvolution
open GaussianCovariancePath GaussianContinuity BackwardRegularity CovarianceMatrix
open CovarianceEndpoint
open scoped Matrix.Norms.Elementwise

abbrev State (n : ℕ) := WordRecursion.State n

/-- The deterministic hypotheses for the ordinary finite-dimensional Itô
formula. The time derivative is an actual almost-everywhere derivative;
its uniform integrable envelope permits terminal heat singularities. -/
structure RegularTest {n : ℕ} (a b : ℝ) (G dG : ℝ → State n → ℝ) : Prop where
  continuous : Continuous (fun p : ℝ × State n => G p.1 p.2)
  state_smooth : ∀ t, ContDiff ℝ 2 (G t)
  gradient_continuous : Continuous (fun p : ℝ × State n => fderiv ℝ (G p.1) p.2)
  hessian_continuous : Continuous (fun p : ℝ × State n => hessian (G p.1) p.2)
  time_absolutelyContinuous : ∀ z, AbsolutelyContinuousOnInterval (fun t => G t z) a b
  time_derivative : ∀ᵐ t : ℝ, t ∈ Ioo a b → ∀ z, HasDerivAt (fun u => G u z) (dG t z) t
  derivative_measurable : Measurable (fun p : ℝ × State n => dG p.1 p.2)
  derivative_state_continuous : ∀ t, Continuous (dG t)
  derivative_envelope : ∃ v : ℝ → ℝ, IntervalIntegrable v volume a b ∧
    ∀ t ∈ Ioo a b, ∀ z, ‖dG t z‖ ≤ v t
  bounds : ∃ M L B : ℝ, ∀ t z, ‖G t z‖ ≤ M ∧
    ‖fderiv ℝ (G t) z‖ ≤ L ∧ ‖hessian (G t) z‖ ≤ B

def backward {n : ℕ} (W : EndpointWindow n) (F : State n → ℝ) (t : ℝ) : State n → ℝ :=
  gaussianAverage (W.path t).val F

def backwardDerivative {n : ℕ} (W : EndpointWindow n) (F : State n → ℝ)
    (t : ℝ) (z : State n) : ℝ :=
  -(1 / 2 : ℝ) * covarianceAction (densityMatrix W.coefficient W.observations t)
    (hessian (backward W F t) z)

theorem action_entry_bound {n : ℕ} (A : Mat n) (H : State n →L[ℝ] State n →L[ℝ] ℝ)
    {P : ℝ} (hP : 0 ≤ P) (hA : ∀ i j, |A i j| ≤ P) :
    ‖covarianceAction A H‖ ≤ (n : ℝ)^2 * P * ‖H‖ := by
  unfold covarianceAction
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖A i j *
        H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, P * ‖H‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hA i j) (PositiveMatrixBounds.bilinear_basis_bound H i j) (norm_nonneg _) hP
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem backwardDerivative_measurable {n : ℕ} (W : EndpointWindow n)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) :
    Measurable (fun p : ℝ × State n => backwardDerivative W F p.1 p.2) := by
  have hH := gaussian_hessian_joint_continuous W.path W.continuous_path hF hbound hD hDD
  apply Measurable.const_mul
  unfold covarianceAction
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact ((covarianceDensity_measurable W.coefficient W.measurable W.observations i j).comp measurable_fst).mul
    (((hH.clm_apply continuous_const).clm_apply continuous_const).measurable)

theorem backwardDerivative_bound {n : ℕ} (W : EndpointWindow n)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hB : 0 ≤ B)
    {t : ℝ} (ht : t ∈ Ioo W.left W.right) (z : State n) :
    ‖backwardDerivative W F t z‖ ≤
      (1 / 2 : ℝ) * (n : ℝ)^2 * B *
        (W.upper * (1 + heatConstant * (W.right - t)^(-(1 / 2 : ℝ)))) := by
  have hP : 0 ≤ W.upper * (1 + heatConstant * (W.right - t)^(-(1 / 2 : ℝ))) := by
    apply mul_nonneg W.upper_nonneg
    exact add_nonneg zero_le_one (mul_nonneg heatConstant_pos.le
      (Real.rpow_pos_of_pos (sub_pos.mpr ht.2) _).le)
  have hb := action_entry_bound (densityMatrix W.coefficient W.observations t)
    (hessian (backward W F t) z) hP (fun i j =>
      covarianceDensity_endpoint_bound W.coefficient W.measurable W.observations W.upper_nonneg
        ht.2 W.target_after (W.bounded t (Ioo_subset_Icc_self ht)) i j)
  have hh : ‖hessian (backward W F t) z‖ ≤ B :=
    gaussian_state_hessian_bound (W.path t).val hF hbound hD hDD z
  unfold backwardDerivative
  rw [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  apply (mul_le_mul_of_nonneg_left hb (by norm_num)).trans
  have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (mul_nonneg (sq_nonneg (n : ℝ)) hP))
  nlinarith only [hh']

theorem backward_regular {n : ℕ} (W : EndpointWindow n)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖) :
    RegularTest W.left W.right (backward W F) (backwardDerivative W F) := by
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
    exact gaussian_time_absolutelyContinuous W.path (fun _ _ huv => W.path_antitone huv)
      W.path_trace_absolutelyContinuous hF hbound hD hDD hB z
  · filter_upwards [W.path_ae_hasDerivAt] with t ht
    intro htin z
    have hd := hasDerivAt_monotone_gaussian_average W.path (ht htin)
      (fun _ _ huv => W.path_antitone huv) hF hbound hD hDD hK hH z
    rw [GaussianBackward.covarianceAction_neg, mul_neg] at hd
    change HasDerivAt (fun u => gaussianAverage (W.path u).val F z)
      (-(1 / 2 : ℝ) * covarianceAction (densityMatrix W.coefficient W.observations t)
        (hessian (gaussianAverage (W.path t).val F) z)) t
    convert hd using 1 <;> ring
  · exact backwardDerivative_measurable W hF hbound hD hDD
  · intro t
    have hH := (gaussian_hessian_joint_continuous W.path W.continuous_path hF hbound hD hDD).comp
      ((continuous_const (y := t)).prodMk (continuous_id : Continuous (fun z : State n => z)))
    unfold backwardDerivative covarianceAction
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul ((hH.clm_apply continuous_const).clm_apply continuous_const)
  · refine ⟨fun t => (1 / 2 : ℝ) * (n : ℝ)^2 * B *
        (W.upper * (1 + heatConstant * (W.right - t)^(-(1 / 2 : ℝ)))), ?_, ?_⟩
    · exact (endpoint_majorant_integrable W.upper).const_mul _
    · exact fun t ht z => backwardDerivative_bound W hF hbound hD hDD hB ht z
  · exact ⟨M, L, B, fun t z => ⟨GaussianSmooth.average_norm_bound _ hbound z,
      gaussian_state_gradient_bound _ hF hbound hD z,
      gaussian_state_hessian_bound _ hF hbound hD hDD z⟩⟩

end SHE.GaussianItoTest
