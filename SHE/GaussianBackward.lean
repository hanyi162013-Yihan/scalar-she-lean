module

public import SHE.GaussianCovariancePath
public import SHE.ClippedCovariance

@[expose] public section
set_option autoImplicit false

/-! The actual backward Gaussian equation for physical heat observations.
Only the finite-dimensional Itô formula will remain a stochastic input. -/
noncomputable section
namespace SHE.GaussianBackward
open Set MeasureTheory ProbabilityTheory Filter AddCircle StoppedFourier
open GaussianIncrement GaussianTaylor GaussianTaylorAverage GaussianConvolution GaussianCovariancePath
open WordRecursion CovarianceMatrix ClippedCovariance
open scoped Matrix.Norms.Elementwise

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
abbrev State (n : ℕ) := WordRecursion.State n

theorem heat_generator_integrable {n : ℕ} (W : ObservationWindow n) {q : ℝ}
    (hq : q ∈ Icc W.left W.right) (H : State n →L[ℝ] State n →L[ℝ] ℝ) :
    Integrable (fun x : HeatCircle => W.coefficient (q, x) * H (heatRow W.observations q x) (heatRow W.observations q x)) haarAddCircle := by
  have hi (i j : Fin n) := covariance_spatial_integrable W.coefficient W.measurable W.observations
    W.gap_pos W.upper_nonneg W.target_gap hq.2 (W.bounded q hq) i j
  have hs := integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
    (hi i j).mul_const (H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))))
  convert hs using 1
  funext x
  rw [WordRecursion.bilinear_mixed_pairs H]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every diagonal and mixed physical heat pair is retained when the actual
covariance density acts on the Hessian. -/
theorem density_action_integral {n : ℕ} (W : ObservationWindow n) {q : ℝ}
    (hq : q ∈ Icc W.left W.right) (H : State n →L[ℝ] State n →L[ℝ] ℝ) :
    covarianceAction (densityMatrix W.coefficient W.observations q) H =
      ∫ x : HeatCircle, W.coefficient (q, x) * H (heatRow W.observations q x) (heatRow W.observations q x) ∂haarAddCircle := by
  have hi (i j : Fin n) := covariance_spatial_integrable W.coefficient W.measurable W.observations
    W.gap_pos W.upper_nonneg W.target_gap hq.2 (W.bounded q hq) i j
  have he (x : HeatCircle) : W.coefficient (q, x) * H (heatRow W.observations q x) (heatRow W.observations q x) =
      ∑ i : Fin n, ∑ j : Fin n, W.coefficient (q, x) * heatRow W.observations q x i * heatRow W.observations q x j *
        H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    rw [WordRecursion.bilinear_mixed_pairs H]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => (hi i j).mul_const _))]
  unfold covarianceAction
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => (hi i j).mul_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const]
  rfl

theorem covarianceAction_neg {n : ℕ} (A : Mat n) (H : State n →L[ℝ] State n →L[ℝ] ℝ) :
    covarianceAction (-A) H = -covarianceAction A H := by
  simpa only [actionLinear_apply] using map_neg (actionLinear H) A

/-- The genuine physical backward Gaussian equation, simultaneously at every
finite observation state, almost everywhere in time. The covariance is the
displayed physical heat/profile integral. No nondegeneracy is required. -/
theorem ae_physical_backward_equation {n : ℕ} (W : ObservationWindow n)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖GaussianTaylor.hessian F z‖ ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖GaussianTaylor.hessian F w - GaussianTaylor.hessian F z‖ ≤ K * ‖w - z‖) :
    ∀ᵐ q : ℝ, q ∈ Ioo W.left W.right → ∀ z : State n,
      HasDerivAt (fun t => gaussianSemigroup W.coefficient W.observations t W.right F z)
        (-(1 / 2 : ℝ) * ∫ x : HeatCircle, W.coefficient (q, x) *
          directionalSecond (gaussianSemigroup W.coefficient W.observations q W.right F) z
            (heatRow W.observations q x) ∂haarAddCircle) q := by
  filter_upwards [W.path_ae_hasDerivAt] with q hq
  intro hqin z
  have hd := hasDerivAt_monotone_gaussian_average W.path (hq hqin)
    (fun u v huv => W.path_antitone huv) hF hbound hD hDD hK hH z
  have heq : gaussianAverage (W.path q).val F = gaussianSemigroup W.coefficient W.observations q W.right F := by
    rw [W.path_eq (Ioo_subset_Icc_self hqin)]
    rfl
  rw [heq, covarianceAction_neg, mul_neg] at hd
  have he : covarianceAction (densityMatrix W.coefficient W.observations q)
      (GaussianTaylor.hessian (gaussianSemigroup W.coefficient W.observations q W.right F) z) =
      ∫ x : HeatCircle, W.coefficient (q, x) *
        directionalSecond (gaussianSemigroup W.coefficient W.observations q W.right F) z
          (heatRow W.observations q x) ∂haarAddCircle :=
    density_action_integral W (Ioo_subset_Icc_self hqin) _
  rw [he] at hd
  have hfun : (fun t => gaussianSemigroup W.coefficient W.observations t W.right F z) =ᶠ[nhds q]
      (fun t => gaussianAverage (W.path t).val F z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hqin] with t ht
    rw [W.path_eq (Ioo_subset_Icc_self ht)]
    rfl
  convert hd.congr_of_eventuallyEq hfun using 1; ring

end SHE.GaussianBackward
