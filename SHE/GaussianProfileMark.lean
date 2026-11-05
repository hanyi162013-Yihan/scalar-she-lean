module

public import SHE.GaussianSignedCovariance
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Genuine continuum covariance-profile differentiation and physical
rank-one disintegration. The signed profile mark stays inside its actual
integral, including every mixed observation pair. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianProfileMark
open MeasureTheory Set Real Matrix SHE.WordRecursion SHE.GaussianContinuity
  SHE.GaussianSignedCovariance SHE.GaussianTaylorAverage SHE.GaussianConvolution
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def rankMatrix {n : ℕ} (v : State n) : Mat n :=
  Matrix.toEuclideanLin.symm (InnerProductSpace.rankOne ℝ v v).toLinearMap

theorem rankMatrix_eq_vecMulVec {n : ℕ} (v : State n) :
    rankMatrix v = Matrix.vecMulVec (fun i => v i) (fun i => v i) := by
  simpa only [rankMatrix, star_trivial] using InnerProductSpace.symm_toEuclideanLin_rankOne v v

theorem rankMatrix_norm {n : ℕ} (v : State n) : ‖rankMatrix v‖ = ‖v‖ ^ 2 := by
  rw [Matrix.l2_opNorm_def]
  change ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (rankMatrix v))‖ = _
  rw [rankMatrix, LinearEquiv.apply_symm_apply]
  change ‖InnerProductSpace.rankOne ℝ v v‖ = _
  rw [InnerProductSpace.norm_rankOne, pow_two]

theorem rankMatrix_positive {n : ℕ} (v : State n) : (rankMatrix v).PosSemidef := by
  rw [rankMatrix_eq_vecMulVec]
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (fun i => v i)

theorem continuous_rankMatrix (n : ℕ) : Continuous (rankMatrix (n := n)) := by
  rw [show rankMatrix (n := n) =
    (fun v => Matrix.vecMulVec (fun i => v i) (fun i => v i)) from funext rankMatrix_eq_vecMulVec]
  apply continuous_matrix
  intro i j
  exact (PiLp.continuous_apply 2 _ i).mul (PiLp.continuous_apply 2 _ j)

theorem rankMatrix_covarianceAction {n : ℕ} (v : State n)
    (H : State n →L[ℝ] State n →L[ℝ] ℝ) : covarianceAction (rankMatrix v) H = H v v := by
  rw [rankMatrix_eq_vecMulVec]
  exact (bilinear_mixed_pairs H v).symm

def entryContinuous {n : ℕ} (i j : Fin n) : Mat n →L[ℝ] ℝ :=
  (show Mat n →ₗ[ℝ] ℝ from
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

theorem matrix_integral_entries {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (A : X → Mat n) (hA : Integrable A μ) (i j : Fin n) :
    (∫ x, A x ∂μ) i j = ∫ x, A x i j ∂μ := by
  exact ((entryContinuous i j).integral_comp_comm hA).symm

def profileCovariance {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (c : X → ℝ) (v : X → State n) : Mat n :=
  ∫ x, c x • rankMatrix (v x) ∂μ

theorem profileCovariance_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (c : X → ℝ) (v : X → State n)
    (hc : AEStronglyMeasurable c μ) (hv : AEStronglyMeasurable v μ)
    (hweight : Integrable (fun x => |c x| * ‖v x‖ ^ 2) μ) :
    Integrable (fun x => c x • rankMatrix (v x)) μ := by
  apply hweight.mono' (hc.smul ((continuous_rankMatrix n).comp_aestronglyMeasurable hv))
  filter_upwards with x
  simp only [Pi.smul_apply']
  rw [norm_smul, Real.norm_eq_abs, rankMatrix_norm]

theorem profileCovariance_entries {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (c : X → ℝ) (v : X → State n)
    (hi : Integrable (fun x => c x • rankMatrix (v x)) μ) (i j : Fin n) :
    profileCovariance μ c v i j = ∫ x, c x * v x i * v x j ∂μ := by
  rw [profileCovariance, matrix_integral_entries μ _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    simp only [Matrix.smul_apply, rankMatrix_eq_vecMulVec, Matrix.vecMulVec_apply, smul_eq_mul]
    ring)

theorem profileCovariance_positive {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (c : X → ℝ) (v : X → State n)
    (hi : Integrable (fun x => c x • rankMatrix (v x)) μ)
    (hc : ∀ᵐ x ∂μ, 0 ≤ c x) : (profileCovariance μ c v).PosSemidef := by
  have hentries (i j : Fin n) : Integrable (fun x => (c x • rankMatrix (v x)) i j) μ :=
    (entryContinuous i j).integrable_comp hi
  have hp := SHE.CovarianceMatrix.entry_integral_posSemidef μ _ hentries
    (hc.mono (fun x hx => (rankMatrix_positive (v x)).smul hx))
  convert! hp using 1
  ext i j
  exact matrix_integral_entries μ _ hi i j

/-- The covariance Hessian contraction disintegrates into the actual
continuum physical rank-one directions. The signed scalar input is kept
under the integral. -/
theorem profileCovariance_action {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (e : X → ℝ) (v : X → State n)
    (hi : Integrable (fun x => e x • rankMatrix (v x)) μ)
    (H : State n →L[ℝ] State n →L[ℝ] ℝ) :
    covarianceAction (profileCovariance μ e v) H = ∫ x, e x * H (v x) (v x) ∂μ := by
  let T : Mat n →L[ℝ] ℝ := (SHE.GaussianCovariancePath.actionLinear H).toLinearMap.toContinuousLinearMap
  have hT (A : Mat n) : T A = covarianceAction A H := rfl
  have hh := T.integral_comp_comm hi
  rw [hT] at hh
  change (∫ x, T (e x • rankMatrix (v x)) ∂μ) = _ at hh
  have hpoint (x : X) : T (e x • rankMatrix (v x)) = e x * H (v x) (v x) := by
    rw [map_smul, smul_eq_mul, hT, rankMatrix_covarianceAction]
  simpa only [hpoint, profileCovariance] using hh.symm

/-- Differentiation of the actual continuum covariance integral. The
dominator is the profile derivative times the physical frame energy;
no pointwise supremum of the signed input is taken. -/
theorem hasDerivAt_profileCovariance {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (c e : ℝ → X → ℝ) (v : X → State n) {θ₀ : ℝ} {s : Set ℝ}
    (hs : s ∈ nhds θ₀) (hv : AEStronglyMeasurable v μ)
    (hc : ∀ᶠ θ in nhds θ₀, AEStronglyMeasurable (c θ) μ)
    (hci : Integrable (fun x => |c θ₀ x| * ‖v x‖ ^ 2) μ)
    (he : AEStronglyMeasurable (e θ₀) μ) (g : X → ℝ)
    (hgi : Integrable (fun x => g x * ‖v x‖ ^ 2) μ)
    (hdom : ∀ᵐ x ∂μ, ∀ θ ∈ s, |e θ x| ≤ g x)
    (hdiff : ∀ᵐ x ∂μ, ∀ θ ∈ s, HasDerivAt (fun u => c u x) (e θ x) θ) :
    Integrable (fun x => e θ₀ x • rankMatrix (v x)) μ ∧
    HasDerivAt (fun θ => profileCovariance μ (c θ) v)
      (profileCovariance μ (e θ₀) v) θ₀ := by
  have hvr := (continuous_rankMatrix n).comp_aestronglyMeasurable hv
  have hc₀ : AEStronglyMeasurable (c θ₀) μ := hc.self_of_nhds
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun θ x => c θ x • rankMatrix (v x))
    (F' := fun θ x => e θ x • rankMatrix (v x)) (bound := fun x => g x * ‖v x‖ ^ 2) hs
    (hc.mono (fun θ hθ => hθ.smul hvr))
    (profileCovariance_integrable μ (c θ₀) v hc₀ hv hci) (he.smul hvr)
    (hdom.mono (fun x hx θ hθ => by
      rw [norm_smul, Real.norm_eq_abs, rankMatrix_norm]
      exact mul_le_mul_of_nonneg_right (hx θ hθ) (sq_nonneg _))) hgi
    (hdiff.mono (fun x hx θ hθ => (hx θ hθ).smul_const (rankMatrix (v x))))

/-- Genuine marked differentiation of a Gaussian law whose covariance is
the actual continuum profile integral. The final derivative is a physical
rank-one integral containing the signed profile input. All mixed pairs,
singular ranks, collisions and nonmonotone covariance changes are covered. -/
theorem hasDerivAt_profile_gaussian_average {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (c e : ℝ → X → ℝ) (v : X → State n) {θ₀ : ℝ} {s : Set ℝ}
    (hs : s ∈ nhds θ₀) (hv : AEStronglyMeasurable v μ)
    (hc : ∀ θ, AEStronglyMeasurable (c θ) μ)
    (hci : ∀ θ, Integrable (fun x => |c θ x| * ‖v x‖ ^ 2) μ)
    (hcpos : ∀ θ, ∀ᵐ x ∂μ, 0 ≤ c θ x)
    (he : AEStronglyMeasurable (e θ₀) μ) (g : X → ℝ)
    (hgi : Integrable (fun x => g x * ‖v x‖ ^ 2) μ)
    (hdom : ∀ᵐ x ∂μ, ∀ θ ∈ s, |e θ x| ≤ g x)
    (hdiff : ∀ᵐ x ∂μ, ∀ θ ∈ s, HasDerivAt (fun u => c u x) (e θ x) θ)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖) (z : State n) :
    HasDerivAt (fun θ => gaussianAverage (profileCovariance μ (c θ) v) F z)
      ((1 / 2 : ℝ) * ∫ x, e θ₀ x *
        hessian (gaussianAverage (profileCovariance μ (c θ₀) v) F) z (v x) (v x) ∂μ) θ₀ := by
  have hi (θ : ℝ) := profileCovariance_integrable μ (c θ) v (hc θ) hv (hci θ)
  let C : ℝ → PositiveCovariance n := fun θ =>
    ⟨profileCovariance μ (c θ) v, profileCovariance_positive μ (c θ) v (hi θ) (hcpos θ)⟩
  obtain ⟨hei, hd⟩ := hasDerivAt_profileCovariance μ c e v hs hv
    (Filter.Eventually.of_forall hc) (hci θ₀) he g hgi hdom hdiff
  have hg := SHE.GaussianSignedCovariance.hasDerivAt_gaussian_average C hd
    hF hbound hD hDD hK hH z
  rw [profileCovariance_action μ (e θ₀) v hei] at hg
  exact hg

end SHE.GaussianProfileMark
