module

public import SHE.GaussianBorelProfileMark
public import SHE.ProfileFrameRange
public import SHE.PositiveMatrixRanges

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! An actual positive scalar floor supplies every covariance-range
condition for bounded-Borel continuum marking. The fixed mean is arbitrary,
including means outside the singular covariance range. -/
namespace SHE.GaussianRangeSmooth
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianProfileMark
  GaussianConvolution MeasurableGaussianScores
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

theorem covariance_range_smul {n : ℕ} (A : Mat n) {α : ℝ} (hα : α ≠ 0) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (α • A)).range =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range := by
  have he : (Matrix.toEuclideanCLM (𝕜 := ℝ) (α • A)).toLinearMap =
      α • (Matrix.toEuclideanCLM (𝕜 := ℝ) A).toLinearMap := by
    apply LinearMap.ext
    intro x
    simp
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) (α • A)).toLinearMap.range = _
  rw [he, LinearMap.range_smul _ α hα]

theorem profileCovariance_add_floor {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (α : ℝ) (c : X → ℝ) (v : X → State n)
    (hi : Integrable (fun x => rankMatrix (v x)) μ)
    (hc : Integrable (fun x => c x • rankMatrix (v x)) μ) :
    profileCovariance μ (fun x => α + c x) v =
      α • profileCovariance μ (fun _ => 1) v + profileCovariance μ c v := by
  unfold profileCovariance
  simp only [one_smul, add_smul]
  have hiα : Integrable (fun x => α • rankMatrix (v x)) μ := hi.smul α
  rw [integral_add hiα hc, integral_smul]

theorem hasDerivAt_profile_borel_positive_floor
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    {α : ℝ} (hα : 0 < α) (c : ℝ → X → ℝ) (e : X → ℝ) (v : X → State n) {θ₀ : ℝ}
    (hv : AEStronglyMeasurable v μ) (henergy : Integrable (fun x => ‖v x‖ ^ 2) μ)
    (hc : ∀ θ, AEStronglyMeasurable (c θ) μ)
    (hci : ∀ θ, Integrable (fun x => |c θ x| * ‖v x‖ ^ 2) μ)
    (hcpos : ∀ θ, ∀ᵐ x ∂μ, 0 ≤ c θ x)
    (he : AEStronglyMeasurable e μ) (g : X → ℝ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hgi : Integrable (fun x => g x * ‖v x‖ ^ 2) μ)
    (hlip : ∀ᵐ x ∂μ, LipschitzWith (Real.nnabs (g x)) (fun θ => c θ x))
    (hdiff : ∀ᵐ x ∂μ, HasDerivAt (fun θ => c θ x) (e x) θ₀)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M) (z : State n) :
    HasDerivAt (fun θ => gaussianAverage (profileCovariance μ (fun x => α + c θ x) v) F z)
      ((1 / 2 : ℝ) * ∫ x, e x *
        (∫ y, F (z + y) * secondScore (profileCovariance μ (fun x => α + c θ₀ x) v) (v x) y
          ∂multivariateGaussian 0 (profileCovariance μ (fun x => α + c θ₀ x) v)) ∂μ) θ₀ := by
  let G := profileCovariance μ (fun _ => 1) v
  let R := α • G
  have hiG : Integrable (fun x => (1 : ℝ) • rankMatrix (v x)) μ :=
    profileCovariance_integrable μ (fun _ => 1) v aestronglyMeasurable_const hv (by simpa using henergy)
  have hG : G.PosSemidef := profileCovariance_positive μ (fun _ => 1) v hiG (ae_of_all _ (by norm_num))
  have hR : R.PosSemidef := hG.smul hα.le
  have hr : (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range = (Matrix.toEuclideanCLM (𝕜 := ℝ) G).range :=
    covariance_range_smul G hα.ne'
  have hvG := ae_frame_mem_gram_range μ v hv henergy
  have hvR : ∀ᵐ x ∂μ, v x ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range := by
    simpa only [hr, G] using hvG
  have hi (θ : ℝ) := profileCovariance_integrable μ (c θ) v (hc θ) hv (hci θ)
  have hp (θ : ℝ) := profileCovariance_positive μ (c θ) v (hi θ) (hcpos θ)
  have hRange (θ : ℝ) : (Matrix.toEuclideanCLM (𝕜 := ℝ) (profileCovariance μ (c θ) v)).range ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range :=
    profileCovariance_range_le μ (c θ) v (hi θ) _ hvR
  have hvA : ∀ᵐ x ∂μ, v x ∈
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (R + profileCovariance μ (c θ₀) v)).range :=
    hvR.mono (fun _ hx => PositiveMatrixRanges.range_le_add_right hR (hp θ₀) hx)
  let Fz : State n → ℝ := fun y => F (z + y)
  have hh := hasDerivAt_profile_borel_reserve μ hR c e v hv hc hci hcpos he g hg0 hgi hlip hdiff
    hRange hvR hvA Fz (hF.comp (measurable_const.add measurable_id)) M (fun y => hM _)
    (Submodule.zero_mem _)
  have hcov (θ : ℝ) : profileCovariance μ (fun x => α + c θ x) v = R + profileCovariance μ (c θ) v :=
    profileCovariance_add_floor μ α (c θ) v (by simpa only [one_smul] using hiG) (hi θ)
  simp_rw [← hcov] at hh
  convert! hh using 1
  · funext θ
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by simp [Fz])
  · congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by simp only [zero_add, Fz])

end SHE.GaussianRangeSmooth
