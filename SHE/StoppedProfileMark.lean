module

public import SHE.StoppedRowWeighted
public import SHE.PhysicalProfileMark

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Genuine signed canonical-profile differentiation of the full
individually stopped observation covariance. Each original stopping mask
remains inside its own row throughout covariance differentiation. -/
namespace SHE.StoppedProfileMark
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance
  StoppedGaussianFeatures StoppedRowWeighted GaussianProfileMark
  GaussianProfileMarkAE GaussianContinuity GaussianTaylorAverage GaussianConvolution GaussianTaylor
open scoped MatrixOrder Matrix.Norms.L2Operator NNReal Topology
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {n : ℕ} (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)

theorem bounded_profile_frame_integrable
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1) (hages : ∀ i, σ i ≤ target i)
    {q : ℝ} (hq : 0 ≤ q) {c : Domain → ℝ} (hc : Measurable c)
    {M : ℝ} (hbound : ∀ p, |c p| ≤ M) :
    Integrable (fun p => |c p| * ‖stoppedRow σ target center p‖ ^ 2) (historyMeasure q) := by
  have hi := weighted_stopped_row_integrable_cutoff σ target center hσ hσ1 hages
    (by norm_num : (-1 : ℝ) < 0) hq
  simp only [Real.rpow_zero, one_mul] at hi
  apply (hi.const_mul M).mono'
    (((continuous_abs.measurable.comp hc).mul
      ((stoppedRow_measurable σ target center).norm.pow_const (2 : ℕ))).aestronglyMeasurable)
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hbound p) (sq_nonneg _)

theorem profileCovariance_eq_stopped
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1) (hages : ∀ i, σ i ≤ target i)
    {q : ℝ} (hq : 0 ≤ q) {c : Domain → ℝ} (hc : Measurable c)
    {M : ℝ} (hbound : ∀ p, |c p| ≤ M) :
    profileCovariance (historyMeasure q) c (stoppedRow σ target center) =
      StoppedGaussianFeatures.stoppedCovariance σ target center c q := by
  have hw := bounded_profile_frame_integrable σ target center hσ hσ1 hages hq hc hbound
  have hi := profileCovariance_integrable (historyMeasure q) c (stoppedRow σ target center)
    hc.aestronglyMeasurable (stoppedRow_measurable σ target center).aestronglyMeasurable hw
  ext i j
  exact profileCovariance_entries (historyMeasure q) c (stoppedRow σ target center) hi i j

end SHE.StoppedProfileMark

namespace SHE.CanonicalCovariance.ProfileParameters
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance
  StoppedGaussianFeatures StoppedRowWeighted StoppedProfileMark GaussianProfileMark
  GaussianProfileMarkAE GaussianContinuity GaussianTaylorAverage GaussianConvolution GaussianTaylor
  ProfilePointwise ProfileParameter
open scoped MatrixOrder Matrix.Norms.L2Operator NNReal Topology
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable (P : ProfileParameters)

omit [MeasurableSpace CircleL2] [BorelSpace CircleL2] in
theorem stopped_dominator_frame_integrable {n : ℕ}
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσh : ∀ i, σ i ≤ P.horizon)
    (hages : ∀ i, σ i ≤ target i) (d : CircleL2) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun p => P.dominator d p * ‖stoppedRow σ target center p‖ ^ 2) (historyMeasure q) := by
  let C := 2 * (ProfileStability.meanConstant P.lower P.holder P.exponent *
    Real.sqrt (1 + heatConstant) * ‖d‖)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity [ProfileStability.meanConstant_nonneg (β := P.exponent) P.lower_pos.le P.holder_nonneg]
  have hi := weighted_stopped_row_integrable_cutoff σ target center hσ
    (fun i => (hσh i).trans P.horizon_le_one) hages
    (show -1 < (P.exponent - 2) / 4 by linarith [P.exponent_pos]) hq
  have hm : Measurable (P.dominator d) := by
    unfold dominator curveBound pointwiseConstant
    exact (((real_rpow_measurable ((P.exponent - 2) / 4)).comp measurable_fst).const_mul C).ite
      (measurableSet_Ioc.preimage measurable_fst) measurable_const
  apply (hi.const_mul C).mono'
    ((hm.mul ((stoppedRow_measurable σ target center).norm.pow_const (2 : ℕ))).aestronglyMeasurable)
  have ht : ∀ᵐ p : StoppedGaussianFeatures.Domain ∂historyMeasure q, 0 ≤ p.1 := by
    exact Measure.quasiMeasurePreserving_fst.ae
      ((ae_restrict_mem measurableSet_Ici).mono (fun t ht => hq.trans ht))
  filter_upwards [ht] with p hp
  change ‖P.dominator d p * ‖stoppedRow σ target center p‖ ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (P.dominator_nonneg d p) (sq_nonneg _))]
  have hg : P.dominator d p ≤ C * p.1 ^ ((P.exponent - 2) / 4) := by
    unfold dominator curveBound
    split_ifs with ht
    · unfold pointwiseConstant C
      ring_nf
      exact le_rfl
    · exact mul_nonneg hC (Real.rpow_nonneg hp _)
  exact (mul_le_mul_of_nonneg_right hg (sq_nonneg _)).trans_eq (by ring)

/-- Actual a.e. parameter differentiation of the complete stopped-history
Gaussian reference generated by the consistent canonical profile. This
allows distinct stopping times, arbitrary target-stop gaps, and singular
observation covariances. -/
theorem ae_stopped_physical_gaussian_mark {n : ℕ}
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσh : ∀ i, σ i ≤ P.horizon)
    (hages : ∀ i, σ i ≤ target i) (u d : CircleL2) {q : ℝ} (hq : 0 ≤ q)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) *
        P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    {F : WordRecursion.State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖) (z : WordRecursion.State n) :
    ∀ᵐ θ ∂volume,
      HasDerivAt (fun η => gaussianAverage
        (StoppedGaussianFeatures.stoppedCovariance σ target center (P.varyingCoefficient u d η) q) F z)
        ((1 / 2 : ℝ) * ∫ p : StoppedGaussianFeatures.Domain, P.derivative u d θ p *
          hessian (gaussianAverage
            (StoppedGaussianFeatures.stoppedCovariance σ target center (P.varyingCoefficient u d θ) q) F) z
            (stoppedRow σ target center p) (stoppedRow σ target center p) ∂historyMeasure q) θ := by
  have hv := (stoppedRow_measurable σ target center).aestronglyMeasurable (μ := historyMeasure q)
  have hc (θ : ℝ) := (P.coefficient_measurable u d θ).aestronglyMeasurable (μ := historyMeasure q)
  have hci (θ : ℝ) := StoppedProfileMark.bounded_profile_frame_integrable σ target center hσ
    (fun i => (hσh i).trans P.horizon_le_one) hages hq
    (P.coefficient_measurable u d θ) (P.coefficient_abs_bound u d θ)
  have hcpos (θ : ℝ) : ∀ᵐ p ∂historyMeasure q, 0 ≤ P.varyingCoefficient u d θ p :=
    ae_of_all _ (fun p => P.lower_pos.le.trans (P.coefficient_bounds u d θ p).1)
  have he (θ : ℝ) : AEStronglyMeasurable (P.derivative u d θ) (historyMeasure q) :=
    ((profileDerivative_measurable P.measurable P.lower_pos P.upper_nonneg P.holder_nonneg
      P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound
      P.holder_bound P.small hsmallPoint u d).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hlip : ∀ᵐ p ∂historyMeasure q,
      LipschitzWith (Real.nnabs (P.dominator d p)) (fun θ => P.varyingCoefficient u d θ p) := by
    apply ae_of_all
    intro p
    apply LipschitzWith.of_dist_le_mul
    intro θ η
    have hh := (profileCurve_lipschitz P.measurable P.lower_pos P.upper_nonneg P.holder_nonneg
      P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound
      P.holder_bound P.small hsmallPoint u d p).dist_le_mul θ η
    rw [Real.coe_nnabs, abs_of_nonneg (P.dominator_nonneg d p)]
    exact hh
  have hd := ae_profile_hasDerivAt P.measurable P.lower_pos P.upper_nonneg P.holder_nonneg
    P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound
    P.holder_bound P.small hsmallPoint (historyMeasure q) u d
  filter_upwards [hd] with θ hθ
  have hmark := hasDerivAt_profile_gaussian_average_of_lipschitz (historyMeasure q)
    (P.varyingCoefficient u d) (P.derivative u d θ) (stoppedRow σ target center) hv hc hci hcpos
    (he θ) (P.dominator d) (ae_of_all _ (P.dominator_nonneg d))
    (P.stopped_dominator_frame_integrable σ target center hσ hσh hages d hq)
    hlip hθ hF hbound hD hDD hK hH z
  have heq (η : ℝ) := profileCovariance_eq_stopped σ target center hσ
    (fun i => (hσh i).trans P.horizon_le_one) hages hq
    (P.coefficient_measurable u d η) (P.coefficient_abs_bound u d η)
  simp_rw [heq] at hmark
  exact hmark

end SHE.CanonicalCovariance.ProfileParameters
