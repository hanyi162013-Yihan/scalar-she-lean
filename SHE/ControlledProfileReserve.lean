module

public import SHE.ControlledBorelProfileMark
public import SHE.ProfileReserveCalculus

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledProfile
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier ProfileVariance
  StoppedGaussianFeatures StoppedProfileMark GaussianProfileMark GaussianRangeSmooth
  GaussianConvolution ProfileParameter ProfilePointwise ProfileStability
open scoped MatrixOrder Matrix.Norms.L2Operator NNReal Topology
local instance controlledProfileReserve_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters)

/-- The actual controlled canonical profile constructs one fixed reserve
for the entire parameter path, with a genuinely Lipschitz residual and
the exact physical range of every full stopped covariance. -/
theorem exists_stopped_profile_reserve {n : ℕ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσh : ∀ i, σ i ≤ P.horizon)
    (hages : ∀ i, σ i ≤ target i) (u d : CircleL2) {q : ℝ} (hq : 0 ≤ q)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2) :
    ∃ Q : ProfileReserve (fun θ => StoppedGaussianFeatures.stoppedCovariance σ target center
        (fun p => profile P Λ u d (θ, p)) q),
      ∃ K : ℝ≥0, LipschitzWith K (fun θ => (Q.residual θ).val) := by
  have hv := (stoppedRow_measurable σ target center).aestronglyMeasurable (μ := historyMeasure q)
  have henergy : Integrable (fun p => ‖stoppedRow σ target center p‖ ^ 2) (historyMeasure q) := by
    have hh := StoppedProfileMark.bounded_profile_frame_integrable σ target center hσ
      (fun i => (hσh i).trans P.horizon_le_one) hages hq
      (c := fun _ => 1) measurable_const (M := 1) (by intro p; norm_num)
    simpa only [abs_one, one_mul] using hh
  have hcm (θ : ℝ) : Measurable (fun p => profile P Λ u d (θ, p)) :=
    (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hc (θ : ℝ) := (hcm θ).aestronglyMeasurable (μ := historyMeasure q)
  have hcb (θ : ℝ) (p : Domain) : |profile P Λ u d (θ, p)| ≤ P.upper := by
    rw [abs_of_nonneg (P.lower_pos.le.trans (profile_bounds P Λ u d (θ, p)).1)]
    exact (profile_bounds P Λ u d (θ, p)).2
  have hci (θ : ℝ) := StoppedProfileMark.bounded_profile_frame_integrable σ target center hσ
    (fun i => (hσh i).trans P.horizon_le_one) hages hq (hcm θ) (hcb θ)
  have hclower (θ : ℝ) : ∀ᵐ p ∂historyMeasure q, P.lower ≤ profile P Λ u d (θ, p) :=
    ae_of_all _ (fun p => (profile_bounds P Λ u d (θ, p)).1)
  have hlip : ∀ᵐ p ∂historyMeasure q,
      LipschitzWith (Real.nnabs (P.dominator d p)) (fun θ => profile P Λ u d (θ, p)) := by
    apply ae_of_all
    intro p
    apply LipschitzWith.of_dist_le_mul
    intro θ η
    have hh := (profile_curve_lipschitz P hΛ u d hsmallPoint p).dist_le_mul θ η
    rw [Real.coe_nnabs, abs_of_nonneg (P.dominator_nonneg d p)]
    exact hh
  have hh := exists_uniform_profile_reserve (historyMeasure q) P.lower_pos
    (fun θ p => profile P Λ u d (θ, p)) (stoppedRow σ target center) hv henergy hc hci hclower
    (P.dominator d) (ae_of_all _ (P.dominator_nonneg d))
    (P.stopped_dominator_frame_integrable σ target center hσ hσh hages d hq) hlip
  have heq (η : ℝ) := profileCovariance_eq_stopped σ target center hσ
    (fun i => (hσh i).trans P.horizon_le_one) hages hq (hcm η) (hcb η)
  have hfun : (fun η => profileCovariance (historyMeasure q) (fun p => profile P Λ u d (η, p))
      (stoppedRow σ target center)) =
      fun η => StoppedGaussianFeatures.stoppedCovariance σ target center (fun p => profile P Λ u d (η, p)) q :=
    funext heq
  rw [hfun] at hh
  exact hh

end SHE.ControlledProfile
