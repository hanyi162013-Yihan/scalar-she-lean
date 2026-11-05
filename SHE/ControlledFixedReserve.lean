module

public import SHE.ControlledFiniteScores

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledFixedReserve
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianRangeSmooth
  ControlledProfile ControlledFutureMeans StoppedGaussianFeatures StoppedGaussianScore GaussianProfileMark
  ProfilePointwise ProfileParameter ProfileStability StoppedFourier PhysicalMeanRange
open scoped BigOperators NNReal Matrix.Norms.L2Operator
local instance controlledFixedReserve_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

def coefficient (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (old : ControlledProfile.Domain → ℝ) (θ : ℝ) (p : ControlledProfile.Domain) : ℝ :=
  profile P Λ u d (θ, p) - old p

def covariance (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (old : ControlledProfile.Domain → ℝ) (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (q θ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  stoppedCovariance σ target center (coefficient P Λ u d old θ) q

def mark (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (old : ControlledProfile.Domain → ℝ) (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (q : ℝ) (F : State n → ℝ) (θ : ℝ) (m : State n) : ℝ :=
  FiniteWordScores.covarianceMark (historyMeasure q) (covariance P Λ u d old σ target center q θ)
    (fun p => derivative P Λ u d (p, θ)) (stoppedRow σ target center) F m

theorem coefficient_bounds (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (old : ControlledProfile.Domain → ℝ) {ε : ℝ} (hb : ∀ p, 0 ≤ old p ∧ old p ≤ ε)
    (θ : ℝ) (p : ControlledProfile.Domain) :
    P.lower - ε ≤ coefficient P Λ u d old θ p ∧ coefficient P Λ u d old θ p ≤ P.upper := by
  have hp := profile_bounds P Λ u d (θ, p)
  have ho := hb p
  dsimp only [coefficient]
  constructor <;> linarith

/-- Any fixed measurable old covariance fraction bounded strictly below the
ellipticity floor leaves an actual uniform positive reserve. On one common
a.e. parameter event, every bounded Borel test has the literal signed
continuum covariance derivative, at every physical mean. -/
theorem reserve_and_mark (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (u d : CircleL2) (old : ControlledProfile.Domain → ℝ) (hold : Measurable old)
    {ε : ℝ} (hε : ε < P.lower) (hb : ∀ p, 0 ≤ old p ∧ old p ≤ ε)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσh : ∀ i, σ i ≤ P.horizon) (hages : ∀ i, σ i ≤ target i)
    (q : ℝ) (hq : 0 ≤ q)
    (hsmall : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2) :
    ∃ Q : ProfileReserve (covariance P Λ u d old σ target center q),
      (∃ K : ℝ≥0, LipschitzWith K (fun θ => (Q.residual θ).val)) ∧
      ∀ᵐ θ ∂volume, ∀ (F : State n → ℝ), Measurable F →
        ∀ M : ℝ, (∀ y, |F y| ≤ M) → ∀ z : State n,
          HasDerivAt (fun η => gaussianAverage (covariance P Λ u d old σ target center q η) F z)
            (mark P Λ u d old σ target center q F θ z) θ := by
  let c := coefficient P Λ u d old
  let row := stoppedRow σ target center
  let μ := historyMeasure q
  have hv : Measurable row := stoppedRow_measurable σ target center
  have hσ1 : ∀ i, σ i ≤ 1 := fun i => (hσh i).trans P.horizon_le_one
  have henergy : Integrable (fun p => ‖row p‖ ^ 2) μ := by
    have hi := StoppedProfileMark.bounded_profile_frame_integrable σ target center hσ hσ1 hages hq
      (c := fun _ => 1) measurable_const (M := 1) (fun _ => by norm_num)
    simpa only [abs_one, one_mul] using hi
  have hc (θ : ℝ) : Measurable (c θ) :=
    ((profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)).sub hold
  have hcb (θ : ℝ) (p : ControlledProfile.Domain) : |c θ p| ≤ P.upper := by
    rw [abs_of_nonneg ((sub_pos.mpr hε).le.trans (coefficient_bounds P Λ u d old hb θ p).1)]
    exact (coefficient_bounds P Λ u d old hb θ p).2
  have hci (θ : ℝ) : Integrable (fun p => |c θ p| * ‖row p‖ ^ 2) μ :=
    StoppedProfileMark.bounded_profile_frame_integrable σ target center hσ hσ1 hages hq (hc θ) (hcb θ)
  have hcl (θ : ℝ) : ∀ᵐ p ∂μ, P.lower - ε ≤ c θ p :=
    ae_of_all _ (fun p => (coefficient_bounds P Λ u d old hb θ p).1)
  have hgi : Integrable (fun p => P.dominator d p * ‖row p‖ ^ 2) μ :=
    P.stopped_dominator_frame_integrable σ target center hσ hσh hages d hq
  have hgl : ∀ᵐ p ∂μ, LipschitzWith (Real.nnabs (P.dominator d p)) (fun θ => c θ p) := by
    apply ae_of_all
    intro p
    apply LipschitzWith.of_dist_le_mul
    intro θ η
    have hi := (profile_curve_lipschitz P hΛ u d hsmall p).dist_le_mul θ η
    change |profile P Λ u d (θ, p) - profile P Λ u d (η, p)| ≤
      curveBound P.lower P.holder P.exponent P.horizon d p * |θ - η| at hi
    rw [Real.coe_nnabs, abs_of_nonneg (P.dominator_nonneg d p)]
    simpa only [c, coefficient, Real.dist_eq, sub_sub_sub_cancel_right,
      CanonicalCovariance.ProfileParameters.dominator] using hi
  have heq (θ : ℝ) : profileCovariance μ (c θ) row = covariance P Λ u d old σ target center q θ :=
    StoppedProfileMark.profileCovariance_eq_stopped σ target center hσ hσ1 hages hq (hc θ) (hcb θ)
  have hres := exists_uniform_profile_reserve μ (sub_pos.mpr hε) c row
    hv.aestronglyMeasurable henergy (fun θ => (hc θ).aestronglyMeasurable) hci hcl
    (P.dominator d) (ae_of_all _ (P.dominator_nonneg d)) hgi hgl
  have hfun : (fun θ => profileCovariance μ (c θ) row) = covariance P Λ u d old σ target center q :=
    funext heq
  rw [hfun] at hres
  obtain ⟨Q, K, hK⟩ := hres
  refine ⟨Q, ⟨K, hK⟩, ?_⟩
  filter_upwards [ControlledProfile.ae_hasDerivAt P hΛ u d hsmall μ] with θ hd
  intro F hF M hM z
  have he : AEStronglyMeasurable (fun p => derivative P Λ u d (p, θ)) μ :=
    ((derivative_measurable P hΛ u d hsmall).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hdiff : ∀ᵐ p ∂μ, HasDerivAt (fun η => c η p) (derivative P Λ u d (p, θ)) θ :=
    hd.mono (fun p hp => hp.sub_const (old p))
  have hh := hasDerivAt_profile_borel_of_uniform_floor μ (sub_pos.mpr hε) c
    (fun p => derivative P Λ u d (p, θ)) row hv.aestronglyMeasurable henergy
    (fun η => (hc η).aestronglyMeasurable) hci hcl he (P.dominator d)
    (ae_of_all _ (P.dominator_nonneg d)) hgi hgl hdiff F hF M hM z
  simp_rw [heq] at hh
  exact hh

theorem actual_future_direction_mem_range (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d D : CircleL2)
    (old : ControlledProfile.Domain → ℝ) (hold : Measurable old)
    {ε : ℝ} (hε : ε < P.lower) (hb : ∀ p, 0 ≤ old p ∧ old p ≤ ε)
    (target : Fin n → ℝ) (center : Fin n → UnitAddCircle) (q : ℝ) (hq : 0 ≤ q)
    (hgap : ∀ i, q < target i) :
    futureDirection Λ target center q hq d D ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (covariance P Λ u d old target target (nativeCenter center) q 0)).range := by
  obtain ⟨δ, hδ, hs⟩ := exists_positive_gap (fun i => target i - q) (fun i => sub_pos.mpr (hgap i))
  apply futureDirection_mem_range Λ hΛ target center q hq δ hδ (fun i => by linarith [hs i])
    (coefficient P Λ u d old 0)
    (((profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)).sub hold)
    P.upper (P.lower - ε)
  · intro p
    exact ⟨(sub_pos.mpr hε).le.trans (coefficient_bounds P Λ u d old hb 0 p).1,
      (coefficient_bounds P Λ u d old hb 0 p).2⟩
  · exact sub_pos.mpr hε
  · intro p
    exact (coefficient_bounds P Λ u d old hb 0 p).1

end SHE.ControlledFixedReserve
