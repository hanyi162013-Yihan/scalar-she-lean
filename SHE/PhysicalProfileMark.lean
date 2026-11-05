module

public import SHE.GaussianProfileMarkAE
public import SHE.HeatRowWeighted
public import SHE.ProfileParameterL2
public import SHE.CanonicalCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Literal physical covariance differentiation for the actual canonical
profile, including terminal-age observations. The derivative profile is a
proved ordinary scalar derivative with the sharp spatial L² estimate. -/
noncomputable section
namespace SHE.PhysicalProfileMark
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance WordRecursion
  GaussianProfileMark GaussianProfileMarkAE HeatRowWeighted ProfilePointwise ProfileParameter
  CanonicalCovariance GaussianContinuity GaussianTaylorAverage GaussianConvolution
open scoped MatrixOrder Matrix.Norms.L2Operator NNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

instance sourceMeasure_sfinite (s : ℝ) : SFinite (sourceMeasure s) := by
  unfold sourceMeasure
  infer_instance

/-- Bounded measurable profiles multiply the actual physical frame energy
integrably, including zero terminal heat gaps. -/
theorem bounded_profile_frame_integrable {n : ℕ} (Z : Fin n → Observation)
    {s M : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hZ : ∀ i, s ≤ (Z i).target)
    {c : HeatRowWeighted.Domain → ℝ} (hc : Measurable c) (_hM : 0 ≤ M)
    (hbound : ∀ p, |c p| ≤ M) :
    Integrable (fun p => |c p| * ‖heatRow Z p.1 p.2‖ ^ 2) (sourceMeasure s) := by
  have hi := weighted_heatRow_integrable Z hs hs1 (by norm_num : (-1 : ℝ) < 0) hZ
  simp only [Real.rpow_zero, one_mul] at hi
  apply (hi.const_mul M).mono'
    (((continuous_abs.measurable.comp hc).mul
      ((heatRow_vector_measurable Z).norm.pow_const (2 : ℕ))).aestronglyMeasurable)
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hbound p) (sq_nonneg _)

/-- The abstract continuum rank-one covariance is exactly the manuscript's
physical covariance matrix, not an independently selected Gaussian matrix. -/
theorem profileCovariance_eq_physical {n : ℕ} (Z : Fin n → Observation)
    {s M : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hZ : ∀ i, s ≤ (Z i).target)
    {c : HeatRowWeighted.Domain → ℝ} (hc : Measurable c) (hM : 0 ≤ M)
    (hbound : ∀ p, |c p| ≤ M) :
    profileCovariance (sourceMeasure s) c (fun p => heatRow Z p.1 p.2) =
      covariance c Z 0 s := by
  have hw := bounded_profile_frame_integrable Z hs hs1 hZ hc hM hbound
  have hi := profileCovariance_integrable (sourceMeasure s) c
    (fun p => heatRow Z p.1 p.2) hc.aestronglyMeasurable
    (heatRow_vector_measurable Z).aestronglyMeasurable hw
  ext i j
  rw [profileCovariance_entries (sourceMeasure s) c (fun p => heatRow Z p.1 p.2) hi i j]
  have he : Integrable (fun p : HeatRowWeighted.Domain =>
      c p * heatRow Z p.1 p.2 i * heatRow Z p.1 p.2 j) (sourceMeasure s) := by
    have hh := (entryContinuous i j).integrable_comp hi
    change Integrable (fun p : HeatRowWeighted.Domain =>
      (c p • rankMatrix (heatRow Z p.1 p.2)) i j) (sourceMeasure s) at hh
    simpa only [Matrix.smul_apply, rankMatrix_eq_vecMulVec, Matrix.vecMulVec_apply,
      smul_eq_mul, mul_assoc] using hh
  rw [sourceMeasure, integral_prod _ he]
  exact (intervalIntegral.integral_of_le hs.le).symm

end SHE.PhysicalProfileMark

namespace SHE.CanonicalCovariance.ProfileParameters
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance WordRecursion
  GaussianProfileMark GaussianProfileMarkAE HeatRowWeighted ProfilePointwise ProfileParameter
  GaussianContinuity GaussianTaylorAverage GaussianConvolution PhysicalProfileMark
open scoped MatrixOrder Matrix.Norms.L2Operator NNReal Topology
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable (P : ProfileParameters)

def varyingCoefficient (u d : CircleL2) (θ : ℝ) (p : HeatRowWeighted.Domain) : ℝ :=
  profileCurve P.coefficient P.lower P.horizon u d p θ

def derivative (u d : CircleL2) (θ : ℝ) (p : HeatRowWeighted.Domain) : ℝ :=
  profileDerivative P.coefficient P.lower P.horizon u d (p, θ)

def dominator (d : CircleL2) (p : HeatRowWeighted.Domain) : ℝ :=
  curveBound P.lower P.holder P.exponent P.horizon d p

theorem coefficient_measurable (u d : CircleL2) (θ : ℝ) :
    Measurable (P.varyingCoefficient u d θ) :=
  (profileCurve_measurable P.measurable P.lower_pos P.upper_nonneg P.holder_nonneg
    P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound
    P.holder_bound P.small u d).comp (measurable_id.prodMk measurable_const)

theorem coefficient_bounds (u d : CircleL2) (θ : ℝ) (p : HeatRowWeighted.Domain) :
    P.lower ≤ P.varyingCoefficient u d θ p ∧ P.varyingCoefficient u d θ p ≤ P.upper := by
  unfold varyingCoefficient profileCurve
  split_ifs
  · exact CanonicalProfile.profile_elliptic P.measurable P.lower_pos P.upper_nonneg P.holder_nonneg
      P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound
      P.holder_bound P.small _
  · exact ⟨le_rfl, (P.lower_bound 0).trans (P.upper_bound 0)⟩

theorem coefficient_abs_bound (u d : CircleL2) (θ : ℝ) (p : HeatRowWeighted.Domain) :
    |P.varyingCoefficient u d θ p| ≤ P.upper := by
  rw [abs_of_nonneg (P.lower_pos.le.trans (P.coefficient_bounds u d θ p).1)]
  exact (P.coefficient_bounds u d θ p).2

omit [MeasurableSpace CircleL2] [BorelSpace CircleL2] in
theorem dominator_nonneg (d : CircleL2) (p : HeatRowWeighted.Domain) :
    0 ≤ P.dominator d p := curveBound_nonneg P.lower_pos.le P.holder_nonneg d p

omit [MeasurableSpace CircleL2] [BorelSpace CircleL2] in
/-- The deterministic pointwise derivative dominator is genuinely integrable
against the entire physical history frame. -/
theorem dominator_frame_integrable {n : ℕ} (Z : Fin n → Observation)
    (_u d : CircleL2) {s : ℝ} (hs : 0 < s) (hsh : s ≤ P.horizon)
    (hZ : ∀ i, s ≤ (Z i).target) :
    Integrable (fun p => P.dominator d p * ‖heatRow Z p.1 p.2‖ ^ 2) (sourceMeasure s) := by
  have hi := weighted_heatRow_integrable Z hs (hsh.trans P.horizon_le_one)
    (show -1 < (P.exponent - 2) / 4 by linarith [P.exponent_pos]) hZ
  have hc := hi.const_mul
    (2 * (ProfileStability.meanConstant P.lower P.holder P.exponent *
      Real.sqrt (1 + heatConstant) * ‖d‖))
  apply hc.congr
  have ht : ∀ᵐ p : HeatRowWeighted.Domain ∂sourceMeasure s, p.1 ∈ Ioc 0 s :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [ht] with p hp
  rw [dominator, curveBound, ite_eq_left (show p.1 ∈ Ioc 0 P.horizon from
    ⟨hp.1, hp.2.trans hsh⟩), pointwiseConstant]
  ring

/-- Genuine a.e. marked differentiation of the literal physical Gaussian
reference generated by the actual consistent canonical scalar profile. -/
theorem ae_physical_gaussian_mark {n : ℕ} (Z : Fin n → Observation)
    (u d : CircleL2) {s : ℝ} (hs : 0 < s) (hsh : s ≤ P.horizon)
    (hZ : ∀ i, s ≤ (Z i).target)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) *
        P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    {F : WordRecursion.State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖) (z : WordRecursion.State n) :
    ∀ᵐ θ ∂volume,
      HasDerivAt (fun η => gaussianSemigroup (P.varyingCoefficient u d η) Z 0 s F z)
        ((1 / 2 : ℝ) * ∫ p : HeatRowWeighted.Domain, P.derivative u d θ p *
          hessian (gaussianSemigroup (P.varyingCoefficient u d θ) Z 0 s F) z
            (heatRow Z p.1 p.2) (heatRow Z p.1 p.2) ∂sourceMeasure s) θ := by
  have hv := (heatRow_vector_measurable Z).aestronglyMeasurable (μ := sourceMeasure s)
  have hc (θ : ℝ) := (P.coefficient_measurable u d θ).aestronglyMeasurable (μ := sourceMeasure s)
  have hci (θ : ℝ) := bounded_profile_frame_integrable Z hs (hsh.trans P.horizon_le_one)
    hZ (P.coefficient_measurable u d θ) P.upper_nonneg (P.coefficient_abs_bound u d θ)
  have hcpos (θ : ℝ) : ∀ᵐ p ∂sourceMeasure s, 0 ≤ P.varyingCoefficient u d θ p :=
    ae_of_all _ (fun p => P.lower_pos.le.trans (P.coefficient_bounds u d θ p).1)
  have he (θ : ℝ) : AEStronglyMeasurable (P.derivative u d θ) (sourceMeasure s) :=
    ((profileDerivative_measurable P.measurable P.lower_pos P.upper_nonneg P.holder_nonneg
      P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound
      P.holder_bound P.small hsmallPoint u d).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hlip : ∀ᵐ p ∂sourceMeasure s,
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
    P.holder_bound P.small hsmallPoint (sourceMeasure s) u d
  filter_upwards [hd] with θ hθ
  have hmark := hasDerivAt_profile_gaussian_average_of_lipschitz (sourceMeasure s)
    (P.varyingCoefficient u d) (P.derivative u d θ) (fun p => heatRow Z p.1 p.2) hv hc hci hcpos
    (he θ) (P.dominator d) (ae_of_all _ (P.dominator_nonneg d))
    (P.dominator_frame_integrable Z u d hs hsh hZ) hlip hθ hF hbound hD hDD hK hH z
  have heq (η : ℝ) := profileCovariance_eq_physical Z hs (hsh.trans P.horizon_le_one) hZ
    (P.coefficient_measurable u d η) P.upper_nonneg (P.coefficient_abs_bound u d η)
  simp_rw [heq] at hmark
  exact hmark

end SHE.CanonicalCovariance.ProfileParameters
