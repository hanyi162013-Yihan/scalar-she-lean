module

public import SHE.ControlledProfileTransfer
public import SHE.PhysicalMeanRange

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledObservationTransfer
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore GaussianIncrement GaussianRangeSmooth GaussianConvolution
  ProfilePointwise ProfileStability PhysicalMeanRange ControlledProfile
open scoped InnerProductSpace Matrix.Norms.L2Operator
local instance controlledObservationTransfer_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

/-- The actual finite controlled heat mean, sampled at the original
observation times and physical centers. -/
def meanVector (Λ : ℝ) (σ : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (u d : CircleL2) (θ : ℝ) : State n :=
  WithLp.toLp 2 (fun i => ControlledProfile.mean Λ u d (θ, (σ i, nativeCenter a i)))

theorem meanVector_affine (Λ : ℝ) (σ : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (u d : CircleL2) (θ : ℝ) :
    meanVector Λ σ a u d θ = currentDirection σ a 0 u + θ • dampedDirection σ σ a 0 Λ d := by
  apply PiLp.ext
  intro i
  change PhysicalProfile.physicalHeatMean u (σ i, nativeCenter a i) +
      θ * exp (-Λ * σ i) * PhysicalProfile.physicalHeatMean d (σ i, nativeCenter a i) =
    PhysicalProfile.physicalHeatMean u (σ i - 0, nativeCenter a i) +
      θ * (exp (-Λ * (σ i - 0)) * PhysicalProfile.physicalHeatMean d (σ i - 0, nativeCenter a i))
  simp only [sub_zero]
  ring

/-- The range condition is proved from ellipticity and the actual full
stopped physical history. No covariance nondegeneracy is assumed. -/
theorem direction_mem_range (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (σ : Fin n → ℝ) (a : Fin n → UnitAddCircle) (hσ : ∀ i, 0 < σ i)
    (u d : CircleL2) :
    dampedDirection σ σ a 0 Λ d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (stoppedCovariance σ σ (nativeCenter a) (fun p => profile P Λ u d (0, p)) 0)).range := by
  obtain ⟨δ, hδ, hδσ⟩ := exists_positive_gap σ hσ
  have hc : Measurable (fun p => profile P Λ u d (0, p)) :=
    (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hb (p : ControlledProfile.Domain) : 0 ≤ profile P Λ u d (0, p) ∧ profile P Λ u d (0, p) ≤ P.upper :=
    ⟨P.lower_pos.le.trans (profile_bounds P Λ u d (0, p)).1, (profile_bounds P Λ u d (0, p)).2⟩
  exact dampedDirection_mem_range σ σ a 0 Λ hΛ (fun _ => le_rfl) δ hδ
    (fun i => by simpa only [zero_add] using hδσ i) _ hc P.upper P.lower hb P.lower_pos
    (fun p => (profile_bounds P Λ u d (0, p)).1) d

/-- Exact bounded-Borel transfer for the actual controlled mean and
profile in every finite observation dimension. All range applicability is
discharged, including singular collision configurations. -/
theorem integral_actual_controlled_mean (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (σ : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (hσ : ∀ i, 0 < σ i) (hσh : ∀ i, σ i ≤ P.horizon) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hbound : ∀ z, |F z| ≤ M)
    (r s : ℝ) :
    let A := fun θ => stoppedCovariance σ σ (nativeCenter a) (fun p => profile P Λ u d (θ, p)) 0
    let D := dampedDirection σ σ a 0 Λ d
    let mark := fun θ => stoppedBorelCovarianceMark P Λ σ σ (nativeCenter a) u d 0 F θ (meanVector Λ σ a u d θ) +
      (∫ y, F (meanVector Λ σ a u d θ + y) * MeasurableGaussianScores.firstScore (A θ) D y
        ∂multivariateGaussian 0 (A θ))
    IntervalIntegrable mark volume r s ∧
      (∫ θ in r..s, mark θ) = gaussianAverage (A s) F (meanVector Λ σ a u d s) -
        gaussianAverage (A r) F (meanVector Λ σ a u d r) := by
  have hh := integral_stopped_borel_affine P hΛ σ σ (nativeCenter a) hσ hσh (fun _ => le_rfl)
    u d (by norm_num : 0 ≤ (0 : ℝ)) hsmallPoint F hF M hbound
    (currentDirection σ a 0 u) (dampedDirection σ σ a 0 Λ d)
    (direction_mem_range P hΛ σ a hσ u d) r s
  dsimp only [ProfileReserve.affineMeanMark] at hh
  simpa only [← meanVector_affine] using hh

end SHE.ControlledObservationTransfer
