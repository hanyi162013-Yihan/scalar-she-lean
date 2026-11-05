module

public import SHE.ControlledProfileReserve
public import SHE.ProfileReserveTotalMark

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledProfile
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier ProfileVariance
  StoppedGaussianFeatures StoppedProfileMark GaussianProfileMark GaussianRangeSmooth
  GaussianConvolution ProfileParameter ProfilePointwise ProfileStability MeasurableGaussianScores
open scoped MatrixOrder Matrix.Norms.L2Operator NNReal Topology
local instance controlledProfileTransfer_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters)

/-- The literal covariance mark, with full individually stopped rows. -/
def stoppedBorelCovarianceMark {n : ℕ} (Λ : ℝ) (σ target : Fin n → ℝ)
    (center : Fin n → HeatCircle) (u d : CircleL2) (q : ℝ)
    (F : WordRecursion.State n → ℝ) (θ : ℝ) (z : WordRecursion.State n) : ℝ :=
  (1 / 2 : ℝ) * ∫ p : Domain, derivative P Λ u d (p, θ) *
    (∫ y, F (z + y) * secondScore
      (stoppedCovariance σ target center (fun p => profile P Λ u d (θ, p)) q)
      (stoppedRow σ target center p) y
      ∂multivariateGaussian 0
        (stoppedCovariance σ target center (fun p => profile P Λ u d (θ, p)) q))
    ∂historyMeasure q

/-- The actual controlled profile yields an exact finite-dimensional
endpoint transfer, including the physical mean and covariance scores.
No smoothness of the bounded Borel test is assumed. -/
theorem integral_stopped_borel_affine {n : ℕ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσh : ∀ i, σ i ≤ P.horizon)
    (hages : ∀ i, σ i ≤ target i) (u d : CircleL2) {q : ℝ} (hq : 0 ≤ q)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    (F : WordRecursion.State n → ℝ) (hF : Measurable F) (M : ℝ)
    (hbound : ∀ z, |F z| ≤ M) (base D : WordRecursion.State n)
    (hD : D ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (stoppedCovariance σ target center (fun p => profile P Λ u d (0, p)) q)).range)
    (a b : ℝ) :
    let A := fun θ => stoppedCovariance σ target center (fun p => profile P Λ u d (θ, p)) q
    let mark := fun θ => stoppedBorelCovarianceMark P Λ σ target center u d q F θ (base + θ • D) +
      ProfileReserve.affineMeanMark A F base D θ
    IntervalIntegrable mark volume a b ∧
      (∫ θ in a..b, mark θ) = gaussianAverage (A b) F (base + b • D) -
        gaussianAverage (A a) F (base + a • D) := by
  obtain ⟨Q, K, hK⟩ := exists_stopped_profile_reserve P hΛ σ target center hσ hσh hages u d hq hsmallPoint
  have hc := ae_stopped_borel_gaussian_mark_all_means P hΛ σ target center hσ hσh hages
    u d hq hsmallPoint F hF M hbound
  exact Q.integral_affine_total hK F hF M hbound base D hD
    (stoppedBorelCovarianceMark P Λ σ target center u d q F) hc a b

end SHE.ControlledProfile
