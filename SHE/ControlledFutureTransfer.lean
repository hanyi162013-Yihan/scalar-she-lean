module

public import SHE.ControlledFutureMeans

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledFutureTransfer
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore GaussianIncrement GaussianRangeSmooth GaussianConvolution
  ProfilePointwise ProfileStability PhysicalMeanRange ControlledProfile ControlledFutureMeans
open scoped InnerProductSpace Matrix.Norms.L2Operator
local instance controlledFutureTransfer_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

/-- The exact physical current-plus-old future direction satisfies the
actual controlled-profile covariance range condition. -/
theorem actual_future_direction_mem_range (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (q : ℝ) (hq : 0 ≤ q) (hgap : ∀ i, q < target i) (u d D : CircleL2) :
    futureDirection Λ target a q hq d D ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (stoppedCovariance target target (nativeCenter a) (fun p => profile P Λ u d (0, p)) q)).range := by
  obtain ⟨δ, hδ, hs⟩ := exists_positive_gap (fun i => target i - q) (fun i => sub_pos.mpr (hgap i))
  have hc : Measurable (fun p => profile P Λ u d (0, p)) :=
    (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hb (p : ControlledProfile.Domain) : 0 ≤ profile P Λ u d (0, p) ∧ profile P Λ u d (0, p) ≤ P.upper :=
    ⟨P.lower_pos.le.trans (profile_bounds P Λ u d (0, p)).1, (profile_bounds P Λ u d (0, p)).2⟩
  exact futureDirection_mem_range Λ hΛ target a q hq δ hδ (fun i => by linarith [hs i])
    _ hc P.upper P.lower hb P.lower_pos (fun p => (profile_bounds P Λ u d (0, p)).1) d D

/-- Exact endpoint transfer with the manuscript's actual conditional
future mean. The current states are arbitrary physical L2 states; neither
compatibility with a Gaussian law nor a surrogate current input is assumed. -/
theorem integral_actual_future_mean (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (q : ℝ) (hq : 0 ≤ q) (hgap : ∀ i, q < target i)
    (hTh : ∀ i, target i ≤ P.horizon) (u d Z D : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hbound : ∀ z, |F z| ≤ M)
    (r s : ℝ) :
    let A := fun θ => stoppedCovariance target target (nativeCenter a) (fun p => profile P Λ u d (θ, p)) q
    let E := futureDirection Λ target a q hq d D
    let m := futureMeanVector Λ target a q hq u d Z D
    let mark := fun θ => stoppedBorelCovarianceMark P Λ target target (nativeCenter a) u d q F θ (m θ) +
      (∫ y, F (m θ + y) * MeasurableGaussianScores.firstScore (A θ) E y
        ∂multivariateGaussian 0 (A θ))
    IntervalIntegrable mark volume r s ∧
      (∫ θ in r..s, mark θ) = gaussianAverage (A s) F (m s) - gaussianAverage (A r) F (m r) := by
  have hT : ∀ i, 0 < target i := fun i => lt_of_le_of_lt hq (hgap i)
  have hh := integral_stopped_borel_affine P hΛ target target (nativeCenter a) hT hTh (fun _ => le_rfl)
    u d hq hsmallPoint F hF M hbound (currentDirection target a q Z)
    (futureDirection Λ target a q hq d D)
    (actual_future_direction_mem_range P hΛ target a q hq hgap u d D) r s
  dsimp only [ProfileReserve.affineMeanMark] at hh
  simpa only [← futureMeanVector_affine Λ target a q hq hgap u d Z D] using hh

end SHE.ControlledFutureTransfer
