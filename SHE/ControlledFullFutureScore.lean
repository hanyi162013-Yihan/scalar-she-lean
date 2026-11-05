module

public import SHE.FullFutureWeightedScore
public import SHE.ControlledOldIntervals

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.ControlledFixedReserve
open Set Filter MeasureTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  GaussianIncrement MeasurableGaussianScores WordRecursion StopWeightedRows
open scoped BigOperators
local instance controlledFullFutureScore_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n : ℕ}

/-- Removing a fixed old profile of at most half the ellipticity floor
leaves the exact full-future stop-weighted score envelope, uniformly in
the interpolation parameter and damping strength. In particular, the
Gaussian range is the true full residual range, not a common front range. -/
theorem weighted_residual_sqrt_heat_envelope (n : ℕ) :
    ∃ H C : ℝ,0<H ∧ 0<C ∧
      ∀ (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ},0≤Λ →
      ∀ (u d : CircleL2) (old : ControlledProfile.Domain→ℝ),Measurable old →
      (∀ p,0≤old p ∧ old p≤P.lower/2) →
      ∀ (Z : Fin n→Observation),(∀ i,(Z i).stop≤(Z i).target) →
      ∀ {q r hi : ℝ},0≤q → q≤r → r<hi →
      (∀ i,hi≤(Z i).stop) → (∀ i,(Z i).target-r≤H) →
      ∀ θ : ℝ,∀ᵐ y : HeatCircle ∂haarAddCircle,
        weightedHeatRow Λ Z q r y∈
          (Matrix.toEuclideanCLM (𝕜:=ℝ) (covariance P Λ u d old
            (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) q θ)).range ∧
        sqrt (scoreVariance (covariance P Λ u d old
          (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) q θ)
          (weightedHeatRow Λ Z q r y))≤
          sqrt (2*C/(P.lower*(hi-r)))*
            ∑ i,sqrt ‖ProfileVariance.heatPhysical (4*((Z i).target-r)) (Z i).center y‖ := by
  obtain ⟨H,C,hH,hC,hV⟩ := FullFutureDampedHeat.weighted_sqrt_heat_envelope n
  refine ⟨H,C,hH,hC,?_⟩
  intro P Λ hΛ u d old hold hb Z hages q r hi hq hqr hrhi hstop hsmall θ
  have hc : Measurable (coefficient P Λ u d old θ) :=
    ((ControlledProfile.profile_measurable P Λ u d).comp
      (measurable_const.prodMk measurable_id)).sub hold
  have he : 0<P.lower/2 := half_pos P.lower_pos
  have hcb (p : ControlledProfile.Domain) :
      P.lower/2≤coefficient P Λ u d old θ p ∧ coefficient P Λ u d old θ p≤P.upper := by
    have hh := coefficient_bounds P Λ u d old hb θ p
    constructor <;> linarith
  have hv := hV Z hages hq hqr hrhi hΛ hstop hsmall _ hc he hcb
  have hcoef : C/((P.lower/2)*(hi-r))=2*C/(P.lower*(hi-r)) := by
    field_simp [P.lower_pos.ne',(sub_pos.mpr hrhi).ne']
    <;> ring
  simpa only [covariance,hcoef] using hv

end SHE.ControlledFixedReserve
