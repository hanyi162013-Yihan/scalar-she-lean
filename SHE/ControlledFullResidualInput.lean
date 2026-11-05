module

public import SHE.CoveredOldResidualCovariance
public import SHE.FutureResidualScoreInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.ControlledResidualScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays ControlledOldIntervals
  ProfileL2 MeasurableGaussianScores CoveredHistoryGeometry CoveredControlledLaw
local instance controlledFullResidualInput_periodPos : Fact (0<2*π) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {X : Type} [MeasurableSpace X] {n : ℕ}

/-- The exact physical signed-input mass in the all-order covariance
mark is the full-future one-input field already bounded analytically.
Every old fraction, original target, and covered stop is retained. -/
theorem full_residual_input_eq_ae (P : CanonicalCovariance.ProfileParameters)
    (ha : SmoothCylinders.BoundedSmooth P.coefficient) (Λ : ℝ) (u d : CircleL2) (θ : ℝ)
    (L : Level (ControlledWordLevel.referenceData P ha Λ u d θ) X n)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure (ControlledWordLevel.referenceData P ha Λ u d θ) μ k,
      ∀ q : ℝ,0≤q → q≤(carrier L k).terminal p → ∀ e : Domain→ℝ,
      (∫ r,|e r| *scoreVariance
        (fullResidualCovariance L (referenceProfile P Λ u d) k p q)
        (stoppedRow (stops L k p) (targets L k p) (centers L k p) r)
          ∂StoppedGaussianFeatures.historyMeasure q)=
      futureInput (stops L k p) (targets L k p) (centers L k p)
        (fun r=>ControlledProfile.profile P Λ u d (θ,r)-
          fixedProfile P Λ u d (lower L k p) (upper L k p) r) e q 0 := by
  filter_upwards [CoveredControlledLaw.full_residual_eq_fixedReserve_ae P ha Λ u d θ L hages μ k]
    with p hp
  intro q hq hqt e
  rw [hp q hq hqt]
  simp only [futureInput,add_zero,ControlledFixedReserve.covariance,ControlledFixedReserve.coefficient]
  rfl

end SHE.ControlledResidualScoreInput
