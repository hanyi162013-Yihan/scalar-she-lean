module

public import SHE.IntervalScoreHeatKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.UniformScoreConstants
open Set Filter MeasureTheory AddCircle StoppedFourier StoppedGaussianFeatures StoppedGaussianScore
local instance uniformScoreConstants_periodPos : Fact (0<2*Real.pi) := ⟨by positivity⟩
open scoped BigOperators

/-- Chosen ONCE per dimension, before every profile, reference,
interpolation parameter, observation geometry and recursive level. -/
def horizon (n : ℕ) : ℝ := Classical.choose (IntervalScoreEnvelope.score_heat_kernel n)

def constant (n : ℕ) : ℝ := Classical.choose (Classical.choose_spec
  (IntervalScoreEnvelope.score_heat_kernel n))

theorem horizon_pos (n : ℕ) : 0<horizon n :=
  (Classical.choose_spec (Classical.choose_spec (IntervalScoreEnvelope.score_heat_kernel n))).1

theorem constant_pos (n : ℕ) : 0<constant n :=
  (Classical.choose_spec (Classical.choose_spec (IntervalScoreEnvelope.score_heat_kernel n))).2.1

/-- The genuine collision-uniform physical heat estimate with global
dimensional witnesses. No analytic estimate is introduced as a premise. -/
theorem score_heat_kernel (n : ℕ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i≤target i) {lo hi ell M : ℝ}
    (hlo : 0≤lo) (hgap : lo<hi) (hstop : ∀ i,σ i≤lo ∨ hi≤σ i)
    (hsmall : ∀ i,hi≤σ i → target i-lo≤horizon n)
    (c : Domain→ℝ) (hc : Measurable c) (hell : 0<ell) (hb : ∀ p,ell≤c p ∧ c p≤M) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,
      MeasurableGaussianScores.scoreVariance
        (stoppedCovariance σ target center (OldIntervalCovariance.intervalProfile c lo hi) 0)
        (stoppedRow σ target center (lo,x))≤
        (constant n/(ell*(hi-lo)))*∑ i∈IntervalHistoryEnergy.active σ hi,
          ‖ProfileVariance.heatPhysical (2*(target i-lo)) (center i) x‖ :=
  (Classical.choose_spec (Classical.choose_spec (IntervalScoreEnvelope.score_heat_kernel n))).2.2
    σ target center hages hlo hgap hstop hsmall c hc hell hb

end SHE.UniformScoreConstants
