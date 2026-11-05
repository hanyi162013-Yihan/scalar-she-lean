module

public import SHEStochastic.UnboundedHeatInitialVersion
public import SHEStochastic.BallProjection
public import SHEStochastic.ContinuousNormExit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.UnboundedL2Localization
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (AddCircle.haarAddCircle (T := 2 * Real.pi)))

/-- Localization in the spatial L² state, rather than an assumed
pointwise bound on the coefficient or solution. -/
def state (R : ℝ≥0) (p : ℝ≥0 × Ω) : Lp E 2 (AddCircle.haarAddCircle (T := 2 * Real.pi)) :=
  BallProjection.project R (U p)

theorem predictable (hU : StronglyMeasurable[F.predictable] U) (R : ℝ≥0) :
    StronglyMeasurable[F.predictable] (state U R) :=
  (BallProjection.lipschitz R).continuous.comp_stronglyMeasurable hU

theorem norm_bound (R : ℝ≥0) (p : ℝ≥0 × Ω) : ‖state U R p‖ ≤ R :=
  BallProjection.norm_le_radius R (U p)

theorem agrees (R : ℝ≥0) {p : ℝ≥0 × Ω} (hp : ‖U p‖ ≤ R) : state U R p = U p :=
  BallProjection.of_norm_le R hp

theorem continuous (R : ℝ≥0) (hc : ∀ ω, Continuous (fun t ↦ U (t, ω))) (ω : Ω) :
    Continuous (fun t ↦ state U R (t, ω)) :=
  (BallProjection.lipschitz R).continuous.comp (hc ω)

/-- The history bound used by all heat-convolution estimates follows
from construction, for every original predictable state. -/
theorem history_bound (μ : Measure Ω) (H R : ℝ≥0) :
    ∀ᵐ p ∂energyMeasure μ H, ‖state U R p‖ ≤ (R : ℝ) :=
  Filter.Eventually.of_forall (norm_bound U R)

theorem exit_stopping (hU : StronglyMeasurable[F.predictable] U)
    (hc : ∀ ω, Continuous (fun t ↦ U (t, ω))) (N : ℕ) :
    IsStoppingTime F (ContinuousNormExit.exit (fun t ω ↦ U (t, ω)) N) :=
  ContinuousNormExit.isStoppingTime (fun t ω ↦ U (t, ω)) hc F
    (show IsStronglyPredictable F (fun t ω ↦ U (t, ω)) from hU).stronglyAdapted N

theorem agrees_before_exit (hc : ∀ ω, Continuous (fun t ↦ U (t, ω)))
    (N : ℕ) (p : ℝ≥0 × Ω)
    (hp : (p.1 : WithTop ℝ≥0) < ContinuousNormExit.exit (fun t ω ↦ U (t, ω)) N p.2) :
    state U (N : ℝ≥0) p = U p :=
  agrees U (N : ℝ≥0) (ContinuousNormExit.before_bound (fun t ω ↦ U (t, ω)) hc N p.1 p.2 hp).le

theorem exit_probability_vanishes (hU : StronglyMeasurable[F.predictable] U)
    (hc : ∀ ω, Continuous (fun t ↦ U (t, ω)))
    (μ : Measure Ω) [IsFiniteMeasure μ] (H : ℝ≥0) :
    Filter.Tendsto (fun N ↦ μ {ω | ContinuousNormExit.exit (fun t ω ↦ U (t, ω)) N ω ≤
      (H : WithTop ℝ≥0)}) Filter.atTop (nhds 0) :=
  ContinuousNormExit.probability_vanishes (fun t ω ↦ U (t, ω)) hc μ F
    (show IsStronglyPredictable F (fun t ω ↦ U (t, ω)) from hU).stronglyAdapted H

end SHEStochastic.UnboundedL2Localization
