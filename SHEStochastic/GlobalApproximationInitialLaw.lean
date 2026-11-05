module

public import SHEStochastic.GlobalBoundedApproximationCompactness
public import SHEStochastic.NativeApproximationInitialLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.GlobalApproximationInitialLaw
open MeasureTheory ProbabilityTheory Filter SHE SHE.DyadicApproximation
open StoppedPathPasting NativeApproximationInitialLaw
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω ι : Type*} [Countable ι] [MeasurableSpace Ω] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℕ → ℝ≥0 → Ω → RealL2)
  (hcW : ∀ k sample, Continuous (fun t ↦ W k t sample))
  (hW : ∀ k, StronglyMeasurable[F.predictable] (Function.uncurry (W k)))
  (P : ℕ → FiniteScalarIto.Family F μ H ι)

include hW in
/-- The actual joint weak limit keeps the given random initial state
law and starts every centered driver at zero. -/
theorem preserved (ξ : Ω → RealL2) (hξ : Measurable ξ)
    (hInitial : ∀ k, W k 0 =ᵐ[μ] ξ)
    (Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := RealL2) (ι := ι) H))
    (φ : ℕ → ℕ)
    (hlim : Tendsto ((GlobalBoundedApproximationCompactness.laws F μ H W hcW P) ∘ φ) atTop (𝓝 Q)) :
    (Q : Measure _).map (initial H) = μ.map (fun sample ↦ (ξ sample, fun _ : ι ↦ (0 : ℝ))) :=
  CanonicalInitialLaw.preserved F μ H W hcW hW P ξ hξ hInitial Q φ hlim

end SHEStochastic.GlobalApproximationInitialLaw
