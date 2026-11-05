module

public import SHEStochastic.NativeBoundedApproximationCompactness
public import SHEStochastic.CanonicalInitialLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.NativeApproximationInitialLaw
open MeasureTheory ProbabilityTheory Filter SHE SHE.DyadicApproximation
open StoppedPathPasting
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {ι : Type*} [Countable ι]

def initial (H : ℝ≥0) (x : CanonicalContinuousStateDriver.Space (E := RealL2) (ι := ι) H) :
    RealL2 × (ι → ℝ) := (x.1 (origin H), fun i => x.2 i (origin H))

theorem continuous_initial (H : ℝ≥0) : Continuous (initial (ι := ι) H) :=
  CanonicalInitialLaw.continuous_initial H

variable {Ω : Type*} [MeasurableSpace Ω] [DecidableEq ι]
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
    (Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := RealL2) (ι := ι) (min H 1)))
    (φ : ℕ → ℕ)
    (hlim : Tendsto ((NativeBoundedApproximationCompactness.laws F μ H W hcW P) ∘ φ) atTop (𝓝 Q)) :
    (Q : Measure _).map (initial (min H 1)) = μ.map (fun sample ↦ (ξ sample, fun _ : ι ↦ (0 : ℝ))) := by
  letI : MetricSpace (ι → ℝ) := TopologicalSpace.metrizableSpaceMetric _
  let Z : Ω → RealL2 × (ι → ℝ) := fun sample ↦ (ξ sample, fun _ ↦ 0)
  have hZ : Measurable Z := hξ.prodMk measurable_const
  apply (WeakLimitProbabilityTools.hasLaw
    ((NativeBoundedApproximationCompactness.laws F μ H W hcW P) ∘ φ) Q hlim
    (initial (min H 1)) (continuous_initial _) (μ.map Z) ?_).map_eq
  intro k
  let R := NativeHorizonRestriction.family (P (φ k)) (min H 1) (min_le_left _ _)
  have ha (t : ℝ≥0) : Measurable[F t] (W (φ k) t) :=
    ((show IsStronglyPredictable F (W (φ k)) from hW (φ k)).stronglyAdapted t).measurable
  refine ⟨(continuous_initial _).measurable.aemeasurable, ?_⟩
  change (μ.map (CanonicalNativeBrownian.bundle F μ (min H 1) R (W (φ k)) (hcW (φ k)))).map
    (initial (min H 1)) = μ.map Z
  rw [Measure.map_map (continuous_initial _).measurable
    (CanonicalNativeBrownian.measurable_bundle F μ (min H 1) R (W (φ k)) (hcW (φ k)) ha)]
  apply Measure.map_congr
  filter_upwards [hInitial (φ k)] with sample hs
  change (W (φ k) (0+(origin (min H 1)).val.toNNReal) sample,
      fun i ↦ (P (φ k)).W i (0+(origin (min H 1)).val.toNNReal) sample - (P (φ k)).W i 0 sample) =
    (ξ sample, fun _ : ι ↦ 0)
  simp only [origin, Real.toNNReal_zero, zero_add, hs, sub_self]

end SHEStochastic.NativeApproximationInitialLaw
