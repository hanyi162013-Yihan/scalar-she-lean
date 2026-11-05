module

public import SHEStochastic.NativeBoundedSolutionTightness
public import SHEStochastic.CanonicalApproximationCompactness
public import SHEStochastic.NativeHorizonRestriction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeBoundedApproximationCompactness
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open SHE.CanonicalStateDriverFiltration UnboundedNativeHeatEquation
open scoped NNReal ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℕ → ℝ≥0 → Ω → RealL2)
  (hcW : ∀ k sample, Continuous (fun t ↦ W k t sample))
  (hW : ∀ k, StronglyMeasurable[F.predictable] (Function.uncurry (W k)))
  {G : ℕ → ℝ → V} {C : ℕ → ℝ≥0} {β : ℝ≥0}
  (hG : ∀ k, HolderWith (C k) β (G k)) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ k z, ‖G k z‖ ≤ B)
  (P : ℕ → FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

def laws := CanonicalApproximationCompactness.varyingLaws F μ (min H 1) W hcW
  (fun k ↦ NativeHorizonRestriction.family (P k) (min H 1) (min_le_left _ _))

include B hb in
/-- Uniformly bounded native weak approximations with one random
initial law have an actual subsequential joint limit. Its retained
driver is Brownian in the entire canonical state/driver filtration. -/
theorem exists_limit (hH : 0 < H) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (ξ : Ω → RealL2) (hξ : Measurable ξ)
    (hEquation : ∀ k, RandomEquation F μ H (W k) (hW k) (hG k) hβ hβ1 (P k) e ξ) :
    ∃ Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := RealL2) (ι := ι) (min H 1)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto ((laws F μ H W hcW P) ∘ φ) atTop (𝓝 Q) ∧
        ∀ n (a : Fin n → ι), FiniteBrownianLawOn (filtration (E := RealL2) (ι := ι) (min H 1))
          (Q : Measure _) (min H 1) (fun i ↦ coordinate (min H 1) (a i))
          (fun i j ↦ if a i = a j then 1 else 0) := by
  have ht := NativeBoundedSolutionTightness.tight F μ H W hcW hW hG hβ hβ1 B hb P e hH hnull ξ hξ hEquation
  exact CanonicalApproximationCompactness.exists_limit_varying F μ (min H 1) W hcW
    (fun k t ↦ ((show IsStronglyPredictable F (W k) from hW k).stronglyAdapted t).measurable)
    (fun k ↦ NativeHorizonRestriction.family (P k) (min H 1) (min_le_left _ _)) ht

end SHEStochastic.NativeBoundedApproximationCompactness
