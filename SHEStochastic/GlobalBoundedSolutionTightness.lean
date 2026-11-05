module

public import SHEStochastic.GlobalBoundedMildRecognition
public import SHEStochastic.GlobalBoundedHeatTightness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.GlobalBoundedSolutionTightness
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open StoppedPathPasting UnboundedNativeHeatEquation
open scoped NNReal ENNReal

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

include B hb in
/-- Actual weak solution paths are uniformly tight under a common
coefficient bound and one random initial law. Their Hölder seminorms
and Brownian realizations may vary with the approximation. -/
theorem tight (hH : 0 < H) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (ξ : Ω → RealL2) (hξ : Measurable ξ)
    (hEquation : ∀ k, UnboundedGlobalNativeEquation.RandomEquation F μ H (W k) (hW k) (hG k) hβ hβ1 (P k) e ξ) :
    IsTightMeasureSet (Set.range (fun k ↦ μ.map (NativeContinuousPath.path H (W k) (hcW k)))) := by
  obtain ⟨Y, hYm, hYrep, hYtight⟩ := GlobalBoundedHeatTightness.exists_tight_versions_varying F μ H
    (fun k ↦ physical (W k)) (fun k ↦ physical_predictable F (W k) (hW k))
    hG hβ hβ1.le B hb P e
  have he (k : ℕ) : NativeContinuousPath.path H (W k) (hcW k) =ᵐ[μ]
      fun sample ↦ GlobalHeatPathTightness.path H hH
        (ξ sample) (Y k sample) :=
    GlobalBoundedMildRecognition.path_eq F μ H (W k) (hW k) (hG k) hβ hβ1 B (hb k) (P k) e
      ξ hH (hcW k) hnull (hEquation k) (Y k) (hYm k) (hYrep k)
  have hm (k : ℕ) : μ.map (NativeContinuousPath.path H (W k) (hcW k)) =
      μ.map (fun sample ↦ GlobalHeatPathTightness.path H hH
        (ξ sample) (Y k sample)) := Measure.map_congr (he k)
  simpa only [hm] using GlobalHeatPathTightness.tight_random_initial μ ξ hξ Y hYm hYtight
    H hH

end SHEStochastic.GlobalBoundedSolutionTightness
