module

public import SHEStochastic.BoundedFourierMildRecognition
public import SHEStochastic.BoundedHeatStoppedLocality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.BoundedMildHeatEquation
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open UnboundedNativeHeatEquation BoundedHeatCoefficientLift
open HeatParameterCover HeatParameterCoordinates
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B) (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

/-- A native bounded-coefficient mild solution satisfies the original
localized positive-heat equation with exactly the same Brownian integral. -/
theorem equation (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (ξ : Ω → RealL2)
    (hMild : BoundedFourierMildRecognition.HasClosedVersion F μ H W hW hG hβ hβ1 B hb
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) ξ) :
    RandomEquation F μ H W hW hG hβ hβ1 P e ξ := by
  obtain ⟨Y, hm, he, hs⟩ := hMild
  intro N T δ hTH hT hδ hTD hTD1 x
  have ho := NativeRemainderObservation.stochastic_observation F (field (physical W) hG hβ hβ1.le)
    (predictable F (physical W) (physical_predictable F W hW) hG hβ hβ1.le)
    (projection_holder B) (by norm_num) (by norm_num) μ H
    (Filter.Eventually.of_forall (norm_bound (physical W) hG hβ hβ1.le B hb))
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) T δ hTH hT hδ hTD hTD1 x
    (fun p sample ↦ Y sample p) (fun p ↦ (ContinuousMap.measurable_eval p).comp hm)
    (fun sample ↦ (Y sample).continuous) he
  have hl := BoundedHeatStoppedLocality.integral_agrees F (physical W) (physical_predictable F W hW)
    hG hβ hβ1 B hb μ H (physical_continuous W hcW) N (T+δ) hTD hTD1 x T P e hnull
  filter_upwards [hs, ho, hl] with sample hs ho hl hbefore
  have hheat := NativeHeatObservation.functional_heat (show (0 : ℝ) < δ from hδ)
    (show (0 : ℝ) ≤ T from T.2) x (ξ sample)
  have heq := (congrArg (NativeHeatObservation.functional δ x) (hs T hTH hT)).trans
    ((map_add (NativeHeatObservation.functional δ x) _ _).trans (congrArg₂ (·+·) hheat ho))
  have hsum : (δ : ℝ)+(T : ℝ) = ((T+δ : ℝ≥0) : ℝ) := by push_cast; ring
  rw [hsum] at heq
  exact heq.trans (congrArg (fun z : ℝ ↦ NativeHeatObservation.functional (T+δ) x (ξ sample)+z)
    (hl hbefore.le).symm)

end SHEStochastic.BoundedMildHeatEquation
