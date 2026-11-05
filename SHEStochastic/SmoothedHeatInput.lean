module

public import SHEStochastic.HeatRowInputIntegration
public import SHEStochastic.HeatRowSpatialAveraging
public import SHEStochastic.PhysicalHeatKernelMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.SmoothedHeatInput
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter Set
open HeatParameterPullback UnboundedHeatFamily
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) {R : ℝ}
  (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)

/-- Heat smoothing of the actual predictable input equals the same
future-target row stopped at the original observation time. This is an
identity of Hilbert inputs, not a supplied stochastic Fubini hypothesis. -/
theorem average_eq_stopped (T δ : ℝ≥0) (hδ : 0 < δ)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (hTD : T + δ ≤ H) (hTD1 : ((T + δ : ℝ≥0) : ℝ) ≤ 1)
    (x : HeatCircle) :
    (∫ a : HeatCircle, input F U hU hG hβ hβ1 μ H T hTH hT a hbound
      ∂PhysicalHeatKernelMeasure.measure δ hδ x) =
      StoppedItoInputs.stop F μ H T (input F U hU hG hβ hβ1 μ H (T + δ) hTD hTD1 x hbound) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let t : ShortTime := ⟨T, T.property, hT⟩
  let v := input F U hU hG hβ hβ1 μ H (T + δ) hTD hTD1 x hbound
  have ha := HeatRowInputIntegration.integral_ae_trim F U hU hG hβ hβ1 μ H hbound t hTH
    (PhysicalHeatKernelMeasure.measure δ hδ x)
  have hs := StoppedInputParameter.stop_ae_trim F μ H v T
  have hv := (memLp F U hU hG hβ hβ1 μ H (T + δ) hTD hTD1 x hbound).coeFn_toLp
  apply Lp.ext
  filter_upwards [ha, hs, hv] with p hp hstop hvalue
  refine hp.trans ?_
  change (∫ a : HeatCircle, family F U hU hG hβ hβ1 T a p
    ∂PhysicalHeatKernelMeasure.measure δ hδ x) = StoppedItoInputs.stop F μ H T v p
  rw [PhysicalHeatKernelMeasure.integral, HeatRowSpatialAveraging.spatial_average F U hU hG hβ hβ1 T δ hδ x p,
    hstop]
  by_cases ht : p.1 < T
  · rw [if_pos ht, indicator_of_mem (show p ∈ StoppedItoInputs.before (T : ℝ) from ht)]
    exact hvalue.symm
  · rw [if_neg ht, indicator_of_notMem (show p ∉ StoppedItoInputs.before (T : ℝ) from ht)]

end SHEStochastic.SmoothedHeatInput
