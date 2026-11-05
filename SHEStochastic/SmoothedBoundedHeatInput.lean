module

public import SHEStochastic.BoundedHeatCoefficientLift
public import SHEStochastic.HeatRowInputIntegration
public import SHEStochastic.HeatRowSpatialAveraging
public import SHEStochastic.PhysicalHeatKernelMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.SmoothedBoundedHeatInput
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle
open HeatParameterPullback
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

/-- Smooth an actual native heat input by any positive heat age. Only
its integration time lies in the native horizon; the future heat target
need not lie in that horizon. -/
def input (T δ : ℝ≥0) (hT : T ≤ H) (hT1 : (T : ℝ) ≤ 1) (hδ : 0 < δ) (x : HeatCircle) :
    Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H :=
  ∫ a : HeatCircle, BoundedHeatCoefficientLift.input F U hU hG hβ hβ1 B hb μ H T hT hT1 a
    ∂PhysicalHeatKernelMeasure.measure δ hδ x

/-- The averaged input has the literal future-target representative,
with the ORIGINAL causal integration cutoff T. -/
theorem input_ae_trim (T δ : ℝ≥0) (hT : T ≤ H) (hT1 : (T : ℝ) ≤ 1) (hδ : 0 < δ) (x : HeatCircle) :
    input F U hU hG hβ hβ1 B hb μ H T δ hT hT1 hδ x =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
      fun p ↦ if p.1 < T then BoundedHeatCoefficientLift.family F U hU hG hβ hβ1 B (T+δ) x p else 0 := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have ha := HeatRowInputIntegration.integral_ae_trim F (BoundedHeatCoefficientLift.field U hG hβ hβ1)
    (BoundedHeatCoefficientLift.predictable F U hU hG hβ hβ1)
    (BoundedHeatCoefficientLift.projection_holder B) (by norm_num) (by norm_num) μ H
    (Filter.Eventually.of_forall (BoundedHeatCoefficientLift.norm_bound U hG hβ hβ1 B hb))
    (⟨T, T.property, hT1⟩ : ShortTime) hT (PhysicalHeatKernelMeasure.measure δ hδ x)
  filter_upwards [ha] with p hp
  refine hp.trans ?_
  rw [PhysicalHeatKernelMeasure.integral]
  change (∫ a : HeatCircle, RealCausalHeatKernel.value x δ a •
    BoundedHeatCoefficientLift.family F U hU hG hβ hβ1 B T a p ∂haarAddCircle) = _
  exact HeatRowSpatialAveraging.spatial_average F
    (BoundedHeatCoefficientLift.field U hG hβ hβ1)
    (BoundedHeatCoefficientLift.predictable F U hU hG hβ hβ1)
    (BoundedHeatCoefficientLift.projection_holder B) (by norm_num) (by norm_num) T δ hδ x p

theorem input_ae (T δ : ℝ≥0) (hT : T ≤ H) (hT1 : (T : ℝ) ≤ 1) (hδ : 0 < δ) (x : HeatCircle) :
    input F U hU hG hβ hβ1 B hb μ H T δ hT hT1 hδ x =ᵐ[energyMeasure μ H]
      fun p ↦ if p.1 < T then BoundedHeatCoefficientLift.family F U hU hG hβ hβ1 B (T+δ) x p else 0 :=
  ae_eq_of_ae_eq_trim (input_ae_trim F U hU hG hβ hβ1 B hb μ H T δ hT hT1 hδ x)

/-- This is the actual spatial coefficient-times-heat-kernel row,
including its exact causal cutoff. It holds for scalar or Hilbert noise. -/
theorem spatial_ae (T δ : ℝ≥0) (hT : T ≤ H) (hT1 : (T : ℝ) ≤ 1) (hδ : 0 < δ) (x : HeatCircle) :
    ∀ᵐ p ∂energyMeasure μ H, input F U hU hG hβ hβ1 B hb μ H T δ hT hT1 hδ x p =ᵐ[haarAddCircle]
      fun y ↦ if p.1 < T then RealCausalHeatKernel.value x ((T+δ : ℝ≥0)-(p.1 : ℝ)) y • G (U p y) else 0 := by
  filter_upwards [input_ae F U hU hG hβ hβ1 B hb μ H T δ hT hT1 hδ x] with p hp
  rw [hp]
  by_cases ht : p.1 < T
  · simpa only [if_pos ht] using BoundedHeatCoefficientLift.family_ae F U hU hG hβ hβ1 B hb (T+δ) x p
  · rw [if_neg ht]
    filter_upwards [Lp.coeFn_zero V 2 (haarAddCircle (T := 2 * Real.pi))] with y hy
    simpa only [if_neg ht, Pi.zero_apply] using hy

end SHEStochastic.SmoothedBoundedHeatInput
