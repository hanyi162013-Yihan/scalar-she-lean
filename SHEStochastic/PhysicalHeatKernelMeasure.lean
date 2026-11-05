module

public import SHEStochastic.RealCausalHeatKernel
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.PhysicalHeatKernelMeasure
open MeasureTheory SHE SHE.StoppedFourier AddCircle Filter
open scoped ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem nonneg {r : ℝ} (hr : 0 < r) (x a : HeatCircle) :
    0 ≤ RealCausalHeatKernel.value x r a := by
  rw [RealCausalHeatKernel.eq_norm hr]
  exact norm_nonneg _

/-- The literal positive physical heat-kernel weight as a probability
measure. Its mass is exactly one under normalized physical Haar measure. -/
def measure (r : ℝ) (_hr : 0 < r) (x : HeatCircle) : Measure HeatCircle :=
  haarAddCircle.withDensity (fun a ↦ ENNReal.ofReal (RealCausalHeatKernel.value x r a))

instance probability (r : ℝ) (hr : 0 < r) (x : HeatCircle) : IsProbabilityMeasure (measure r hr x) := by
  constructor
  rw [measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hi : Integrable (RealCausalHeatKernel.value x r) haarAddCircle :=
    (RealCausalHeatKernel.value x r).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (nonneg hr x)),
    RealCausalHeatKernel.integral_one hr]
  simp

/-- Heat-weighted integration uses the ordinary Bochner integral in any
real normed space; no extra spatial integration convention is introduced. -/
theorem integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : ℝ) (hr : 0 < r) (x : HeatCircle) (g : HeatCircle → V) :
    (∫ a, g a ∂measure r hr x) =
      ∫ a : HeatCircle, RealCausalHeatKernel.value x r a • g a ∂haarAddCircle := by
  rw [measure, integral_withDensity_eq_integral_toReal_smul
    (RealCausalHeatKernel.value x r).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun a ↦ by
    change (ENNReal.ofReal (RealCausalHeatKernel.value x r a)).toReal • g a = _
    rw [ENNReal.toReal_ofReal (nonneg hr x a)]

end SHEStochastic.PhysicalHeatKernelMeasure
