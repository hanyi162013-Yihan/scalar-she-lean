module

public import SHE.PhysicalMeanRange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PhysicalMeanSemigroup
open MeasureTheory AddCircle StoppedFourier PhysicalProfile RealHeatCovarianceMean
open scoped InnerProductSpace
local instance physicalMeanSemigroup_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem heatMean_eq_real_inner {r : ℝ} (hr : 0 < r) (d : CircleL2) (x : HeatCircle) :
    physicalHeatMean d (r, x) = inner ℝ (circleHeat r x) d := by
  rw [physicalHeatMean_eq hr, real_inner_eq_complex_re]

theorem heatMean_add {r : ℝ} (hr : 0 < r) (d e : CircleL2) (x : HeatCircle) :
    physicalHeatMean (d + e) (r, x) = physicalHeatMean d (r, x) + physicalHeatMean e (r, x) := by
  simp only [heatMean_eq_real_inner hr, inner_add_right]

theorem heatMean_smul {r : ℝ} (hr : 0 < r) (d : CircleL2) (θ : ℝ) (x : HeatCircle) :
    physicalHeatMean (θ • d) (r, x) = θ * physicalHeatMean d (r, x) := by
  simp only [heatMean_eq_real_inner hr, real_inner_smul_right]

/-- The literal physical heat mean obeys the exact semigroup identity. -/
theorem heatMean_heat {r q : ℝ} (hr : 0 < r) (hq : 0 ≤ q) (d : CircleL2) (x : HeatCircle) :
    physicalHeatMean (circleHeatOperator q hq d) (r, x) = physicalHeatMean d (q + r, x) := by
  rw [physicalHeatMean_eq hr, physicalHeatMean_eq (by linarith : 0 < q + r),
    ← circleHeatOperator_self_adjoint, circleHeatOperator_heat hq hr]

end SHE.PhysicalMeanSemigroup
