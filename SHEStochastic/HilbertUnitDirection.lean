module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HilbertUnitDirection
open MeasureTheory

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]

/-- A measurable unit direction, with a fixed unit vector filling the
zero case. Multiplication by the original norm recovers the original row. -/
def direction (v z : C) : C := by
  classical
  exact if z = 0 then v else ‖z‖⁻¹ • z

theorem norm_direction (v : C) (hv : ‖v‖ = 1) (z : C) : ‖direction v z‖ = 1 := by
  classical
  by_cases hz : z = 0
  · simp [direction, hz, hv]
  · rw [direction, if_neg hz, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

theorem recover (v z : C) : ‖z‖ • direction v z = z := by
  classical
  by_cases hz : z = 0
  · simp [direction, hz]
  · rw [direction, if_neg hz, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]

theorem measurable_direction (v : C) : Measurable (direction v) := by
  classical
  unfold direction
  exact Measurable.ite (measurableSet_singleton (0 : C)) measurable_const
    (measurable_norm.inv.smul measurable_id)

theorem stronglyMeasurable_direction {Ω : Type*} {m : MeasurableSpace Ω} {R : Ω → C}
    (hR : StronglyMeasurable R) (v : C) : StronglyMeasurable (fun ω ↦ direction v (R ω)) :=
  ((measurable_direction v).comp hR.measurable).stronglyMeasurable

end SHEStochastic.HilbertUnitDirection
