module

public import SHE.StandardTerminalBDGPower

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.BDGSecondMoment
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

/-- The second-moment base of the BDG induction is precisely the
already constructed Hilbert Itô isometry, with constant one. -/
theorem power_one {Ω C E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
    (I : StandardTerminalIto (C := C) (E := E) F μ H) :
    StandardTerminalBDGPower 1 I 1 := by
  intro u
  simp only [mul_one, pow_one, ENNReal.coe_one, one_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal (Lp.memLp (I.integral u)).norm.integrable_sq
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _), ← realLp_norm_sq]
  rw [I.isometry_energy]
  exact le_of_eq (lintegral_lintegral_swap
    ((memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).aestronglyMeasurable.norm.pow 2
      |>.aemeasurable.ennreal_ofReal))

end SHEStochastic.BDGSecondMoment
