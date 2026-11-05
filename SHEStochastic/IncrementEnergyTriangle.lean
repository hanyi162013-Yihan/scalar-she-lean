module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.IncrementEnergyTriangle
open MeasureTheory
open scoped ENNReal

theorem norm_sq {C : Type*} [NormedAddCommGroup C] (x y z : C) :
    ‖x - z‖ ^ 2 ≤ 2 * (‖x - y‖ ^ 2 + ‖y - z‖ ^ 2) := by
  have ht : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
    simpa only [dist_eq_norm] using dist_triangle x y z
  have hp := pow_le_pow_left₀ (norm_nonneg (x - z)) ht 2
  nlinarith [sq_nonneg (‖x - y‖ - ‖y - z‖)]

/-- Only one scalar energy needs to be measurable; this applies even
when the Hilbert-valued rows have no chosen ambient Borel structure. -/
theorem integrated {A C : Type*} [MeasurableSpace A] [NormedAddCommGroup C]
    (ν : Measure A) (f g h : A → C)
    (hm : Measurable (fun a ↦ ENNReal.ofReal (‖g a - h a‖ ^ 2))) :
    (∫⁻ a, ENNReal.ofReal (‖f a - h a‖ ^ 2) ∂ν) ≤
      2 * ((∫⁻ a, ENNReal.ofReal (‖f a - g a‖ ^ 2) ∂ν) +
        ∫⁻ a, ENNReal.ofReal (‖g a - h a‖ ^ 2) ∂ν) := by
  calc
    _ ≤ ∫⁻ a, (2 : ℝ≥0∞) * (ENNReal.ofReal (‖f a - g a‖ ^ 2) +
          ENNReal.ofReal (‖g a - h a‖ ^ 2)) ∂ν := by
      apply lintegral_mono
      intro a
      calc
        _ ≤ ENNReal.ofReal (2 * (‖f a - g a‖ ^ 2 + ‖g a - h a‖ ^ 2)) :=
          ENNReal.ofReal_le_ofReal (norm_sq _ _ _)
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]; norm_num
    _ = _ := by rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_right _ hm]

end SHEStochastic.IncrementEnergyTriangle
