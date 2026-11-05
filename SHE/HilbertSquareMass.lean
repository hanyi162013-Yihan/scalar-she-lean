module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.HilbertSquareMass
open MeasureTheory
open scoped ENNReal
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A bound for the genuine positive square mass supplies both L2
integrability and the real integral estimate, without normalizing the
parameter measure. -/
theorem of_lintegral_bound (μ : Measure X) (f : X→E) (hf : Measurable f) (C : ℝ)
    (hb : (∫⁻ x,ENNReal.ofReal (‖f x‖^2) ∂μ)≤ENNReal.ofReal C) :
    Integrable (fun x=>‖f x‖^2) μ ∧ (∫ x,‖f x‖^2 ∂μ)≤max C 0 := by
  have hm : Measurable (fun x=>‖f x‖^2):=hf.norm.pow_const 2
  have hi : Integrable (fun x=>‖f x‖^2) μ := by
    refine ⟨hm.aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x=>sq_nonneg ‖f x‖))]
    exact hb.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (le_max_right C 0)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x=>sq_nonneg ‖f x‖))]
  exact hb.trans (ENNReal.ofReal_le_ofReal (le_max_left C 0))

end SHE.HilbertSquareMass
