module

public import SHE.PredictableTime

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.PredictableL2
open MeasureTheory Set
open scoped NNReal ENNReal

theorem timeMeasure_mass (h : ℝ≥0) : timeMeasure h univ=ENNReal.ofReal (h:ℝ) := by
  have he := congrArg (fun μ : Measure ℝ => μ univ) (timeMeasure_map h)
  rw [Measure.map_apply measurable_coe_nnreal_real MeasurableSet.univ] at he
  simpa only [preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc,
    sub_zero] using he

theorem timeMeasure_one_integral (h : ℝ≥0) : (∫⁻ _ : ℝ≥0,(1:ℝ≥0∞) ∂timeMeasure h)=ENNReal.ofReal (h:ℝ) := by
  rw [lintegral_const,one_mul,timeMeasure_mass]

end SHE.PredictableL2
