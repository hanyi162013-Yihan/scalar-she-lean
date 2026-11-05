module

public import SHE.PredictableTime
public import SHE.JointInterpolationFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ScalarTimeZeroExtension
open Set MeasureTheory DyadicApproximation PredictableL2
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]

def extend (H : ℝ≥0) (D : ℝ≥0×Ω→ℝ) (z : ℝ×Ω) : ℝ :=
  (Ioc (0:ℝ) (H:ℝ)).indicator (fun r=>D (r.toNNReal,z.2)) z.1

theorem measurable (H : ℝ≥0) (D : ℝ≥0×Ω→ℝ) (hD : Measurable D) : Measurable (extend H D):=by
  have hm:=hD.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  exact hm.ite (measurableSet_Ioc.preimage measurable_fst) measurable_const

/-- The actual scalar negative-input RMS extends to the real translation clock
with EXACTLY its original integrated energy. -/
theorem energy (H : ℝ≥0) (D : ℝ≥0×Ω→ℝ) (hD : Measurable D)
    (hi : Integrable (fun z=>‖D z‖^2) ((timeMeasure H).prod μ)) :
    Integrable (fun z=>‖extend H D z‖^2) ((volume : Measure ℝ).prod μ) ∧
      (∫z,‖extend H D z‖^2 ∂((volume : Measure ℝ).prod μ))=
        (∫z,‖D z‖^2 ∂((timeMeasure H).prod μ)) := by
  have hm:Measurable (fun z=>‖extend H D z‖^2):=((measurable H D hD).norm.pow_const 2)
  have hn:Measurable (fun z=>‖D z‖^2):=hD.norm.pow_const 2
  have he : (∫⁻z,ENNReal.ofReal (‖extend H D z‖^2) ∂((volume : Measure ℝ).prod μ))=
      (∫⁻z,ENNReal.ofReal (‖D z‖^2) ∂((timeMeasure H).prod μ)) := by
    rw [show (∫⁻z,ENNReal.ofReal (‖extend H D z‖^2) ∂((volume : Measure ℝ).prod μ))=
      (∫⁻r,∫⁻ω,ENNReal.ofReal (‖extend H D (r,ω)‖^2) ∂μ) from
        lintegral_prod _ (by exact (ENNReal.measurable_ofReal.comp hm).aemeasurable),
      show (∫⁻z,ENNReal.ofReal (‖D z‖^2) ∂((timeMeasure H).prod μ))=
      (∫⁻r,∫⁻ω,ENNReal.ofReal (‖D (r,ω)‖^2) ∂μ ∂timeMeasure H) from
        lintegral_prod _ (by exact (ENNReal.measurable_ofReal.comp hn).aemeasurable),timeMeasure_lintegral]
    have hpoint (r : ℝ) : (∫⁻ω,ENNReal.ofReal (‖extend H D (r,ω)‖^2) ∂μ)=
        (Ioc (0:ℝ) (H:ℝ)).indicator (fun t=>∫⁻ω,ENNReal.ofReal (‖D (t.toNNReal,ω)‖^2) ∂μ) r := by
      by_cases hr:r∈Ioc (0:ℝ) (H:ℝ)
      · simp only [extend,indicator_of_mem hr]
      · simp only [extend,indicator_of_notMem hr,norm_zero,zero_pow (by decide : (2:ℕ)≠0),ENNReal.ofReal_zero,lintegral_zero]
    simp_rw [hpoint]
    exact lintegral_indicator measurableSet_Ioc _
  have hI:Integrable (fun z=>‖extend H D z‖^2) ((volume : Measure ℝ).prod μ):=by
    refine ⟨hm.aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _)),he]
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))).mp hi.hasFiniteIntegral
  refine ⟨hI,?_⟩
  calc
    _=(ENNReal.ofReal (∫z,‖extend H D z‖^2 ∂((volume : Measure ℝ).prod μ))).toReal:=
      (ENNReal.toReal_ofReal (integral_nonneg (fun _=>sq_nonneg _))).symm
    _=(ENNReal.ofReal (∫z,‖D z‖^2 ∂((timeMeasure H).prod μ))).toReal:=by
      rw [ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ (fun _=>sq_nonneg _)),
        ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _=>sq_nonneg _)),he]
    _=_:=ENNReal.toReal_ofReal (integral_nonneg (fun _=>sq_nonneg _))

end SHE.ScalarTimeZeroExtension
