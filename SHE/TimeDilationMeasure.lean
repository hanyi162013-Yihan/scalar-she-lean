module

public import SHE.PredictableTimeDilation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.PredictableTimeDilation
open MeasureTheory Set PredictableL2
open scoped NNReal ENNReal

theorem real_time_map (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0) :
    (volume.restrict (Ioc (0:ℝ) (h:ℝ))).map (fun t : ℝ => (c:ℝ)*t)=
      ENNReal.ofReal ((c:ℝ)⁻¹) • volume.restrict (Ioc (0:ℝ) ((c*h:ℝ≥0):ℝ)) := by
  have hcR : 0<(c:ℝ) := hc
  have hpre : (fun t : ℝ => (c:ℝ)*t) ⁻¹' Ioc (0:ℝ) ((c*h:ℝ≥0):ℝ)=Ioc 0 (h:ℝ) := by
    ext t
    simp only [mem_preimage,mem_Ioc,NNReal.coe_mul]
    constructor
    · intro ht
      exact ⟨(mul_pos_iff_of_pos_left hcR).mp ht.1,(mul_le_mul_iff_right₀ hcR).mp ht.2⟩
    · intro ht
      exact ⟨mul_pos hcR ht.1,mul_le_mul_of_nonneg_left ht.2 hcR.le⟩
  rw [← hpre,← Measure.restrict_map (measurable_const_mul (c:ℝ)) measurableSet_Ioc,
    Real.map_volume_mul_left hcR.ne',abs_of_pos (inv_pos.mpr hcR),Measure.restrict_smul]

/-- The exact finite Lebesgue clock-change measure. The Jacobian is
retained, including at the two zero-measure endpoints. -/
theorem timeMeasure_map_clock (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0) :
    (timeMeasure h).map (clock c hc)=
      ENNReal.ofReal ((c:ℝ)⁻¹) • timeMeasure (c*h) := by
  apply nonnegative_coe_measurableEmbedding.map_injective
  rw [Measure.map_map measurable_coe_nnreal_real (clock_continuous c hc).measurable,Measure.map_smul,
    timeMeasure_map]
  have he : (((↑) : ℝ≥0→ℝ) ∘ clock c hc)=
      (fun t : ℝ => (c:ℝ)*t)∘((↑) : ℝ≥0→ℝ) := rfl
  rw [he,← Measure.map_map (measurable_const_mul (c:ℝ)) measurable_coe_nnreal_real,
    timeMeasure_map,real_time_map c hc h]
  exact measurable_coe_nnreal_real.aemeasurable

theorem timeMeasure_clock_preserving (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0) :
    MeasurePreserving (clock c hc) (ENNReal.ofReal (c:ℝ) • timeMeasure h) (timeMeasure (c*h)) := by
  refine ⟨(clock_continuous c hc).measurable,?_⟩
  rw [Measure.map_smul _ (clock_continuous c hc).measurable.aemeasurable,timeMeasure_map_clock c hc h,smul_smul]
  have heq : ENNReal.ofReal (c:ℝ)*ENNReal.ofReal ((c:ℝ)⁻¹)=1 := by
    calc
      _=ENNReal.ofReal ((c:ℝ)*(c:ℝ)⁻¹) := (ENNReal.ofReal_mul c.2).symm
      _=1 := by rw [mul_inv_cancel₀ (show (c:ℝ)≠0 from ne_of_gt hc),ENNReal.ofReal_one]
  rw [heq,one_smul]

variable {Ω : Type*} [MeasurableSpace Ω]

theorem energyMeasure_clock_preserving (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0)
    (μ : Measure Ω) [SFinite μ] :
    MeasurePreserving (fun p : ℝ≥0×Ω => (clock c hc p.1,p.2))
      (ENNReal.ofReal (c:ℝ) • energyMeasure μ h) (energyMeasure μ (c*h)) := by
  have hh := (timeMeasure_clock_preserving c hc h).prod (MeasurePreserving.id μ)
  change MeasurePreserving (Prod.map (clock c hc) id)
    (ENNReal.ofReal (c:ℝ) • ((timeMeasure h).prod μ)) ((timeMeasure (c*h)).prod μ)
  rw [← Measure.prod_smul_left]
  exact hh

end SHE.PredictableTimeDilation
