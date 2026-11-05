module

public import SHE.TimeDilationIto
public import SHE.ScaledLpEquivalence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.PredictableTimeDilation
open MeasureTheory Set Filter PredictableL2
open scoped NNReal ENNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
variable (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0)

def processEquivalence : Process (E := C) (filtration 𝓕 (clock c hc)) μ (c*h)≃ₗᵢ[ℝ]
    Process (E := C) 𝓕 μ h :=
  @ScaledLpPull.equivalence (ℝ≥0×Ω) (ℝ≥0×Ω) C 𝓕.predictable
    (filtration 𝓕 (clock c hc)).predictable _ _
    ((energyMeasure μ h).trim (predictable_le_product 𝓕))
    ((energyMeasure μ (c*h)).trim (predictable_le_product (filtration 𝓕 (clock c hc))))
    (c:ℝ) hc (predictableEquiv 𝓕 (clock c hc)) (predictableMeasure_clock_preserving 𝓕 μ c hc h)

theorem processEquivalence_apply (v : Process (E := C) (filtration 𝓕 (clock c hc)) μ (c*h)) :
    processEquivalence 𝓕 μ c hc h v=processIsometry 𝓕 μ c hc h v := rfl

theorem processEquivalence_symm_ae (v : Process (E := C) 𝓕 μ h) :
    (processEquivalence 𝓕 μ c hc h).symm v=ᵐ[energyMeasure μ (c*h)]
      (fun p => Real.sqrt (c:ℝ)⁻¹ • v ((clock c hc).symm p.1,p.2)) := by
  apply ae_eq_of_ae_eq_trim
  exact @ScaledLpPull.equivalence_symm_ae (ℝ≥0×Ω) (ℝ≥0×Ω) C 𝓕.predictable
    (filtration 𝓕 (clock c hc)).predictable _ _
    ((energyMeasure μ h).trim (predictable_le_product 𝓕))
    ((energyMeasure μ (c*h)).trim (predictable_le_product (filtration 𝓕 (clock c hc))))
    (c:ℝ) hc (predictableEquiv 𝓕 (clock c hc)) (predictableMeasure_clock_preserving 𝓕 μ c hc h) v

/-- Evaluation of the rescaled integral on an actual pushed input is
the original integral exactly in terminal L². -/
theorem integral_push (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    (v : Process (E := C) 𝓕 μ h) :
    (integral 𝓕 μ c hc h I).integral ((processEquivalence 𝓕 μ c hc h).symm v)=I.integral v := by
  change I.integral (processIsometry 𝓕 μ c hc h ((processEquivalence 𝓕 μ c hc h).symm v))=I.integral v
  rw [← processEquivalence_apply,LinearIsometryEquiv.apply_symm_apply]

end SHE.PredictableTimeDilation
