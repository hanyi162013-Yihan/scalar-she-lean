module
public import SHE.DeterministicItoShiftIntegral
public import SHE.PredictableItoRotation
public import SHE.TimeDilationRoundTrip
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.DeterministicItoShiftRotation
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω A C E:Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup A] [InnerProductSpace ℝ A]
variable [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [SFinite μ]
variable (H v h:ℝ≥0) (hvh:v+h≤H) (φ:A→ₗᵢ[ℝ] C)

def field : (ℝ≥0×Ω)→A→ₗᵢ[ℝ] C := fun _=>φ

theorem measurable_field :
    @Measurable ((ℝ≥0×Ω)×A) C (𝓕.predictable.prod ‹MeasurableSpace A›)
      ‹MeasurableSpace C› (fun p=>field φ p.1 p.2) :=
  φ.continuous.measurable.comp measurable_snd

/-- Literal physical window extension commutes with every constant noise
isometry. The assertion is equality in the ORIGINAL predictable spaces. -/
theorem input (f:Process (E:=A) (DeterministicItoShift.filtration 𝓕 v) μ h):
    DeterministicItoShift.input 𝓕 μ H v h hvh
      (PredictableItoRotation.processIsometry (DeterministicItoShift.filtration 𝓕 v) μ h
        (field φ) (measurable_field (DeterministicItoShift.filtration 𝓕 v) φ) f)=
    PredictableItoRotation.processIsometry 𝓕 μ H (field φ) (measurable_field 𝓕 φ)
      (DeterministicItoShift.input 𝓕 μ H v h hvh f) :=by
  have hl:=PredictableItoRotation.processIsometry_ae
    (DeterministicItoShift.filtration 𝓕 v) μ h (field φ)
    (measurable_field (DeterministicItoShift.filtration 𝓕 v) φ) f
  have he:=DeterministicItoShift.extend_ae 𝓕 μ H v h hvh
    (Lp.stronglyMeasurable (PredictableItoRotation.processIsometry
      (DeterministicItoShift.filtration 𝓕 v) μ h (field φ)
      (measurable_field (DeterministicItoShift.filtration 𝓕 v) φ) f)).measurable
    (φ.continuous.measurable.comp (Lp.stronglyMeasurable f).measurable) hl
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [DeterministicItoShift.input_ae 𝓕 μ H v h hvh
      (PredictableItoRotation.processIsometry (DeterministicItoShift.filtration 𝓕 v) μ h
        (field φ) (measurable_field (DeterministicItoShift.filtration 𝓕 v) φ) f),
    he, PredictableItoRotation.processIsometry_ae 𝓕 μ H (field φ) (measurable_field 𝓕 φ)
      (DeterministicItoShift.input 𝓕 μ H v h hvh f),
    DeterministicItoShift.input_ae 𝓕 μ H v h hvh f] with p hi he hr hf
  rw [hi,he,hr,hf]
  simp only [field, DeterministicItoShift.extend]
  split_ifs <;> first | rfl | exact φ.map_zero.symm

/-- Restarting and constant isometric noise rotation give the SAME
ordinary integral, not merely equal terminal laws or versions. -/
theorem integral (J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H):
    PredictableItoRotation.integral (DeterministicItoShift.filtration 𝓕 v) μ h
      (field φ) (measurable_field (DeterministicItoShift.filtration 𝓕 v) φ)
      (DeterministicItoShift.integral 𝓕 μ H v h hvh J)=
    DeterministicItoShift.integral 𝓕 μ H v h hvh
      (PredictableItoRotation.integral 𝓕 μ H (field φ) (measurable_field 𝓕 φ) J) :=by
  apply PredictableTimeDilation.terminalIto_eq_of_integral_eq
  apply LinearIsometry.ext
  intro f
  change J.integral (DeterministicItoShift.input 𝓕 μ H v h hvh
      (PredictableItoRotation.processIsometry (DeterministicItoShift.filtration 𝓕 v) μ h
        (field φ) (measurable_field (DeterministicItoShift.filtration 𝓕 v) φ) f))=
    J.integral (PredictableItoRotation.processIsometry 𝓕 μ H (field φ) (measurable_field 𝓕 φ)
      (DeterministicItoShift.input 𝓕 μ H v h hvh f))
  rw [input]
end SHE.DeterministicItoShiftRotation
