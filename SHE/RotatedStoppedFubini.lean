module
public import SHE.StandardItoStoppedParameterFubini
public import SHE.RotatedItoAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.PredictableItoRotation
open MeasureTheory PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω A C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup A] [InnerProductSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
variable (Φ : (ℝ≥0 × Ω) → A →ₗᵢ[ℝ] C)
variable (hΦ : @Measurable ((ℝ≥0 × Ω) × A) C
  (𝓕.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p => Φ p.1 p.2))

/-- Ordinary stopped parameter Fubini passes to the actual predictable
noise rotation, with the same version and literal stopped integrals. -/
theorem stoppedParameterFubini (B : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
    (hB : StandardItoStoppedParameterFubini B) :
    StandardItoStoppedParameterFubini (integral 𝓕 μ H Φ hΦ B) := by
  intro hnull X _ ν _ K raw hraw hK hfinite
  let raw' : X × (ℝ≥0 × Ω) → C := fun z => Φ z.2 (raw z)
  have hraw' : StronglyMeasurable[(inferInstance : MeasurableSpace X).prod 𝓕.predictable] raw' := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
    exact (hΦ.comp (measurable_snd.prodMk hraw.measurable)).stronglyMeasurable
  let K' : X → Process (E:=C) 𝓕 μ H := fun x => processIsometry 𝓕 μ H Φ hΦ (K x)
  have hK' (x : X) : K' x =ᵐ[energyMeasure μ H] fun p => raw' (x,p) := by
    filter_upwards [processIsometry_ae 𝓕 μ H Φ hΦ (K x),hK x] with p hp hkp
    change (processIsometry 𝓕 μ H Φ hΦ (K x)) p=Φ p (raw (x,p))
    rw [hp,hkp]
  have hfinite' : (∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖raw' (x,(t,ω))‖^2) ∂μ ∂timeMeasure H ∂ν)<∞ := by
    simpa only [raw',LinearIsometry.norm_map] using hfinite
  obtain ⟨Y,hY,hYa,hYc⟩ := hB hnull X ν K' raw' hraw' hK' hfinite'
  refine ⟨Y,hY,?_,hYc⟩
  filter_upwards [hYa] with x hx
  intro q
  have he : (integral 𝓕 μ H Φ hΦ B).integral (stop 𝓕 μ H (q:ℝ) (K x)) =
      B.integral (stop 𝓕 μ H (q:ℝ) (K' x)) := by
    change B.integral (processIsometry 𝓕 μ H Φ hΦ (stop 𝓕 μ H (q:ℝ) (K x)))=_
    rw [RotatedItoAlgebra.map_stop]
  rw [he]
  exact hx q
end SHE.PredictableItoRotation
