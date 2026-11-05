module

public import SHE.MeasurableIsometryLift
public import SHE.StandardTerminalBDG

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PredictableItoRotation
open MeasureTheory PredictableL2
open scoped NNReal ENNReal

variable {Ω A C E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
variable [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)
variable (Φ : (ℝ≥0 × Ω) → A →ₗᵢ[ℝ] C)
variable (hΦ : @Measurable ((ℝ≥0 × Ω) × A) C
  (𝓕.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p => Φ p.1 p.2))

def processIsometry : Process (E := A) 𝓕 μ h →ₗᵢ[ℝ] Process (E := C) 𝓕 μ h := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  exact MeasurableIsometryLift.isometry ((energyMeasure μ h).trim (predictable_le_product 𝓕)) Φ hΦ

theorem processIsometry_ae (v : Process (E := A) 𝓕 μ h) :
    processIsometry 𝓕 μ h Φ hΦ v =ᵐ[energyMeasure μ h] (fun p => Φ p (v p)) := by
  apply ae_eq_of_ae_eq_trim
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  exact MeasurableIsometryLift.map_ae ((energyMeasure μ h).trim (predictable_le_product 𝓕)) Φ hΦ v

theorem processIsometry_stopped (l : ℝ≥0) (v : Process (E := A) 𝓕 μ h)
    (hv : ∀ᵐ p ∂energyMeasure μ h,l < p.1 → v p=0) :
    ∀ᵐ p ∂energyMeasure μ h,l < p.1 → processIsometry 𝓕 μ h Φ hΦ v p=0 := by
  filter_upwards [processIsometry_ae 𝓕 μ h Φ hΦ v,hv] with p hp hs hlt
  rw [hp,hs hlt,map_zero]

/-- Predictable pointwise Hilbert isometries transport the ordinary
terminal Ito integral, preserving its exact norm, centering and adapted
versions. No heat-specific integration law is assumed. -/
def integral (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h) :
    StandardTerminalIto (C := A) (E := E) 𝓕 μ h where
  integral := I.integral.comp (processIsometry 𝓕 μ h Φ hΦ)
  adapted l v hv := I.adapted l _ (processIsometry_stopped 𝓕 μ h Φ hΦ l v hv)
  centered v := I.centered _

variable [SFinite μ]

theorem bracket_ae (v : Process (E := A) 𝓕 μ h) :
    ∀ᵐ ω ∂μ,(∫⁻ s,ENNReal.ofReal (‖processIsometry 𝓕 μ h Φ hΦ v (s,ω)‖^2) ∂timeMeasure h)=
      ∫⁻ s,ENNReal.ofReal (‖v (s,ω)‖^2) ∂timeMeasure h := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure h)).quasiMeasurePreserving.ae
    (processIsometry_ae 𝓕 μ h Φ hΦ v)
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  apply lintegral_congr_ae
  filter_upwards [hω] with s hs
  dsimp only [Prod.swap] at hs
  rw [hs,(Φ (s,ω)).norm_map]

theorem bdg16 (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B) :
    StandardTerminalBDG16 (integral 𝓕 μ h Φ hΦ I) B := by
  intro v
  apply (hBDG (processIsometry 𝓕 μ h Φ hΦ v)).trans_eq
  congr 1
  apply lintegral_congr_ae
  filter_upwards [bracket_ae 𝓕 μ h Φ hΦ v] with ω hω
  rw [hω]

end SHE.PredictableItoRotation
