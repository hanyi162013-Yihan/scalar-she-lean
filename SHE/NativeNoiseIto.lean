module

public import SHE.RealJointNoise

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.NativeRealNoise
open Set Filter MeasureTheory Real StoppedFourier PredictableL2
open scoped ENNReal NNReal
local instance nativeNoiseIto_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance nativeNoiseIto_columnsMeasurable : MeasurableSpace SignedKernelColumns.Space := borel SignedKernelColumns.Space
local instance nativeNoiseIto_columnsBorel : BorelSpace SignedKernelColumns.Space := ⟨rfl⟩
local instance nativeNoiseIto_realColumnsMeasurable : MeasurableSpace RealHaarIntegrand.Columns := borel RealHaarIntegrand.Columns
local instance nativeNoiseIto_realColumnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

/-- A predictable native real-column field with finite actual trace
energy belongs to the ORIGINAL real unit-circle Itô input space. -/
theorem field_memLp (F : ℝ≥0 × Ω → SignedKernelColumns.Space)
    (hF : StronglyMeasurable[𝓕.predictable] F)
    (hr : ∀ z,columnsEmbed (columnsPart (F z))=F z)
    (hE : Integrable (fun z => ‖F z‖^2) (energyMeasure μ H)) :
    @MemLp _ _ 𝓕.predictable _ _ (fun z => columnsPart (F z)) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)) := by
  have hm : StronglyMeasurable[𝓕.predictable] (fun z => columnsPart (F z)) :=
    columnsPart.continuous.comp_stronglyMeasurable hF
  have hi : Integrable (fun z => ‖columnsPart (F z)‖^2) (energyMeasure μ H) :=
    hE.congr (ae_of_all _ (fun z => (columnsPart_norm_sq_of_fixed (F z) (hr z)).symm))
  have hmem : MemLp (fun z => columnsPart (F z)) 2 (energyMeasure μ H) :=
    (memLp_two_iff_integrable_sq_norm (hm.mono (predictable_le_product 𝓕)).aestronglyMeasurable).mpr hi
  exact (le_of_eq (eLpNorm_trim (predictable_le_product 𝓕) hm)).trans_lt hmem

def process (F : ℝ≥0 × Ω → SignedKernelColumns.Space)
    (hF : StronglyMeasurable[𝓕.predictable] F)
    (hr : ∀ z,columnsEmbed (columnsPart (F z))=F z)
    (hE : Integrable (fun z => ‖F z‖^2) (energyMeasure μ H)) :
    Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H :=
  (field_memLp 𝓕 μ H F hF hr hE).toLp (fun z => columnsPart (F z))

theorem process_ae (F : ℝ≥0 × Ω → SignedKernelColumns.Space)
    (hF : StronglyMeasurable[𝓕.predictable] F)
    (hr : ∀ z,columnsEmbed (columnsPart (F z))=F z)
    (hE : Integrable (fun z => ‖F z‖^2) (energyMeasure μ H)) :
    process 𝓕 μ H F hF hr hE=ᵐ[energyMeasure μ H] fun z => columnsPart (F z) :=
  ae_eq_of_ae_eq_trim (field_memLp 𝓕 μ H F hF hr hE).coeFn_toLp

theorem process_norm_sq (F : ℝ≥0 × Ω → SignedKernelColumns.Space)
    (hF : StronglyMeasurable[𝓕.predictable] F)
    (hr : ∀ z,columnsEmbed (columnsPart (F z))=F z)
    (hE : Integrable (fun z => ‖F z‖^2) (energyMeasure μ H)) :
    ‖process 𝓕 μ H F hF hr hE‖^2=
      ∫ q,∫ ω,‖F (q,ω)‖^2 ∂μ ∂timeMeasure H := by
  rw [process_integral_energy]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod (process_ae 𝓕 μ H F hF hr hE)] with q hq
  apply integral_congr_ae
  filter_upwards [hq] with ω hω
  rw [hω]
  exact columnsPart_norm_sq_of_fixed (F (q,ω)) (hr (q,ω))

/-- Exact native expected energy for the ORIGINAL supplied real Itô
integral. No new noise, complex integral, clock rescaling assumption or
extra stochastic isometry is introduced. -/
theorem original_ito_energy
    (I : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=DyadicApproximation.RealL2) 𝓕 μ H)
    (F : ℝ≥0 × Ω → SignedKernelColumns.Space)
    (hF : StronglyMeasurable[𝓕.predictable] F)
    (hr : ∀ z,columnsEmbed (columnsPart (F z))=F z)
    (hE : Integrable (fun z => ‖F z‖^2) (energyMeasure μ H)) :
    (∫ ω,‖NativeHeatObservation.embed (I.integral (process 𝓕 μ H F hF hr hE) ω)‖^2 ∂μ)=
      ∫ q,∫ ω,‖F (q,ω)‖^2 ∂μ ∂timeMeasure H := by
  simp only [NativeHeatObservation.embed_norm]
  rw [←realLp_norm_sq,I.integral.norm_map]
  exact process_norm_sq 𝓕 μ H F hF hr hE

end SHE.NativeRealNoise
