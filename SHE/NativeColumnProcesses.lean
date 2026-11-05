module

public import SHE.NativeFourierEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.NativeColumnProcesses
open MeasureTheory PredictableL2 NativeFourierNoiseRows OrthogonalItoChannels NativeFourierIto
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω]
local instance nativeColumnProcesses_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeColumnProcesses_circleSecond : SecondCountableTopology StoppedFourier.CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance nativeColumnProcesses_sigma : MeasurableSpace Columns:=borel _
local instance nativeColumnProcesses_borel : BorelSpace Columns:=⟨rfl⟩
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (h : ℝ≥0)

theorem memLp (K : ℝ≥0×Ω→Columns) (hK : StronglyMeasurable[𝓕.predictable] K)
    (hE : Integrable (fun p=>‖K p‖^2) (energyMeasure μ h)) :
    @MemLp _ _ 𝓕.predictable _ _ K 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕)) := by
  have hi : MemLp K 2 (energyMeasure μ h):=
    (memLp_two_iff_integrable_sq_norm (hK.mono (predictable_le_product 𝓕)).aestronglyMeasurable).mpr hE
  exact (le_of_eq (eLpNorm_trim (predictable_le_product 𝓕) hK)).trans_lt hi

def process (K : ℝ≥0×Ω→Columns) (hK : StronglyMeasurable[𝓕.predictable] K)
    (hE : Integrable (fun p=>‖K p‖^2) (energyMeasure μ h)) : Process (E:=Columns) 𝓕 μ h:=
  (memLp 𝓕 μ h K hK hE).toLp K

theorem process_ae (K : ℝ≥0×Ω→Columns) (hK : StronglyMeasurable[𝓕.predictable] K)
    (hE : Integrable (fun p=>‖K p‖^2) (energyMeasure μ h)) :
    process 𝓕 μ h K hK hE=ᵐ[energyMeasure μ h] K :=
  ae_eq_of_ae_eq_trim (memLp 𝓕 μ h K hK hE).coeFn_toLp

/-- Actual predictable column fields with proved finite trace energy
produce full Fourier output on the ORIGINAL scalar J, with exact total
energy. There is no extra Hilbert-valued Itô map premise. -/
theorem output_energy
    (J : StandardTerminalIto (C:=Both Row) (E:=ℝ) 𝓕 μ h)
    (K0 K1 : ℝ≥0×Ω→Columns) (hK0 : StronglyMeasurable[𝓕.predictable] K0)
    (hK1 : StronglyMeasurable[𝓕.predictable] K1)
    (hE0 : Integrable (fun p=>‖K0 p‖^2) (energyMeasure μ h))
    (hE1 : Integrable (fun p=>‖K1 p‖^2) (energyMeasure μ h)) :
    let P0:=process 𝓕 μ h K0 hK0 hE0
    let P1:=process 𝓕 μ h K1 hK1 hE1
    (∫⁻ ω, (∑' l : ℤ,ENNReal.ofReal (‖J.integral (realInput 𝓕 μ h l P0 P1) ω‖^2))+
      (∑' l : ℤ,ENNReal.ofReal (‖J.integral (imagInput 𝓕 μ h l P0 P1) ω‖^2)) ∂μ)=
      ENNReal.ofReal (∫ p,(‖K0 p‖^2+‖K1 p‖^2) ∂energyMeasure μ h) := by
  intro P0 P1
  rw [NativeFourierIto.scalar_energy 𝓕 μ h J P0 P1]
  have he : (fun p=>‖P0 p‖^2+‖P1 p‖^2)=ᵐ[energyMeasure μ h]
      (fun p=>‖K0 p‖^2+‖K1 p‖^2) := by
    filter_upwards [process_ae 𝓕 μ h K0 hK0 hE0,process_ae 𝓕 μ h K1 hK1 hE1] with p h0 h1
    rw [h0,h1]
  rw [lintegral_congr_ae (he.mono (fun p hp=>congrArg ENNReal.ofReal hp))]
  exact (ofReal_integral_eq_lintegral_ofReal (hE0.add hE1)
    (ae_of_all _ (fun p=>add_nonneg (sq_nonneg _) (sq_nonneg _)))).symm

end SHE.NativeColumnProcesses
