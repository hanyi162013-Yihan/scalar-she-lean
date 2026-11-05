module

public import SHE.NativeFourierIto

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.NativeFourierEnergy
open MeasureTheory PredictableL2 NativeFourierNoiseRows OrthogonalItoChannels NativeFourierIto
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (h : ℝ≥0)

/-- Exact full output energy and simultaneous finite Fourier energy,
from the SAME original scalar integral and the actual complete
predictable column processes. -/
theorem energy
    (J : StandardTerminalIto (C:=Both Row) (E:=ℝ) 𝓕 μ h)
    (K0 K1 : Process (E:=Columns) 𝓕 μ h) :
    (∫⁻ ω, (∑' l : ℤ,ENNReal.ofReal (‖J.integral (realInput 𝓕 μ h l K0 K1) ω‖^2))+
      (∑' l : ℤ,ENNReal.ofReal (‖J.integral (imagInput 𝓕 μ h l K0 K1) ω‖^2)) ∂μ)=
      ENNReal.ofReal (‖K0‖^2+‖K1‖^2) := by
  rw [scalar_energy 𝓕 μ h J K0 K1]
  simp_rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  rw [lintegral_add_left (CountableSameItoEnergy.row_measurable K0),
    ←CountableSameItoEnergy.row_energy K0,←CountableSameItoEnergy.row_energy K1]

theorem finite_ae
    (J : StandardTerminalIto (C:=Both Row) (E:=ℝ) 𝓕 μ h)
    (K0 K1 : Process (E:=Columns) 𝓕 μ h) :
    ∀ᵐ ω∂μ,(∑' l : ℤ,ENNReal.ofReal (‖J.integral (realInput 𝓕 μ h l K0 K1) ω‖^2))+
      (∑' l : ℤ,ENNReal.ofReal (‖J.integral (imagInput 𝓕 μ h l K0 K1) ω‖^2))<∞ := by
  apply ae_lt_top
    ((Measurable.tsum (fun l=>CountableSameItoEnergy.scalar_measurable J (realInput 𝓕 μ h l K0 K1))).add
      (Measurable.tsum (fun l=>CountableSameItoEnergy.scalar_measurable J (imagInput 𝓕 μ h l K0 K1))))
  simp only [Pi.add_apply]
  rw [energy 𝓕 μ h J K0 K1]
  exact ENNReal.ofReal_ne_top

end SHE.NativeFourierEnergy
