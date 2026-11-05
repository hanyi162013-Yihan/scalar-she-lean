module

public import SHE.ProcessEnergy

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE
open MeasureTheory PredictableL2
open scoped NNReal

/-- Standard stochastic input package 1, in a reusable terminal Hilbert
form. This is the ordinary linear Itô integration isometry, its adapted
version for integrands stopped at a deterministic time, and centering.
The heat kernel, its time-parameter regularity, and the stochastic
convolution process are deliberately absent from this standard input. -/
structure StandardTerminalIto {Ω C E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0) where
  integral : Process (E := C) 𝓕 μ h →ₗᵢ[ℝ] Lp E 2 μ
  adapted : ∀ (l : ℝ≥0) (v : Process (E := C) 𝓕 μ h),
    (∀ᵐ p ∂energyMeasure μ h,l < p.1 → v p=0) →
    ∃ Z : Ω → E,StronglyMeasurable[𝓕 l] Z ∧ integral v =ᵐ[μ] Z
  centered : ∀ v : Process (E := C) 𝓕 μ h,∫ ω,integral v ω ∂μ=0

namespace StandardTerminalIto
variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [SFinite μ] {h : ℝ≥0}

theorem isometry_energy (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    (v : Process (E := C) 𝓕 μ h) :
    ENNReal.ofReal (‖I.integral v‖^2)=
      ∫⁻ t,∫⁻ ω,ENNReal.ofReal (‖v (t,ω)‖^2) ∂μ ∂timeMeasure h := by
  rw [I.integral.norm_map]
  exact process_lintegral_energy 𝓕 μ h v

theorem difference_energy (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ h)
    (v w : Process (E := C) 𝓕 μ h) :
    ENNReal.ofReal (‖I.integral v-I.integral w‖^2)=
      ∫⁻ t,∫⁻ ω,ENNReal.ofReal (‖v (t,ω)-w (t,ω)‖^2) ∂μ ∂timeMeasure h := by
  rw [← map_sub,I.integral.norm_map]
  exact process_difference_lintegral_energy 𝓕 μ h v w

end StandardTerminalIto
end SHE
