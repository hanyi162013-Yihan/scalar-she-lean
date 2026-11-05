module

public import SHE.StandardTerminalIto
public import SHE.LpEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.CountableSameItoEnergy
open MeasureTheory PredictableL2
open scoped ENNReal NNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [Countable ι]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [SFinite μ]
  {h : ℝ≥0}

/-- The actual predictable representative has measurable squared energy
on the original physical time/sample product. -/
theorem row_measurable (v : Process (E := C) 𝓕 μ h) :
    Measurable (fun p : ℝ≥0 × Ω => ENNReal.ofReal (‖v p‖ ^ 2)) := by
  exact ((realization_stronglyMeasurable (energyMeasure μ h)
    (predictable_le_product 𝓕) v).norm.pow 2).measurable.ennreal_ofReal

theorem scalar_measurable
    (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h)
    (v : Process (E := C) 𝓕 μ h) :
    Measurable (fun ω => ENNReal.ofReal (‖J.integral v ω‖ ^ 2)) := by
  exact ((Lp.stronglyMeasurable (J.integral v)).norm.pow 2).measurable.ennreal_ofReal

/-- Pointwise energy of one row, on the genuine product measure. -/
theorem row_energy (v : Process (E := C) 𝓕 μ h) :
    ENNReal.ofReal (‖v‖ ^ 2) =
      ∫⁻ p, ENNReal.ofReal (‖v p‖ ^ 2) ∂energyMeasure μ h := by
  rw [process_lintegral_energy]
  exact (lintegral_prod _ (row_measurable v).aemeasurable).symm

/-- Countably many coordinates of the SAME original scalar Ito map have
exact output energy equal to their actual input row energy. No second
Hilbert-valued stochastic integral is assumed, and no finite-trace
hypothesis is needed for this nonnegative identity. -/
theorem coordinate_energy
    (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h)
    (v : ι → Process (E := C) 𝓕 μ h) :
    (∫⁻ ω, ∑' i, ENNReal.ofReal (‖J.integral (v i) ω‖ ^ 2) ∂μ) =
      ∫⁻ p, ∑' i, ENNReal.ofReal (‖v i p‖ ^ 2) ∂energyMeasure μ h := by
  rw [lintegral_tsum (fun i => (scalar_measurable J (v i)).aemeasurable),
    lintegral_tsum (fun i => (row_measurable (v i)).aemeasurable)]
  apply tsum_congr
  intro i
  rw [← LpEnergy.lintegral_energy, J.integral.norm_map]
  exact row_energy (v i)

/-- The same identity in literal iterated physical time/sample form. -/
theorem coordinate_time_energy
    (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h)
    (v : ι → Process (E := C) 𝓕 μ h) :
    (∫⁻ ω, ∑' i, ENNReal.ofReal (‖J.integral (v i) ω‖ ^ 2) ∂μ) =
      ∫⁻ t, ∫⁻ ω, ∑' i, ENNReal.ofReal (‖v i (t,ω)‖ ^ 2) ∂μ ∂timeMeasure h := by
  rw [coordinate_energy J v]
  exact lintegral_prod _
    (Measurable.ennreal_tsum (fun i => row_measurable (v i))).aemeasurable

/-- Finite total trace gives simultaneous almost-everywhere finite
coordinate energy, rather than a different exceptional set per mode. -/
theorem coordinate_energy_finite_ae
    (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h)
    (v : ι → Process (E := C) 𝓕 μ h)
    (hv : (∫⁻ p, ∑' i, ENNReal.ofReal (‖v i p‖ ^ 2)
      ∂energyMeasure μ h) ≠ ∞) :
    ∀ᵐ ω ∂μ, (∑' i, ENNReal.ofReal (‖J.integral (v i) ω‖ ^ 2)) < ∞ := by
  apply ae_lt_top (Measurable.ennreal_tsum (fun i => scalar_measurable J (v i)))
  rwa [coordinate_energy J v]

end SHE.CountableSameItoEnergy
