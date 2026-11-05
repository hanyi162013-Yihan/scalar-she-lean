module

public import SHE.NativeBesselExpectation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeBesselHeatCap
open MeasureTheory Set SHE SHE.StoppedFourier AddCircle
open scoped ENNReal
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bound for every positive heat-regularized quadratic form gives
the actual massive Bessel energy with its exact Laplace mass. All
Fourier modes and all positive heat times are retained by Tonelli. -/
theorem bound (μ : Measure Ω) [SFinite μ] (f : Ω → CircleL2) (hf : Measurable f)
    {Λ ρ C : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ)
    (hHeat : ∀ (t : ℝ) (ht : 0 < t),
      (∫⁻ ω,ENNReal.ofReal (‖circleHeatOperator (t/2) (by positivity) (f ω)‖^2) ∂μ) ≤ ENNReal.ofReal C) :
    (∫⁻ ω,ENNReal.ofReal (‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (f ω)‖^2) ∂μ) ≤
      ENNReal.ofReal (Λ^(-ρ))*ENNReal.ofReal C := by
  rw [NativeBesselExpectation.energy μ f hf Λ ρ hΛ hρ]
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ),NativeBesselLaplace.kernel ρ Λ t*ENNReal.ofReal C := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp_rw [NativeBesselHeatEnergy.heat_norm t ht.le]
      exact mul_le_mul_right (hHeat t ht) _
    _ = _ := by
      rw [lintegral_mul_const _ (NativeBesselLaplace.kernel_measurable ρ Λ),
        NativeBesselLaplace.symbol hρ (zero_lt_one.trans_le hΛ)]

/-- The same estimate as an ordinary integrable expected energy. -/
theorem integral_bound (μ : Measure Ω) [SFinite μ] (f : Ω → CircleL2) (hf : Measurable f)
    {Λ ρ C : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hHeat : ∀ (t : ℝ) (ht : 0 < t),
      (∫⁻ ω,ENNReal.ofReal (‖circleHeatOperator (t/2) (by positivity) (f ω)‖^2) ∂μ) ≤ ENNReal.ofReal C) :
    Integrable (fun ω => ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (f ω)‖^2) μ ∧
      (∫ ω,‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (f ω)‖^2 ∂μ) ≤ Λ^(-ρ)*C := by
  have hh := bound μ f hf hΛ hρ hHeat
  have hm : Measurable (fun ω => ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (f ω)‖^2) :=
    (((OneInputOperator.besselHalf Λ ρ hΛ hρ.le).continuous.measurable.comp hf).norm.pow_const 2)
  have hi : Integrable (fun ω => ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (f ω)‖^2) μ := by
    refine ⟨hm.aestronglyMeasurable,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun ω => sq_nonneg _))).mpr
      (hh.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))
  refine ⟨hi,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun ω => sq_nonneg _)),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (zero_le_one.trans hΛ) _)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hΛ) _) hC)).mp hh

end SHEStochastic.NativeBesselHeatCap
