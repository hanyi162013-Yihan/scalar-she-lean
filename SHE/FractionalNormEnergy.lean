module

public import SHE.RealMomentBound

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FractionalNormEnergy
open MeasureTheory
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The original sample L2 energy controls every fractional squared
norm, including zero energy, with no independence or boundedness input. -/
theorem fractional_square (d : Ω→E) (hd : AEStronglyMeasurable d μ)
    (hdi : Integrable (fun ω=>‖d ω‖^2) μ) {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    Integrable (fun ω=>‖d ω‖^((2:ℝ)*β)) μ ∧
      (∫ ω,‖d ω‖^((2:ℝ)*β) ∂μ)≤(∫ ω,‖d ω‖^2 ∂μ)^β := by
  let A:=∫ ω,‖d ω‖^2 ∂μ
  have hA : 0≤A:=integral_nonneg (fun _=>sq_nonneg _)
  have hb : (∫⁻ ω,ENNReal.ofReal (‖‖d ω‖‖^(2:ℝ)) ∂μ)≤ENNReal.ofReal A:=by
    simp only [norm_norm,Real.rpow_two]
    rw [←ofReal_integral_eq_lintegral_ofReal hdi (ae_of_all _ (fun _=>sq_nonneg _))]
  have hf:=FractionalMoment.moment_fraction hd.norm hβ hβ1 hA hb
  have hfb : (∫⁻ ω,ENNReal.ofReal (‖d ω‖^((2:ℝ)*β)) ∂μ)≤ENNReal.ofReal (A^β):=by
    simpa only [norm_norm] using hf
  exact RealMomentBound.integral_bound μ (fun ω=>‖d ω‖^((2:ℝ)*β))
    ((hd.norm.aemeasurable.pow_const ((2:ℝ)*β)).aestronglyMeasurable)
    (fun _=>Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hA _) hfb

end SHE.FractionalNormEnergy
