module

public import SHE.GoodSignedKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRandomKernel
open MeasureTheory AddCircle Real StoppedFourier FiniteHaar
local instance nativeSeparatedAction_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance nativeSeparatedAction_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Exact native action of the unit-coordinate two-time operator. This
retains the original signed input before the true native right heat. -/
theorem separated_norm_native {Λ ρ δ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (F : Ω × (HeatCircle × HeatCircle) → ℂ) (ω : Ω) (z : CircleHeat.CircleL2) :
    ‖separatedHeat Λ ρ (NativeHeatSpan.clock δ) hΛ hρ (unitOperator F ω) z‖=
      ‖OneInputOperator.besselHalf Λ ρ hΛ hρ
        (integralOperator F ω (circleHeatOperator δ hδ (CircleNormalization.push z)))‖ := by
  change ‖CircleNormalization.push.symm (OneInputOperator.besselHalf Λ ρ hΛ hρ
    (CircleNormalization.push (CircleNormalization.push.symm
      (integralOperator F ω (CircleNormalization.push (CircleHeat.heat (NativeHeatSpan.clock δ) z))))))‖=_
  rw [LinearIsometryEquiv.norm_map,LinearIsometryEquiv.apply_symm_apply,
    CircleNormalization.push_heat (NativeHeatSpan.clock δ) (div_nonneg hδ (by positivity)) z]
  have he : (2*π)^2*NativeHeatSpan.clock δ=δ := by
    unfold NativeHeatSpan.clock
    field_simp
    ring
  simp only [he]

end SHE.NativeRandomKernel
