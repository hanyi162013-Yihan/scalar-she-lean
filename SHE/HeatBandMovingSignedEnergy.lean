module
public import SHE.HeatBandCausalEnergy
public import Mathlib.MeasureTheory.Group.Prod
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.HeatBandMovingSignedEnergy
open Set MeasureTheory Real
open scoped ENNReal

/-- A moving past section of the actual input never exceeds its TRUE
whole physical input energy. The shift depends on the future age. -/
theorem shifted_mass (F : ℝ→ℝ≥0∞) (s W : ℝ) :
    (∫⁻v in Ioc (0:ℝ) W,F (v+s))≤∫⁻v,F v := by
  calc
    _≤∫⁻v,F (v+s):=lintegral_mono' Measure.restrict_le_self le_rfl
    _=∫⁻v,F v:=(measurePreserving_add_right (volume:Measure ℝ) s).lintegral_comp_emb
      (MeasurableEquiv.addRight s).measurableEmbedding F

/-- The actual signed-input first Gamma slot has its full band gain
under original moving-past integration. No supremum of the input and
no independent copy of a random field enters this calculation. -/
theorem energy {A β c : ℝ} (hβ:β≤1) (hc:0<c) (j:ℕ)
    (F : ℝ→ℝ≥0∞) (h W : ℝ) :
    (∫⁻τ in Ioc (0:ℝ) h,HeatBandCausalEnergy.kernel A β c j τ*
      (∫⁻v in Ioc (0:ℝ) W,F (v+h-τ)))≤
      ENNReal.ofReal ((A*ScalarHeatBandEnvelope.constant β 0)^2*
        ScalarHeatBandTime.massConstant β 0*c⁻¹*CompactMollifier.radius (j+1)^(2*β))*(∫⁻v,F v) := by
  let K:=HeatBandCausalEnergy.kernel A β c j
  have hp (τ:ℝ) : (∫⁻v in Ioc (0:ℝ) W,F (v+h-τ))≤∫⁻v,F v := by
    simpa only [show ∀v:ℝ,v+h-τ=v+(h-τ) by intro v;ring] using shifted_mass F (h-τ) W
  calc
    _≤∫⁻τ in Ioc (0:ℝ) h,K τ*(∫⁻v,F v):=lintegral_mono (fun τ=>by gcongr 1;exact hp τ)
    _≤∫⁻τ,K τ*(∫⁻v,F v):=lintegral_mono' Measure.restrict_le_self le_rfl
    _=(∫⁻τ,K τ)*(∫⁻v,F v):=lintegral_mul_const _ (HeatBandCausalEnergy.kernel_measurable A β c j)
    _=_:=by rw [show K=HeatBandCausalEnergy.kernel A β c j from rfl,HeatBandCausalEnergy.kernel_mass hβ hc j]
end SHE.HeatBandMovingSignedEnergy
