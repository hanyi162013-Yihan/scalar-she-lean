module
public import SHE.HeatBandMovingSignedEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.HeatBandMovingSignedOrder
open Set MeasureTheory
open scoped ENNReal
/-- The sharp signed-input budget in the ORIGINAL past-then-age order,
with all actual input mass retained. This is Tonelli applied to the
proved band kernel, rather than a changed stochastic integral. -/
theorem energy {A β c:ℝ} (hβ:β≤1) (hc:0<c) (j:ℕ)
    (F:ℝ→ℝ≥0∞) (hF:Measurable F) (h W:ℝ):
    (∫⁻v in Ioc (0:ℝ) W,∫⁻τ in Ioc (0:ℝ) h,
      HeatBandCausalEnergy.kernel A β c j τ*F (v+h-τ))≤
      ENNReal.ofReal ((A*ScalarHeatBandEnvelope.constant β 0)^2*
        ScalarHeatBandTime.massConstant β 0*c⁻¹*CompactMollifier.radius (j+1)^(2*β))*(∫⁻r,F r):=by
  calc
    _=(∫⁻τ in Ioc (0:ℝ) h,∫⁻v in Ioc (0:ℝ) W,
        HeatBandCausalEnergy.kernel A β c j τ*F (v+h-τ)):=by
      apply lintegral_lintegral_swap
      exact (((HeatBandCausalEnergy.kernel_measurable A β c j).comp measurable_snd).mul
        (hF.comp ((measurable_fst.add_const h).sub measurable_snd))).aemeasurable
    _=(∫⁻τ in Ioc (0:ℝ) h,HeatBandCausalEnergy.kernel A β c j τ*
        (∫⁻v in Ioc (0:ℝ) W,F (v+h-τ))):=by
      apply lintegral_congr
      intro τ
      exact lintegral_const_mul _ (hF.comp ((measurable_id.add_const h).sub_const τ))
    _≤_:=HeatBandMovingSignedEnergy.energy (A:=A) hβ hc j F h W
end SHE.HeatBandMovingSignedOrder
