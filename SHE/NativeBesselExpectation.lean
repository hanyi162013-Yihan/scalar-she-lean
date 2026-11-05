module
public import SHE.NativeBesselHeatEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.NativeBesselExpectation
open Set MeasureTheory Real AddCircle StoppedFourier NativeBesselHeatEnergy
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]

theorem measurable_heatMass (f:Ω→CircleL2)(hf:Measurable f):
    Measurable (fun p:Ω×ℝ=>heatMass p.2 (f p.1)):=by
  unfold heatMass
  apply Measurable.tsum
  intro l
  have hc:Measurable (fun p:Ω×ℝ=>fourierCoeff (f p.1) l):=
    ((PhysicalProfile.fourierCoeff_continuous l).measurable.comp hf).comp measurable_fst
  exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul
    (ENNReal.measurable_ofReal.comp (hc.norm.pow_const 2))

/-- Tonelli for the ACTUAL native Bessel energy on the original sample
measure. Positivity permits the full infinite heat-time integral with
no stochastic Fubini assumption or truncation loss. -/
theorem energy (μ:Measure Ω)[SFinite μ](f:Ω→CircleL2)(hf:Measurable f)
    (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0<ρ):
    (∫⁻ω,ENNReal.ofReal (‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (f ω)‖^2) ∂μ)=
      ∫⁻t in Ioi (0:ℝ),NativeBesselLaplace.kernel ρ Λ t*(∫⁻ω,heatMass t (f ω) ∂μ):=by
  simp_rw [NativeBesselHeatEnergy.bessel_norm Λ ρ hΛ hρ]
  have hm:Measurable (fun p:Ω×ℝ=>NativeBesselLaplace.kernel ρ Λ p.2*heatMass p.2 (f p.1)):=
    ((NativeBesselLaplace.kernel_measurable ρ Λ).comp measurable_snd).mul (measurable_heatMass f hf)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards with t
  exact lintegral_const_mul _ ((measurable_heatMass f hf).comp
    (measurable_id.prodMk measurable_const))

end SHE.NativeBesselExpectation
