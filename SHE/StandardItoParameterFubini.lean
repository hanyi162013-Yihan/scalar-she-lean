module

public import SHE.StandardTerminalIto
public import SHE.LpEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SHE
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω C:Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ:Measure Ω} {H:ℝ≥0}

/-- An explicit ordinary parameterized-integral component of accepted
STOCHASTIC FUBINI package 4. Joint predictable square-integrable kernels
have a jointly measurable version of the SAME original scalar Ito map.
No SPDE, Gaussian profile, word bound or analytic applicability occurs
in this standard input. This property is an assumption, not an axiom. -/
def StandardItoParameterFubini (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H):Prop:=
  ∀(X:Type) [MeasurableSpace X] (ν:Measure X) [SFinite ν]
    (K:X→Process (E:=C) 𝓕 μ H) (raw:X×(ℝ≥0×Ω)→C),
    StronglyMeasurable[(inferInstance:MeasurableSpace X).prod 𝓕.predictable] raw→
    (∀x,K x=ᵐ[energyMeasure μ H] fun p=>raw (x,p))→
    (∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖raw (x,(t,ω))‖^2) ∂μ ∂timeMeasure H ∂ν)<∞→
    ∃Y:X×Ω→ℝ,Measurable Y ∧ ∀ᵐx∂ν,(fun ω=>Y (x,ω))=ᵐ[μ] J.integral (K x)

namespace StandardItoParameterFubini
variable [SFinite μ] (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
variable (hF:StandardItoParameterFubini J)
variable {X:Type} [MeasurableSpace X] (ν:Measure X) [SFinite ν]
variable (K:X→Process (E:=C) 𝓕 μ H) (raw:X×(ℝ≥0×Ω)→C)
variable (hraw:StronglyMeasurable[(inferInstance:MeasurableSpace X).prod 𝓕.predictable] raw)
variable (hK:∀x,K x=ᵐ[energyMeasure μ H] fun p=>raw (x,p))
variable (hfinite:(∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖raw (x,(t,ω))‖^2) ∂μ ∂timeMeasure H ∂ν)<∞)

include hF hraw hK hfinite in
/-- Its exact integrated isometry is DERIVED from the original J, not
added as another stochastic input. All parameter exceptional sets occur
under the actual specified parameter measure. -/
theorem energy:
    ∃Y:X×Ω→ℝ,Measurable Y ∧ (∀ᵐx∂ν,(fun ω=>Y (x,ω))=ᵐ[μ] J.integral (K x)) ∧
      (∫⁻x,∫⁻ω,ENNReal.ofReal (|Y (x,ω)|^2) ∂μ ∂ν)=
        ∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖raw (x,(t,ω))‖^2) ∂μ ∂timeMeasure H ∂ν:=by
  obtain ⟨Y,hY,hYa⟩:=hF X ν K raw hraw hK hfinite
  refine ⟨Y,hY,hYa,?_⟩
  apply lintegral_congr_ae
  filter_upwards [hYa] with x hx
  calc
    _=∫⁻ω,ENNReal.ofReal (‖J.integral (K x) ω‖^2) ∂μ:=by
      apply lintegral_congr_ae
      filter_upwards [hx] with ω hω
      rw [hω,Real.norm_eq_abs]
    _=ENNReal.ofReal (‖J.integral (K x)‖^2):=(LpEnergy.lintegral_energy _).symm
    _=∫⁻t,∫⁻ω,ENNReal.ofReal (‖K x (t,ω)‖^2) ∂μ ∂timeMeasure H:=J.isometry_energy _
    _=_:=by
      apply lintegral_congr_ae
      filter_upwards [Measure.ae_ae_of_ae_prod (hK x)] with t ht
      apply lintegral_congr_ae
      filter_upwards [ht] with ω hω
      rw [hω]

end StandardItoParameterFubini
end SHE
