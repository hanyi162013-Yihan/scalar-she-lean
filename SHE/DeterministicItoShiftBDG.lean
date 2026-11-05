module
public import SHE.DeterministicItoShiftIntegral
public import SHE.StandardTerminalBDGPower
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
namespace SHE.DeterministicItoShift
open MeasureTheory Set PredictableL2
open scoped NNReal ENNReal
variable{Ω C E:Type*}[MeasurableSpace Ω]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C]
variable[MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[SFinite μ]
variable(H v h:ℝ≥0)(hvh:v+h≤H)
include hvh

theorem extend_bracket {f:ℝ≥0×Ω→C}
    (hf:@Measurable _ _ (filtration 𝓕 v).predictable _ f)(ω:Ω):
    (∫⁻t,ENNReal.ofReal (‖extend v h f (t,ω)‖^2) ∂timeMeasure H)=
      ∫⁻s,ENNReal.ofReal (‖f (s,ω)‖^2) ∂timeMeasure h:=by
  have hm:Measurable (extend v h f):=(extend_predictable 𝓕 v h hf).mono (predictable_le_product 𝓕) le_rfl
  have ht:Measurable (fun t:ℝ≥0=>ENNReal.ofReal (‖extend v h f (t,ω)‖^2)):=
    ENNReal.measurable_ofReal.comp ((hm.comp (measurable_id.prodMk measurable_const)).norm.pow_const 2)
  calc
    _=∫⁻t in Ioc v (v+h),ENNReal.ofReal (‖extend v h f (t,ω)‖^2) ∂timeMeasure H:=by
      rw [←lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro t
      by_cases hh:t∈Ioc v (v+h)
      · rw [Set.indicator_of_mem hh]
      · have he:extend v h f (t,ω)=0:=extend_off v h f (t,ω) (fun hp=>hh hp.1)
        rw [Set.indicator_of_notMem hh,he]
        simp
    _=∫⁻s,ENNReal.ofReal (‖extend v h f (v+s,ω)‖^2) ∂timeMeasure h:=
      ((time_translation H v h hvh).lintegral_comp ht).symm
    _=_:=by
      apply lintegral_congr_ae
      filter_upwards [timeMeasure_ae_mem h] with s hs
      rw [extend_forward v h f (s,ω) hs]

/-- Equality of true samplewise brackets, with the physical extension
and the local input on one original sample event. -/
theorem bracket_ae(f:Process (E:=C) (filtration 𝓕 v) μ h):
    ∀ᵐω∂μ,(∫⁻t,ENNReal.ofReal (‖input 𝓕 μ H v h hvh f (t,ω)‖^2) ∂timeMeasure H)=
      ∫⁻s,ENNReal.ofReal (‖f (s,ω)‖^2) ∂timeMeasure h:=by
  have ha:=Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap
    (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae (input_ae 𝓕 μ H v h hvh f))
  filter_upwards [ha] with ω hω
  calc
    _=∫⁻t,ENNReal.ofReal (‖extend v h f (t,ω)‖^2) ∂timeMeasure H:=by
      apply lintegral_congr_ae
      filter_upwards [hω] with t ht
      dsimp only [Prod.swap] at ht
      rw [ht]
    _=_:=extend_bracket 𝓕 H v h hvh (Lp.stronglyMeasurable f).measurable ω

theorem bdgPower(p:ℕ)(J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)
    (B:ℝ≥0)(hBDG:StandardTerminalBDGPower p J B):
    StandardTerminalBDGPower p (integral 𝓕 μ H v h hvh J) B:=by
  intro f
  apply (hBDG (input 𝓕 μ H v h hvh f)).trans_eq
  congr 1
  apply lintegral_congr_ae
  filter_upwards [bracket_ae 𝓕 μ H v h hvh f] with ω hω
  rw [hω]

theorem bdg16(J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)
    (B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B):
    StandardTerminalBDG16 (integral 𝓕 μ H v h hvh J) B:=
  bdgPower 𝓕 μ H v h hvh 8 J B hBDG

end SHE.DeterministicItoShift
