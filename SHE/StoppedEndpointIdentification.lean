module
public import SHE.StoppedInputParameter
public import SHE.StandardTerminalIto
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Order.IsLUB
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.StoppedEndpointIdentification
open MeasureTheory Filter Topology Set PredictableL2
open scoped NNReal ENNReal
variable {Ω C:Type*}[MeasurableSpace Ω][NormedAddCommGroup C][InnerProductSpace ℝ C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(H:ℝ≥0)

/-- A continuous scalar version agrees with the SAME original stopped
integral at the right endpoint. No spatial joint version is required. -/
theorem identify (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
    (R:Process (E:=C) 𝓕 μ H)(u:ℝ≥0→Ω→ℝ)(a:Ω→ℝ)
    (v b:ℝ≥0)(hvb:v<b)(hu:∀ω,ContinuousAt (fun t=>u t ω) b)
    (he:∀q,v<q→q<b→u q=ᵐ[μ] (fun ω=>a ω+J.integral (StoppedItoInputs.stop 𝓕 μ H q R) ω)):
    u b=ᵐ[μ] (fun ω=>a ω+J.integral (StoppedItoInputs.stop 𝓕 μ H b R) ω):=by
  obtain ⟨q,hmono,hq,hlim⟩:=exists_seq_strictMono_tendsto' hvb
  have hreal:Tendsto (fun n=>(q n:ℝ)) atTop (𝓝 (b:ℝ)):=
    NNReal.continuous_coe.continuousAt.tendsto.comp hlim
  have hstop:=StoppedInputParameter.stop_tendsto_left 𝓕 μ H R _
    (fun n=>by exact_mod_cast (hq n).2.le) hreal
  have hJ:=J.integral.continuous.continuousAt.tendsto.comp hstop
  obtain ⟨ns,hns,hpoint⟩:=(tendstoInMeasure_of_tendsto_Lp hJ).exists_seq_tendsto_ae
  filter_upwards [hpoint,ae_all_iff.mpr (fun n=>he (q n) (hq n).1 (hq n).2)] with ω hp he
  have hl: Tendsto (fun n=>u (q (ns n)) ω) atTop (𝓝 (u b ω)):=
    (hu ω).tendsto.comp (hlim.comp hns.tendsto_atTop)
  have hr: Tendsto (fun n=>a ω+J.integral (StoppedItoInputs.stop 𝓕 μ H (q (ns n)) R) ω) atTop
      (𝓝 (a ω+J.integral (StoppedItoInputs.stop 𝓕 μ H b R) ω)):=
    (tendsto_const_nhds (x:=a ω)).add hp
  have heq:(fun n=>u (q (ns n)) ω)=
      (fun n=>a ω+J.integral (StoppedItoInputs.stop 𝓕 μ H (q (ns n)) R) ω):=funext (fun n=>he (ns n))
  rw [←heq] at hr
  exact tendsto_nhds_unique hl hr

end SHE.StoppedEndpointIdentification
