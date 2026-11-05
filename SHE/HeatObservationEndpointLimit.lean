module

public import SHE.HeatPhysicalSubsequence
public import SHE.StandardTerminalIto

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.HeatObservationEndpointLimit
open MeasureTheory Filter Topology NativeHeatObservation StoppedFourier FiniteHaar DyadicApproximation AddCircle
open scoped NNReal ENNReal
local instance heatObservationEndpointLimit_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance heatObservationEndpointLimit_realSigma : MeasurableSpace RealL2 := borel _
local instance heatObservationEndpointLimit_realBorel : BorelSpace RealL2 := ⟨rfl⟩
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

/-- A positive-age physical observation and a limit in the SAME original
Itô input space identify the actual zero-age spatial representative.
No pointwise version of the L² state is assumed in advance. -/
theorem physical_endpoint (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
    (U : Ω→RealL2) (hU : Measurable U)
    (R : HeatCircle→ℝ→PredictableL2.Process (E:=C) 𝓕 μ H)
    (a : HeatCircle→ℝ→ℝ)
    (ha : ∀ x,ContinuousAt (a x) 0)
    (hR : ∀ (ε : ℕ→ℝ),(∀ n,0<ε n)→Tendsto ε atTop (𝓝 0)→
      ∀ x,Tendsto (fun n=>R x (ε n)) atTop (𝓝 (R x 0)))
    (hobs : ∀ ε,0<ε→∀ x,(fun ω=>functional ε x (U ω))=ᵐ[μ]
      fun ω=>a x ε+J.integral (R x ε) ω) :
    ∀ᵐ x : HeatCircle∂haarAddCircle,∀ᵐ ω∂μ,
      PredictableScalarField.nativeField U (ω,x)=a x 0+J.integral (R x 0) ω := by
  obtain ⟨ε,hε,hε0,hphysical⟩ := HeatPhysicalSubsequence.exists_common_subsequence U U hU hU μ
  have hs := (Measure.measurePreserving_swap (μ:=haarAddCircle (T:=2*Real.pi)) (ν:=μ)).quasiMeasurePreserving.ae hphysical
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with x hx
  have ht := J.integral.continuous.continuousAt.tendsto.comp (hR ε hε hε0 x)
  obtain ⟨ns,hns,hlim⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  filter_upwards [hx,hlim,ae_all_iff.mpr (fun n=>hobs (ε n) (hε n) x)] with ω hp hj ho
  have hleft : Tendsto (fun n=>functional (ε n) x (U ω)) atTop
      (𝓝 (PredictableScalarField.nativeField U (ω,x))) := by
    simpa only [functional_physical (hε _),Prod.swap,Prod.fst,Prod.snd] using hp.1
  have hright := ((ha x).tendsto.comp (hε0.comp hns.tendsto_atTop)).add hj
  have he : (fun n=>functional (ε (ns n)) x (U ω))=
      (fun n=>a x (ε (ns n))+J.integral (R x (ε (ns n))) ω):=by
    funext n
    exact ho (ns n)
  simp only [Function.comp_def] at hright
  rw [←he] at hright
  exact tendsto_nhds_unique (hleft.comp hns.tendsto_atTop) hright

end SHE.HeatObservationEndpointLimit
