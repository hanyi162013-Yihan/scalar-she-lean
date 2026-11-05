module
public import SHE.OriginalNativeWhiteHeatContinuity
public import SHE.ConditionalCanonicalItoLimit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
namespace SHE.OriginalNativeDenseObservationCompletion
open MeasureTheory Set PredictableL2 StoppedFourier NativeHeatObservation DyadicApproximation FiniteHaar Filter
open scoped NNReal ENNReal Topology
local instance denseObservation_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance denseObservation_realSigma : MeasurableSpace RealL2:=borel _
local instance denseObservation_realBorel : BorelSpace RealL2:=⟨rfl⟩
variable{Ω:Type*}[MeasurableSpace Ω]
variable(U:ℝ≥0→Ω→RealL2)

def residual(q:ℝ≥0)(ε:ℝ)(x:HeatCircle)(ω:Ω):ℝ:=
  functional ε x (U q ω)-functional ((q:ℝ)+ε) x (U 0 ω)

/-- Actual observed path residuals are continuous in native time, positive
heat gap and center, on every continuous state path. -/
theorem residual_tendsto (hc:∀ω,Continuous (fun t=>U t ω))
    (q:ℝ≥0)(ε:ℝ)(hε:0<ε)(x:HeatCircle)
    (qn:ℕ→ℝ≥0)(en:ℕ→ℝ)(xn:ℕ→HeatCircle)
    (hq:Tendsto qn atTop (𝓝 q))(he:Tendsto en atTop (𝓝 ε))(hx:Tendsto xn atTop (𝓝 x))(ω:Ω):
    Tendsto (fun n=>residual U (qn n) (en n) (xn n) ω) atTop (𝓝 (residual U q ε x ω)):=by
  have hstate:Tendsto (fun n=>U (qn n) ω) atTop (𝓝 (U q ω)):=(hc ω).tendsto q |>.comp hq
  have hpar:Tendsto (fun n=>((en n,xn n),U (qn n) ω)) atTop (𝓝 ((ε,x),U q ω)):=
    (he.prodMk_nhds hx).prodMk_nhds hstate
  have h1:Tendsto (fun n=>functional (en n) (xn n) (U (qn n) ω)) atTop
      (𝓝 (functional ε x (U q ω))):=by
    simpa only[Function.comp_def] using
      (OriginalNativeHeatParameterContinuity.functional_joint hε x (U q ω)).tendsto.comp hpar
  have hqr:Tendsto (fun n=>(qn n:ℝ)) atTop (𝓝 (q:ℝ)):=
    (continuous_subtype_val.tendsto q).comp hq
  have hpar0:Tendsto (fun n=>(((qn n:ℝ)+en n,xn n),U 0 ω)) atTop
      (𝓝 (((q:ℝ)+ε,x),U 0 ω)):=((hqr.add he).prodMk_nhds hx).prodMk_nhds tendsto_const_nhds
  have h2:Tendsto (fun n=>functional ((qn n:ℝ)+en n) (xn n) (U 0 ω)) atTop
      (𝓝 (functional ((q:ℝ)+ε) x (U 0 ω))):=by
    simpa only[Function.comp_def] using
      (OriginalNativeHeatParameterContinuity.functional_joint (by positivity) x (U 0 ω)).tendsto.comp hpar0
  exact h1.sub h2

variable(D:SmoothApproximation.ScalarData)(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)
variable(μ:Measure Ω)[IsFiniteMeasure μ](H:ℝ≥0)
variable(hU:IsStronglyPredictable 𝓕 U)

/-- Countable dense-parameter scalar equations extend to the arbitrary
limit parameter through the SAME original conditional scalar integral.
Both the observed and genuine Process-L2 limits are derived internally. -/
theorem equation_of_sequence (J:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hc:∀ω,Continuous (fun t=>U t ω))
    (q:ℝ≥0)(ε:ℝ)(hε:0<ε)(x:HeatCircle)
    (qn:ℕ→ℝ≥0)(en:ℕ→ℝ)(hnpos:∀n,0<en n)(xn:ℕ→HeatCircle)
    (hq:Tendsto qn atTop (𝓝 q))(he:Tendsto en atTop (𝓝 ε))(hx:Tendsto xn atTop (𝓝 x))
    (hcell:∀n,residual U (qn n) (en n) (xn n)=ᵐ[μ]
      (fun ω=>J.integral (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H
        (qn n) (en n) (hnpos n) (xn n)) ω)):
    residual U q ε x=ᵐ[μ]
      (fun ω=>J.integral (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H q ε hε x) ω):=by
  apply ConditionalCanonicalItoLimit.identify 𝓕 μ H J
    (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H q ε hε x)
    (fun n=>OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H (qn n) (en n) (hnpos n) (xn n))
    (fun n=>residual U (qn n) (en n) (xn n)) (residual U q ε x)
  · exact OriginalNativeWhiteHeatRows.input_tendsto D U 𝓕 hU μ H q ε hε x qn en hnpos xn hq he hx
  · exact fun n=>(hcell n).symm
  · exact ae_of_all _ (residual_tendsto U hc q ε hε x qn en xn hq he hx)
end SHE.OriginalNativeDenseObservationCompletion
