module
public import SHE.OriginalNativeRowContinuity
public import SHE.NativeOutputTranslation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.OriginalNativeHeatParameterContinuity
open MeasureTheory Set Filter StoppedFourier NativeHeatObservation DyadicApproximation AddCircle
open scoped Topology ENNReal
local instance heatParameterContinuity_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance heatParameterContinuity_period : Fact (0<2*Real.pi):=⟨by positivity⟩

/-- A native heat row is the genuine Haar translate of its centered row. -/
theorem translate_heat {τ:ℝ}(hτ:0<τ)(x:HeatCircle):
    GaussianAudit.circleTranslate x (circleHeat τ 0)=circleHeat τ x:=by
  change NativeOutputTranslation.translate x (circleHeat τ 0)=circleHeat τ x
  apply (fourierBasis (T:=2*Real.pi)).repr.injective
  apply lp.ext
  funext n
  simp only[fourierBasis_repr,NativeOutputTranslation.fourierCoeff_translate,
    circleHeat_fourierCoeff hτ,heatCoeff,fourier_eval_zero]
  ring

/-- Joint physical-age and native-center continuity holds in actual L2. -/
theorem circleHeat_joint {τ:ℝ}(hτ:0<τ)(x:HeatCircle):
    ContinuousAt (fun p:ℝ×HeatCircle=>circleHeat p.1 p.2) (τ,x):=by
  have hp:ContinuousAt (fun p:ℝ×HeatCircle=>(p.2,circleHeat p.1 0)) (τ,x):=
    continuous_snd.continuousAt.prodMk
      ((HeatAgeContinuity.continuousAt_circleHeat_age hτ 0).comp
        (f:=fun p:ℝ×HeatCircle=>p.1) (x:=(τ,x)) continuous_fst.continuousAt)
  have hc:=GaussianAudit.continuous_circleTranslate.continuousAt.comp hp
  have he:(fun p:ℝ×HeatCircle=>circleHeat p.1 p.2)=ᶠ[𝓝 (τ,x)]
      (fun p=>GaussianAudit.circleTranslate p.2 (circleHeat p.1 0)):=by
    filter_upwards[(continuous_fst.tendsto (τ,x)).eventually (eventually_gt_nhds hτ)] with p hp
    exact (translate_heat hp p.2).symm
  exact hc.congr_of_eventuallyEq he

/-- Original real heat tests retain joint age/center continuity. -/
theorem test_joint {τ:ℝ}(hτ:0<τ)(x:HeatCircle):
    ContinuousAt (fun p:ℝ×HeatCircle=>ScalarHaarHeatRows.test p.1 p.2) (τ,x):=by
  have hp:=CircleNormalization.push.symm.continuous.continuousAt.comp (circleHeat_joint hτ x)
  exact (Complex.reCLM.compLpL 2 (haarAddCircle (T:=(1:ℝ)))).continuous.continuousAt.comp hp

/-- Actual observation functionals vary continuously with all three
parameters, with no spatial-version assumption. -/
theorem functional_joint {τ:ℝ}(hτ:0<τ)(x:HeatCircle)(u:RealL2):
    ContinuousAt (fun p:(ℝ×HeatCircle)×RealL2=>functional p.1.1 p.1.2 p.2) ((τ,x),u):=by
  change ContinuousAt (fun p:(ℝ×HeatCircle)×RealL2=>
    (inner ℂ (circleHeat p.1.1 p.1.2) (embed p.2)).re) ((τ,x),u)
  have hrow:ContinuousAt (fun p:(ℝ×HeatCircle)×RealL2=>circleHeat p.1.1 p.1.2) ((τ,x),u):=
    (circleHeat_joint hτ x).comp (f:=fun p:(ℝ×HeatCircle)×RealL2=>p.1)
      (x:=((τ,x),u)) continuous_fst.continuousAt
  have hstate:ContinuousAt (fun p:(ℝ×HeatCircle)×RealL2=>embed p.2) ((τ,x),u):=
    embed.continuous.continuousAt.comp continuous_snd.continuousAt
  exact Complex.continuous_re.continuousAt.comp (hrow.inner (𝕜:=ℂ) hstate)

/-- The literal rough nonlinear original row is jointly continuous in
positive heat age, native center and the actual state. Holder continuity
of g suffices; no smoothness or supplied row-continuity premise is used. -/
theorem input_joint (D:SmoothApproximation.ScalarData) {τ:ℝ}(hτ:0<τ)(x:HeatCircle)(u:RealL2):
    ContinuousAt (fun p:(ℝ×HeatCircle)×RealL2=>OriginalScalarInputContinuity.input D p.2
      (ScalarHaarHeatRows.test p.1.1 p.1.2)) ((τ,x),u):=by
  have hu:Tendsto (fun p:(ℝ×HeatCircle)×RealL2=>p.2) (𝓝 ((τ,x),u)) (𝓝 u):=
    continuous_snd.tendsto _
  have hv:Tendsto (fun p:(ℝ×HeatCircle)×RealL2=>ScalarHaarHeatRows.test p.1.1 p.1.2)
      (𝓝 ((τ,x),u)) (𝓝 (ScalarHaarHeatRows.test τ x)):=
    (test_joint hτ x).tendsto.comp (continuous_fst.tendsto _)
  exact OriginalScalarInputContinuity.input_tendsto D _ _ u _ hu hv _
    (OriginalScalarInputContinuity.heat_test_bound hτ x)
end SHE.OriginalNativeHeatParameterContinuity
