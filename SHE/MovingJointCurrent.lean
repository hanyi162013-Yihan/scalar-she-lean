module
public import SHE.NativeJointGammaCurrent
public import SHE.NativeMovingGammaClock
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.MovingJointCurrent
open Set MeasureTheory PredictableL2 NativeHeatObservation DyadicApproximation StoppedFourier
open scoped NNReal ENNReal
local instance movingJointCurrent_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingJointCurrent_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingJointCurrent_realSigma : MeasurableSpace RealL2:=borel _
local instance movingJointCurrent_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance movingJointCurrent_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance movingJointCurrent_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance movingJointCurrent_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance movingJointCurrent_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)
variable (U V:ℝ≥0×Ω→RealL2)(hU:StronglyMeasurable[𝓕.predictable] U)(hV:StronglyMeasurable[𝓕.predictable] V)
variable (Λ θ W h:ℝ)
def state (z:ℝ×(ℝ≥0×Ω)):RealL2:=
  NativeJointGammaCurrent.state U V Λ θ (NativeMovingGammaClock.terminal W h z.1) z.2

include hU hV in
/-- Literal joint backward currents remain jointly predictable with a
moving full target. The future-age damping stays inside this state. -/
theorem state_predictable:
    StronglyMeasurable[((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable)] (state U V Λ θ W h):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hcHeat:Continuous (fun p:ℝ×RealL2=>(p.1/timeScale,p.2)):=
    (continuous_fst.div_const timeScale).prodMk continuous_snd
  have hheat:=RealHeat.continuous_realHeat_action.comp hcHeat
  change Continuous (fun p:ℝ×RealL2=>heat p.1 p.2) at hheat
  have htime:=PredictableClock.real_time_measurable 𝓕
  have hage:Measurable (fun z:ℝ×(ℝ≥0×Ω)=>
      (NativeMovingGammaClock.terminal W h z.1:ℝ)-(z.2.1:ℝ)):=
    (NNReal.continuous_coe.measurable.comp ((NativeMovingGammaClock.terminal_measurable W h).comp measurable_fst)).sub
      (htime.comp measurable_snd)
  have hu:=hU.comp_measurable (measurable_snd:Measurable (fun z:ℝ×(ℝ≥0×Ω)=>z.2))
  have hv:=hV.comp_measurable (measurable_snd:Measurable (fun z:ℝ×(ℝ≥0×Ω)=>z.2))
  have h0:=hheat.comp_stronglyMeasurable (hage.stronglyMeasurable.prodMk hu)
  have h1:=hheat.comp_stronglyMeasurable (hage.stronglyMeasurable.prodMk (hv.sub hu))
  have he:=((hage.const_mul (-Λ)).exp).stronglyMeasurable
  exact h0.add ((he.smul h1).const_smul θ)

include hU hV in
theorem scalar_predictable:
    @Measurable ((ℝ×(ℝ≥0×Ω))×HeatCircle) ℝ
      (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _
      (PredictableScalarField.nativeField (state U V Λ θ W h)):=by
  letI:MeasurableSpace (ℝ×(ℝ≥0×Ω)):=(inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable
  exact PredictableScalarField.nativeField_measurable (state_predictable 𝓕 U V hU hV Λ θ W h).measurable
end SHE.MovingJointCurrent
