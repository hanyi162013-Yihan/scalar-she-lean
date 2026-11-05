module
public import SHE.OriginalSingleHaarApproximation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeWhiteToPhysicalEquation
open MeasureTheory PredictableL2 NativeHeatObservation FiniteHaar DyadicApproximation
open StoppedFourier
open scoped NNReal ENNReal
local instance whitePhysical_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance whitePhysical_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=1)).repr.toHomeomorph.secondCountableTopology
local instance whitePhysical_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance whitePhysical_realSigma:MeasurableSpace RealL2:=borel _
local instance whitePhysical_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance whitePhysical_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance whitePhysical_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(J:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)

/-- Physical cylindrical integration constructed from the SAME white
integral by the inverse fixed physical Haar coordinates. -/
def physical:StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓕 μ H:=
  PredictableItoRotation.integral 𝓕 μ H
    (fun _=>OriginalNativeFrozenRows.coordinates.symm.toLinearIsometry)
    (OriginalNativeFrozenRows.coordinates.symm.continuous.measurable.comp measurable_snd) J

variable(D:SmoothApproximation.ScalarData)(U:ℝ≥0→Ω→RealL2)
variable(hU:IsStronglyPredictable 𝓕 U)

/-- Exact actual white/physical observation-input identity, with no
replacement of the state or stochastic integral. -/
theorem integral_row(q:ℝ≥0)(ε:ℝ)(hε:0<ε)(x:HeatCircle):
    (physical 𝓕 μ H J).integral (SingleNativeHeatEquation.row 𝓕 μ H D
      (Function.uncurry U) hU (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x)=
    J.integral (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H q ε hε x):=by
  change J.integral (OriginalSingleHaarInputs.row 𝓕 μ H D U hU q ε hε x)=_
  rw [OriginalSingleHaarApproximation.row_eq]

/-- The residual equation obtained under the actual conditional white
model. This contains only the original heat observations and actual
white stochastic inputs, not a mild or solution-law premise. -/
def ResidualEquation:Prop:=∀q:ℝ≥0,q≤H→∀(ε:ℝ)(hε:0<ε)(x:HeatCircle),
    (fun ω=>functional ε x (U q ω)-functional ((q:ℝ)+ε) x (U 0 ω))=ᵐ[μ]
      J.integral (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H q ε hε x)

theorem equation_of_white(he:ResidualEquation 𝓕 μ H J D U hU)
    (u₀:RealL2)(hzero:U 0=ᵐ[μ] fun _=>u₀):
    SingleNativeHeatEquation.Equation 𝓕 μ H D (physical 𝓕 μ H J) u₀ U hU:=by
  intro q hq ε hε x
  let a:Lp ℝ 2 μ:=(physical 𝓕 μ H J).integral (SingleNativeHeatEquation.row 𝓕 μ H D
    (Function.uncurry U) hU (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x)
  let b:Lp ℝ 2 μ:=J.integral (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H q ε hε x)
  have hi:a=b:=integral_row 𝓕 μ H J D U hU q ε hε x
  filter_upwards [he q hq ε hε x,hzero] with ω hω hz
  change functional ε x (U q ω)=functional ((q:ℝ)+ε) x u₀+a ω
  change functional ε x (U q ω)-functional ((q:ℝ)+ε) x (U 0 ω)=b ω at hω
  rw [hz] at hω
  have hab:a ω=b ω:=congrArg (fun z:Lp ℝ 2 μ=>z ω) hi
  linarith only [hω,hab]

/-- A derived conditional white residual equation with almost surely
fixed initial state yields the genuine supplied single-physical-noise
model. Its value is EXACTLY the original U. -/
def of_white(hc:∀ω,Continuous (fun t=>U t ω))(he:ResidualEquation 𝓕 μ H J D U hU)
    (u₀:RealL2)(hzero:U 0=ᵐ[μ] fun _=>u₀):
    SingleNativeHeatEquation.Data 𝓕 μ H D (physical 𝓕 μ H J) u₀ where
  value:=U
  continuous:=hc
  predictable:=hU
  equation:=equation_of_white 𝓕 μ H J D U hU he u₀ hzero
end SHE.NativeWhiteToPhysicalEquation
