module
public import SHE.RandomInitialSingleHeatEquation
public import SHE.NativeWhiteToPhysicalEquation
public import SHE.OriginalNativeDenseObservationCompletion
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.RandomInitialSingleWhiteEquation
open MeasureTheory PredictableL2 NativeHeatObservation FiniteHaar DyadicApproximation StoppedFourier
open scoped NNReal ENNReal
local instance randomWhite_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance randomWhite_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=1)).repr.toHomeomorph.secondCountableTopology
local instance randomWhite_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance randomWhite_realSigma:MeasurableSpace RealL2:=borel _
local instance randomWhite_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance randomWhite_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance randomWhite_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(D:SmoothApproximation.ScalarData)
variable(J:StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓕 μ H)(ξ:Ω→RealL2)
variable(S:RandomInitialSingleHeatEquation.Data 𝓕 μ H D J ξ)

/-- The original random-initial observable equation is an actual white
residual equation under the SAME fixed-coordinate rotated integral.
The initial state is identified by S.initial; no white equation premise
or representation of a stochastic integral as a path functional is used. -/
theorem residual(q:ℝ≥0)(hq:q≤H)(ε:ℝ)(hε:0<ε)(x:HeatCircle):
    OriginalNativeDenseObservationCompletion.residual S.value q ε x=ᵐ[μ]
      (OriginalSingleHaarInputs.integral 𝓕 μ H J).integral
        (OriginalNativeWhiteHeatRows.input D S.value 𝓕 S.predictable μ H q ε hε x):=by
  let a:Lp ℝ 2 μ:=J.integral (SingleNativeHeatEquation.row 𝓕 μ H D
    (Function.uncurry S.value) S.predictable (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x)
  let b:Lp ℝ 2 μ:=(OriginalSingleHaarInputs.integral 𝓕 μ H J).integral
    (OriginalNativeWhiteHeatRows.input D S.value 𝓕 S.predictable μ H q ε hε x)
  have hi:b=a:=OriginalSingleHaarApproximation.integral_input 𝓕 μ H D S.value S.predictable q ε hε x J
  filter_upwards [S.equation q hq ε hε x] with ω hω
  change functional ε x (S.value q ω)-functional ((q:ℝ)+ε) x (S.value 0 ω)=b ω
  change functional ε x (S.value q ω)=functional ((q:ℝ)+ε) x (ξ ω)+a ω at hω
  have h0:S.value 0 ω=ξ ω:=congrFun S.initial ω
  rw [h0]
  have hab:b ω=a ω:=congrArg (fun z:Lp ℝ 2 μ=>z ω) hi
  linarith only [hω,hab]

theorem equation:NativeWhiteToPhysicalEquation.ResidualEquation 𝓕 μ H
    (OriginalSingleHaarInputs.integral 𝓕 μ H J) D S.value S.predictable:=
  residual 𝓕 μ H D J ξ S
end SHE.RandomInitialSingleWhiteEquation
