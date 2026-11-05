module
public import SHE.SingleNativeHeatEquation
public import SHE.ShiftedOriginalNativeEquation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.RandomInitialSingleHeatEquation
open MeasureTheory Set PredictableL2 NativeHeatObservation FiniteHaar DyadicApproximation
open OrthogonalItoChannels StoppedFourier PredictableItoRotation
open scoped NNReal ENNReal
local instance randomSingle_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance randomSingle_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=1)).repr.toHomeomorph.secondCountableTopology
local instance randomSingle_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance randomSingle_realSigma:MeasurableSpace RealL2:=borel _
local instance randomSingle_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance randomSingle_bothSigma:MeasurableSpace (Both RealL2):=borel _
local instance randomSingle_bothBorel:BorelSpace (Both RealL2):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(D:SmoothApproximation.ScalarData)

/-- The actual random-initial SINGLE cylindrical-noise observable model.
The initial datum is known at time zero; the original positive heat
observations use the exact propagated random initial state. -/
structure Data(J:StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓕 μ H)(ξ:Ω→RealL2) where
  initial_measurable:StronglyMeasurable[𝓕 0] ξ
  value:ℝ≥0→Ω→RealL2
  initial:value 0=ξ
  continuous:∀ω,Continuous (fun t=>value t ω)
  predictable:StronglyMeasurable[𝓕.predictable] (Function.uncurry value)
  equation:∀q:ℝ≥0,q≤H→∀(ε:ℝ)(hε:0<ε)(x:HeatCircle),
    (fun ω=>functional ε x (value q ω))=ᵐ[μ]
      (fun ω=>functional ((q:ℝ)+ε) x (ξ ω)+J.integral
        (SingleNativeHeatEquation.row 𝓕 μ H D (Function.uncurry value) predictable
          (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x) ω)

variable(U:ℝ≥0×Ω→RealL2)(hU:StronglyMeasurable[𝓕.predictable] U)

/-- The original augmented physical row is exactly the left-channel
embedding of its genuine single physical row. Its auxiliary coordinate
is zero by the checked physical row formula, not an extra hypothesis. -/
theorem row_eq_left{T t:ℝ}(ht:t<T)(x:HeatCircle):
    processIsometry 𝓕 μ H (fun _=>left (C:=RealL2)) (left_measurable 𝓕)
      (SingleNativeHeatEquation.row 𝓕 μ H D U hU ht x)=
      PredictableScalarHaarRotation.originalRow 𝓕 μ H D U hU ht x:=by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [processIsometry_ae 𝓕 μ H (fun _=>left (C:=RealL2)) (left_measurable 𝓕)
      (SingleNativeHeatEquation.row 𝓕 μ H D U hU ht x),
    SingleNativeHeatEquation.row_ae 𝓕 μ H D U hU ht x,
    PredictableScalarHaarRotation.originalRow_ae 𝓕 μ H D U hU ht x] with p hp hs ho
  rw [hp,hs,ho]
  split_ifs <;> rfl

theorem integral_row(B:StandardTerminalIto (C:=Both RealL2) (E:=ℝ) 𝓕 μ H)
    {T t:ℝ}(ht:t<T)(x:HeatCircle):
    (leftIntegral 𝓕 μ H B).integral (SingleNativeHeatEquation.row 𝓕 μ H D U hU ht x)=
      B.integral (PredictableScalarHaarRotation.originalRow 𝓕 μ H D U hU ht x):=by
  change B.integral (processIsometry 𝓕 μ H (fun _=>left (C:=RealL2)) (left_measurable 𝓕)
    (SingleNativeHeatEquation.row 𝓕 μ H D U hU ht x))=_
  rw [row_eq_left]

variable(B:StandardTerminalIto (C:=Both RealL2) (E:=ℝ) 𝓕 μ H)(ξ:Ω→RealL2)
theorem original_equation(S:ShiftedOriginalNativeEquation.RandomInitialData 𝓕 μ H D B ξ)
    (q:ℝ≥0)(hq:q≤H)(ε:ℝ)(hε:0<ε)(x:HeatCircle):
    (fun ω=>functional ε x (S.value q ω))=ᵐ[μ]
      (fun ω=>functional ((q:ℝ)+ε) x (ξ ω)+
        (leftIntegral 𝓕 μ H B).integral (SingleNativeHeatEquation.row 𝓕 μ H D
          (Function.uncurry S.value) S.predictable (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x) ω):=by
  let a:Lp ℝ 2 μ:=(leftIntegral 𝓕 μ H B).integral (SingleNativeHeatEquation.row 𝓕 μ H D
    (Function.uncurry S.value) S.predictable (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x)
  let b:Lp ℝ 2 μ:=B.integral (PredictableScalarHaarRotation.originalRow 𝓕 μ H D
    (Function.uncurry S.value) S.predictable (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x)
  have hi:a=b:=integral_row 𝓕 μ H D (Function.uncurry S.value) S.predictable B (by linarith) x
  have he:=S.equation q hq ε hε x
  filter_upwards [he] with ω hω
  change functional ε x (S.value q ω)=functional ((q:ℝ)+ε) x (ξ ω)+a ω
  change functional ε x (S.value q ω)=functional ε x (heat (q:ℝ) (ξ ω))+b ω at hω
  have hh:functional ε x (heat (q:ℝ) (ξ ω))=functional ((q:ℝ)+ε) x (ξ ω):=by
    exact (functional_heat hε q.2 x (ξ ω)).trans
      (congrArg (fun r:ℝ=>functional r x (ξ ω)) (add_comm ε (q:ℝ)))
  exact hω.trans (congrArg₂ (fun r s:ℝ=>r+s) hh
    (congrArg (fun z:Lp ℝ 2 μ=>z ω) hi.symm))

/-- Project an actual shifted augmented original equation to the SAME
single physical noise channel and SAME state/initial datum. All integral
and semigroup identities are proved internally. -/
def of_original(S:ShiftedOriginalNativeEquation.RandomInitialData 𝓕 μ H D B ξ):
    Data 𝓕 μ H D (leftIntegral 𝓕 μ H B) ξ where
  initial_measurable:=S.initial_measurable
  value:=S.value
  initial:=S.initial
  continuous:=S.continuous
  predictable:=S.predictable
  equation:=original_equation 𝓕 μ H D B ξ S

/-- A genuine conditional model whose initial state is almost surely a
fixed x is a supplied deterministic-initial single-noise model. No
pointwise replacement of the actual state trajectory is made. -/
def freeze(J:StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓕 μ H)(ξ:Ω→RealL2)
    (S:Data 𝓕 μ H D J ξ)(u₀:RealL2)(hξ:ξ=ᵐ[μ] fun _=>u₀):
    SingleNativeHeatEquation.Data 𝓕 μ H D J u₀ where
  value:=S.value
  continuous:=S.continuous
  predictable:=S.predictable
  equation:=by
    intro q hq ε hε x
    filter_upwards [S.equation q hq ε hε x,hξ] with ω he hξ
    rw [hξ] at he
    exact he
end SHE.RandomInitialSingleHeatEquation
