module
public import SHE.NativeFrozenGaussianTransition
public import SHE.NativeFrozenSpatialObservation
public import SHE.FullHorizonEndpointStop
public import SHE.TwoChannelPastDifference
public import SHE.RandomGaussianMatrixIto
public import SHE.GaussianStandardRealization

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeFrozenGaussianObservations
open Set MeasureTheory ProbabilityTheory PredictableL2 GaussianMatrixFamily NativeFrozenGaussianRows
open GaussianMatrixGramCurve ControlledProfile OrthogonalItoChannels FiniteHaar StoppedFourier
open scoped NNReal ENNReal
local instance period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeSigma : MeasurableSpace CircleL2:=borel _
local instance nativeBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeSecond : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ]
variable (v b:ℝ≥0) (hvb:v≤b) (P:CanonicalCovariance.ProfileParameters) (Λ κ:ℝ) (hκ:0<κ) (hκP:κ<P.lower)
variable {n:ℕ}(side:Fin n→Bool) (ξ:Fin n→ℝ) (center:Fin n→HeatCircle)
variable (hΛ:0≤Λ) (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
local notation "Curve"=>NativeFrozenGaussianCurve.curve 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center

variable (H:ℝ≥0) (hbH:b≤H) (data:Ω→Inputs) (hdata:Measurable[𝓕 v] data)
local notation "R"=>NativeFrozenGaussianRows.rows 𝓕 μ H v b P Λ κ hκ hκP side ξ center data hdata hbH
local notation "Q"=>GaussianStoppedRows.rows 𝓕 μ H v b R


variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
local notation "Y"=>SingularVectorIntegral.value 𝓕 μ H b J (0:WordRecursion.State n) Q



def scalarRow (i:Fin n):Process (E:=RealHaarInput) 𝓕 μ H:=
  if side i then NativeFrozenSpatialObservation.row 𝓕 μ H b b v (sub_pos.mpr hκP)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP)
    (FrozenReferenceFields.field P Λ κ (ξ i) hκP v data)
    (FrozenReferenceFields.field_predictable 𝓕 P Λ κ (ξ i) hκP v data hdata) hbH le_rfl (center i) 0
  else NativeFrozenSpatialObservation.row 𝓕 μ H b b v hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH le_rfl (center i) 0

local notation "S" i=>scalarRow 𝓕 μ v b P Λ κ hκ hκP side ξ center H hbH data hdata i

theorem input_eq (i:Fin n):Q i=NativeFrozenGaussianRows.mapRow 𝓕 μ H (side i) (S i):=by
  unfold GaussianStoppedRows.rows NativeFrozenGaussianRows.rows
  by_cases hi:side i
  · simp only [hi,ite_true,scalarRow,Bool.false_eq_true,ite_false]
    unfold NativeFrozenGaussianRows.mapRow NativeFrozenGaussianRows.residual
    rw [PastItoAlgebra.post_isometry,←RotatedItoAlgebra.map_stop,
      TwoChannelPastDifference.stop_post,FullHorizonEndpointStop.self]
    simp only [NativeFrozenSpatialObservation.row,max_self,add_zero]
  · simp only [hi,ite_false,scalarRow,Bool.false_eq_true,ite_true]
    unfold NativeFrozenGaussianRows.mapRow NativeFrozenGaussianRows.additive DeterministicNativeHeatRows.process
    rw [PastItoAlgebra.post_isometry,←RotatedItoAlgebra.map_stop,
      TwoChannelPastDifference.stop_post,FullHorizonEndpointStop.self]
    simp only [NativeFrozenSpatialObservation.row,max_self,add_zero]

/-- Each terminal coordinate is the literal SAME-J scalar observation
in its original left or right channel. -/
theorem terminal_coordinate (i:Fin n) (ω:Ω):
    GaussianStoppedRows.terminal 𝓕 μ H v b R J (0:WordRecursion.State n) ω i=
      if side i then (rightIntegral 𝓕 μ H J).integral (S i) ω
      else (leftIntegral 𝓕 μ H J).integral (S i) ω:=by
  have he:=input_eq 𝓕 μ v b P Λ κ hκ hκP side ξ center H hbH data hdata i
  simp only [GaussianStoppedRows.terminal,WithLp.ofLp_toLp,PiLp.zero_apply,zero_add]
  rw [he]
  by_cases hi:side i
  · simp only [hi,ite_true]
    rfl
  · simp only [hi,ite_false]
    rfl

end SHE.NativeFrozenGaussianObservations
