module
public import SHE.FullHorizonEndpointStop
public import SHE.FullHorizonEndpointVersion
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.FullHorizonEndpointPositive
open MeasureTheory Set PredictableL2 StoppedItoInputs FiniteHaar StoppedFourier
open scoped NNReal ENNReal
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H b:ℝ≥0)
variable {ell M T:ℝ}(hell:0<ell)(hM:0≤M)
variable (f:ℝ≥0×Ω→EllipticField ell M)(hf:StronglyMeasurable[𝓕.predictable] f)
variable (hT:(b:ℝ)<T)(x:HeatCircle)(hbH:b≤H)

theorem eq_prefix : FullHorizonEndpoint.process 𝓕 μ H b hell hM f hf hT.le x hbH=
    NativeObservationProcess.process 𝓕 μ H hell hM f hf hT x:=by
  rw [←FullHorizonEndpointVersion.stop_eq_prefix 𝓕 μ H b hell hM f hf hT.le x hbH b le_rfl hT,
    FullHorizonEndpointStop.self]

end SHE.FullHorizonEndpointPositive
