module
public import SHE.FullHorizonEndpoint
public import SHE.PastItoAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.FullHorizonEndpointStop
open MeasureTheory Set PredictableL2 StoppedItoInputs FiniteHaar StoppedFourier
open scoped NNReal ENNReal
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H b:ℝ≥0)
variable {ell M T:ℝ}(hell:0<ell)(hM:0≤M)
variable (f:ℝ≥0×Ω→EllipticField ell M)(hf:StronglyMeasurable[𝓕.predictable] f)
variable (hT:(b:ℝ)≤T)(x:HeatCircle)(hbH:b≤H)
local notation "R"=>FullHorizonEndpoint.process 𝓕 μ H b hell hM f hf hT x hbH

theorem self : stop 𝓕 μ H b R=R:=by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [stop_ae 𝓕 μ H b R,
    FullHorizonEndpoint.process_ae 𝓕 μ H b hell hM f hf hT x hbH] with p hs hp
  rw [hs]
  by_cases hb:p∈before (Ω:=Ω) (b:ℝ)
  · exact indicator_of_mem hb _
  · rw [indicator_of_notMem hb,hp,FullHorizonEndpoint.raw,indicator_of_notMem hb]

end SHE.FullHorizonEndpointStop
