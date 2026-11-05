module
public import SHE.NativeFixedHaarInput
public import SHE.PredictableDamping
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.NativeDampedHaarInput
open Set MeasureTheory PredictableL2 FiniteHaar
open scoped NNReal ENNReal
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable {Λ ell M:ℝ}(hΛ:0≤Λ)(hell:0<ell)(hM:0≤M)
variable (f:ℝ≥0×Ω→EllipticField ell M)(hf:StronglyMeasurable[𝓕.predictable] f)

def raw(t:ℝ≥0)(p:ℝ≥0×Ω):RealHaarIntegrand.Columns:=
  Real.exp (-Λ*((t:ℝ)-(p.1:ℝ))) • NativeFixedHaarInput.raw hell f t p

def input(t:ℝ≥0)(htH:t≤H)(ht1:(t:ℝ)≤1):Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  PredictableContraction.weighted 𝓕 μ H (PredictableDamping.weight Λ t)
    (PredictableDamping.weight_predictable 𝓕 Λ t) (PredictableDamping.weight_bound hΛ t)
    (NativeFixedHaarInput.input 𝓕 μ H hell hM f hf t htH ht1)

theorem input_ae(t:ℝ≥0)(htH:t≤H)(ht1:(t:ℝ)≤1):
    input 𝓕 μ H hΛ hell hM f hf t htH ht1=ᵐ[energyMeasure μ H] raw (Λ:=Λ) hell f t:=by
  filter_upwards [PredictableContraction.weighted_ae 𝓕 μ H (PredictableDamping.weight Λ t)
    (PredictableDamping.weight_predictable 𝓕 Λ t) (PredictableDamping.weight_bound hΛ t)
    (NativeFixedHaarInput.input 𝓕 μ H hell hM f hf t htH ht1),
    NativeFixedHaarInput.input_ae 𝓕 μ H hell hM f hf t htH ht1] with p hp hq
  unfold input
  rw [hp,hq,raw]
  by_cases hs:(p.1:ℝ)≤t
  · rw [PredictableDamping.weight_eq hs]
  · rw [NativeFixedHaarInput.raw,NativeHeatObservation.kernel_zero hell (by linarith),smul_zero,smul_zero]
end SHE.NativeDampedHaarInput
