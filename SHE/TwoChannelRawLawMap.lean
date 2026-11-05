module
public import SHE.TwoChannelRawDriver
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
namespace SHE.TwoChannelRawDriver
open MeasureTheory PredictableL2 OrthogonalItoChannels FiniteHaar
open scoped NNReal ENNReal
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable{Ω Ω':Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
theorem law_map_of_raw_map (𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (K:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓖 ν H)
    (hRaw:μ.map (fun ω=>fun p:(Bool×HaarNode)×ℝ≥0=>RawCylindricalCoordinates.value 𝓕 μ H NativeTwoChannelNoiseBasis.both J p.1 p.2 ω)=
      ν.map (fun ω=>fun p:(Bool×HaarNode)×ℝ≥0=>RawCylindricalCoordinates.value 𝓖 ν H NativeTwoChannelNoiseBasis.both K p.1 p.2 ω)):
    μ.map (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓕 μ H (channels 𝓕 μ H J) b i t ω)=
      ν.map (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓖 ν H (channels 𝓖 ν H K) b i t ω):=by
  let decode:(((Bool×HaarNode)×ℝ≥0)→ℝ)→(Bool→HaarNode→ℝ≥0→ℝ):=
    fun x b i t=>x ((b,i),t)
  have hd:Measurable decode:=measurable_pi_iff.mpr (fun b=>measurable_pi_iff.mpr
    (fun i=>measurable_pi_iff.mpr (fun t=>measurable_pi_apply ((b,i),t))))
  have hh:=congrArg (fun m:Measure (((Bool×HaarNode)×ℝ≥0)→ℝ)=>m.map decode)
    hRaw
  rw [Measure.map_map hd (measurable_pi_iff.mpr (fun p=>RawCylindricalCoordinates.value_measurable 𝓕 μ H _ J p.1 p.2)),
    Measure.map_map hd (measurable_pi_iff.mpr (fun p=>RawCylindricalCoordinates.value_measurable 𝓖 ν H _ K p.1 p.2))] at hh
  have hleft:(fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓕 μ H (channels 𝓕 μ H J) b i t ω)=
      decode ∘(fun ω=>fun p:(Bool×HaarNode)×ℝ≥0=>RawCylindricalCoordinates.value 𝓕 μ H NativeTwoChannelNoiseBasis.both J p.1 p.2 ω):=by
    funext ω b i t
    exact congrFun (driver_eq 𝓕 μ H J b i t) ω
  have hright:(fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓖 ν H (channels 𝓖 ν H K) b i t ω)=
      decode ∘(fun ω=>fun p:(Bool×HaarNode)×ℝ≥0=>RawCylindricalCoordinates.value 𝓖 ν H NativeTwoChannelNoiseBasis.both K p.1 p.2 ω):=by
    funext ω b i t
    exact congrFun (driver_eq 𝓖 ν H K b i t) ω
  rw [hleft,hright]
  exact hh
end SHE.TwoChannelRawDriver
