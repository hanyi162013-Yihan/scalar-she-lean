module
public import SHE.RawCylindricalCoordinates
public import SHE.NativeTwoChannelNoiseBasis
public import SHE.TwoChannelConvolutionLaw
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
namespace SHE.TwoChannelRawDriver
open MeasureTheory PredictableL2 OrthogonalItoChannels PredictableItoRotation FiniteHaar StoppedItoInputs
open scoped NNReal ENNReal
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)

def channels(b:Bool):StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H:=
  if b then leftIntegral 𝓕 μ H J else rightIntegral 𝓕 μ H J

theorem mapped_stop (L:RealHaarInput→ₗᵢ[ℝ] Both RealHaarInput)
    (hL:@Measurable ((ℝ≥0×Ω)×RealHaarInput) (Both RealHaarInput)
      (𝓕.predictable.prod (borel RealHaarInput)) _ (fun p=>L p.2))
    (i:HaarNode)(t:ℝ≥0):
    processIsometry 𝓕 μ H (fun _=>L) hL
      (stop 𝓕 μ H t (RotatedCylindricalCoordinates.constant 𝓕 μ H (NativeTwoChannelNoiseBasis.haar i)))=
    stop 𝓕 μ H t (RotatedCylindricalCoordinates.constant 𝓕 μ H (L (NativeTwoChannelNoiseBasis.haar i))):=by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [processIsometry_ae 𝓕 μ H (fun _=>L) hL
      (stop 𝓕 μ H t (RotatedCylindricalCoordinates.constant 𝓕 μ H (NativeTwoChannelNoiseBasis.haar i))),
    stop_ae 𝓕 μ H t (RotatedCylindricalCoordinates.constant 𝓕 μ H (NativeTwoChannelNoiseBasis.haar i)),
    stop_ae 𝓕 μ H t (RotatedCylindricalCoordinates.constant 𝓕 μ H (L (NativeTwoChannelNoiseBasis.haar i))),
    RotatedCylindricalCoordinates.constant_ae 𝓕 μ H (NativeTwoChannelNoiseBasis.haar i),
    RotatedCylindricalCoordinates.constant_ae 𝓕 μ H (L (NativeTwoChannelNoiseBasis.haar i))] with p hm hs ht hi ho
  rw [hm,hs,ht]
  by_cases hin:p∈before (Ω:=Ω) t
  · rw [Set.indicator_of_mem hin,Set.indicator_of_mem hin,hi,ho]
  · rw [Set.indicator_of_notMem hin,Set.indicator_of_notMem hin,map_zero]

/-- Both literal Haar drivers are coordinates of the SAME whole scalar
integral, with exactly the untouched stopped deterministic inputs. -/
theorem driver_eq(b:Bool)(i:HaarNode)(t:ℝ≥0):
    TwoChannelConvolutionLaw.driver 𝓕 μ H (channels 𝓕 μ H J) b i t=
      RawCylindricalCoordinates.value 𝓕 μ H NativeTwoChannelNoiseBasis.both J (b,i) t:=by
  cases b
  · unfold TwoChannelConvolutionLaw.driver LeftFrozenConvolutionLaw.driver BoundedHilbertItoCell.driver
    change (fun ω=>J.integral (processIsometry 𝓕 μ H (fun _=>right (C:=RealHaarInput))
      (right_measurable 𝓕) (stop 𝓕 μ H t (RotatedCylindricalCoordinates.constant 𝓕 μ H
        (NativeTwoChannelNoiseBasis.haar i)))) ω)=_
    rw [mapped_stop 𝓕 μ H right (right_measurable 𝓕) i t]
    rfl
  · unfold TwoChannelConvolutionLaw.driver LeftFrozenConvolutionLaw.driver BoundedHilbertItoCell.driver
    change (fun ω=>J.integral (processIsometry 𝓕 μ H (fun _=>left (C:=RealHaarInput))
      (left_measurable 𝓕) (stop 𝓕 μ H t (RotatedCylindricalCoordinates.constant 𝓕 μ H
        (NativeTwoChannelNoiseBasis.haar i)))) ω)=_
    rw [mapped_stop 𝓕 μ H left (left_measurable 𝓕) i t]
    rfl

variable{Ω':Type*}[MeasurableSpace Ω']
theorem law_map (𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (K:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓖 ν H)
    (hJ:CylindricalDriverLaw.Law μ H (RawCylindricalCoordinates.value 𝓕 μ H NativeTwoChannelNoiseBasis.both J))
    (hK:CylindricalDriverLaw.Law ν H (RawCylindricalCoordinates.value 𝓖 ν H NativeTwoChannelNoiseBasis.both K)):
    μ.map (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓕 μ H (channels 𝓕 μ H J) b i t ω)=
      ν.map (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓖 ν H (channels 𝓖 ν H K) b i t ω):=by
  let decode:(((Bool×HaarNode)×ℝ≥0)→ℝ)→(Bool→HaarNode→ℝ≥0→ℝ):=
    fun x b i t=>x ((b,i),t)
  have hd:Measurable decode:=measurable_pi_iff.mpr (fun b=>measurable_pi_iff.mpr
    (fun i=>measurable_pi_iff.mpr (fun t=>measurable_pi_apply ((b,i),t))))
  have hh:=congrArg (fun m:Measure (((Bool×HaarNode)×ℝ≥0)→ℝ)=>m.map decode)
    (RawCylindricalCoordinates.map_eq 𝓕 μ H NativeTwoChannelNoiseBasis.both J 𝓖 ν K hJ hK)
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
