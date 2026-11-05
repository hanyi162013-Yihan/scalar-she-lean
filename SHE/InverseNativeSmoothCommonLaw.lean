module
public import SHE.NativeSmoothCommonLaw
public import SHE.InverseClockLocality
public import SHE.InverseClockChannels
public import SHE.InverseClockRawDriver
public import SHE.TwoChannelRawLawMap
public import SHE.ItoLocalityTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.InverseNativeSmoothCommonLaw
open MeasureTheory PredictableL2 LowBands OrthogonalItoChannels PredictableTimeDilation
open scoped NNReal ENNReal
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance : MeasurableSpace FiniteHaar.RealHaarInput:=borel _
local instance : BorelSpace FiniteHaar.RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both FiniteHaar.RealHaarInput):=borel _
local instance : BorelSpace (Both FiniteHaar.RealHaarInput):=⟨rfl⟩
variable{Ω Ω' D:Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ]
variable(c:ℝ≥0)(hc:0<c)(h:ℝ≥0)
local notation "FN"=>filtration 𝓕 (clock c hc)

theorem inverse_channel_naturality
    (I:Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) FN μ (c*h))
    (J:StandardTerminalIto (C:=Both FiniteHaar.RealHaarInput) (E:=ℝ) FN μ (c*h))
    (hIJ:∀b,NativeObservationNaturality.StandardScalarNaturality (I b)
      (TwoChannelRawDriver.channels FN μ (c*h) J b)):
    ∀b,NativeObservationNaturality.StandardScalarNaturality
      (inverseIntegral 𝓕 μ c hc h (I b))
      (TwoChannelRawDriver.channels 𝓕 μ h (inverseIntegral 𝓕 μ c hc h J) b):=by
  intro b
  have hh:=inverse_scalarNaturality 𝓕 μ c hc h (I b)
    (TwoChannelRawDriver.channels FN μ (c*h) J b) (hIJ b)
  cases b
  · change NativeObservationNaturality.StandardScalarNaturality _
      (inverseIntegral 𝓕 μ c hc h (rightIntegral FN μ (c*h) J)) at hh
    rw [inverse_rightIntegral] at hh
    exact hh
  · change NativeObservationNaturality.StandardScalarNaturality _
      (inverseIntegral 𝓕 μ c hc h (leftIntegral FN μ (c*h) J)) at hh
    rw [inverse_leftIntegral] at hh
    exact hh

theorem inverse_channel_locality
    (J:StandardTerminalIto (C:=Both FiniteHaar.RealHaarInput) (E:=ℝ) FN μ (c*h))
    (hlocal:StandardTerminalPastLocality J):
    ∀b,StandardTerminalPastLocality
      (TwoChannelRawDriver.channels 𝓕 μ h (inverseIntegral 𝓕 μ c hc h J) b):=by
  have hl:=InverseClockLocality.locality 𝓕 μ c hc h J hlocal
  intro b
  cases b
  · exact ItoLocalityTransport.rotation (C:=Both FiniteHaar.RealHaarInput)
      (D:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ h
      (fun _:ℝ≥0×Ω=>right (C:=FiniteHaar.RealHaarInput))
      (right_measurable (C:=FiniteHaar.RealHaarInput) 𝓕)
      (inverseIntegral 𝓕 μ c hc h J) hl
  · exact ItoLocalityTransport.rotation (C:=Both FiniteHaar.RealHaarInput)
      (D:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ h
      (fun _:ℝ≥0×Ω=>left (C:=FiniteHaar.RealHaarInput))
      (left_measurable (C:=FiniteHaar.RealHaarInput) 𝓕)
      (inverseIntegral 𝓕 μ c hc h J) hl

local notation "rate"=>NativeClock.rate
local notation "rp"=>NativeClock.rate_pos
variable[NormedAddCommGroup D][InnerProductSpace ℝ D][CompleteSpace D]
variable[MeasurableSpace D][BorelSpace D][SecondCountableTopology D]
variable(hh:(h:ℝ)≤1)(κ:ℝ)(hκ:0<κ){a:ℝ→ℝ}(ha:Measurable a)
variable{ell M K β:ℝ}(hell:0<ell)(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hK:0≤K)
variable(hholder:∀z w,|a z-a w|≤K*|z-w|^β)
variable(I:Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) (filtration 𝓕 (clock rate rp)) μ (rate*h))
variable(J:StandardTerminalIto (C:=Both FiniteHaar.RealHaarInput) (E:=ℝ) (filtration 𝓕 (clock rate rp)) μ (rate*h))
variable(B:Bool→ℝ≥0)(hBDG:∀b,StandardTerminalBDG16 (I b) (B b))
variable(hpos:0<h)(hnull:NullCompleteFiltration.ContainsNullSets (filtration 𝓕 (clock rate rp)) μ)
variable(hIJ:∀b,NativeObservationNaturality.StandardScalarNaturality (I b)
  (TwoChannelRawDriver.channels (filtration 𝓕 (clock rate rp)) μ (rate*h) J b))
variable(hlocal:StandardTerminalPastLocality J)
include hBDG hpos hnull hIJ hlocal in
/-- Actual native smooth models have a common law from the recognized
SAME native driver. All unit-clock law, locality, naturality, null and
BDG applicability is derived by exact inverse-clock identities. -/
theorem paths{Lip:ℝ≥0}(hLip:LipschitzWith Lip (fun x=>(a x:ℂ)))(u₀:StateL2)
    (A:NativeSmoothFirstConstruction.Model 𝓕 μ h hh κ hκ ha hell hb hβ hK hholder
      (fun b=>inverseIntegral 𝓕 μ rate rp h (I b)) u₀)
    (𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (I':Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2)
      (filtration 𝓖 (clock rate rp)) ν (rate*h))
    (J':StandardTerminalIto (C:=Both FiniteHaar.RealHaarInput) (E:=ℝ)
      (filtration 𝓖 (clock rate rp)) ν (rate*h))
    (B':Bool→ℝ≥0)(hBDG':∀b,StandardTerminalBDG16 (I' b) (B' b))
    (hnull':NullCompleteFiltration.ContainsNullSets (filtration 𝓖 (clock rate rp)) ν)
    (hIJ':∀b,NativeObservationNaturality.StandardScalarNaturality (I' b)
      (TwoChannelRawDriver.channels (filtration 𝓖 (clock rate rp)) ν (rate*h) J' b))
    (hlocal':StandardTerminalPastLocality J')
    (A':NativeSmoothFirstConstruction.Model 𝓖 ν h hh κ hκ ha hell hb hβ hK hholder
      (fun b=>inverseIntegral 𝓖 ν rate rp h (I' b)) u₀)
    (stateMap:StateL2→L[ℝ]D)
    (hJ:CylindricalDriverLaw.Law μ (rate*h)
      (RawCylindricalCoordinates.value (filtration 𝓕 (clock rate rp)) μ (rate*h) NativeTwoChannelNoiseBasis.both J))
    (hJ':CylindricalDriverLaw.Law ν (rate*h)
      (RawCylindricalCoordinates.value (filtration 𝓖 (clock rate rp)) ν (rate*h)
        NativeTwoChannelNoiseBasis.both J')):
    NativePathLawComparison.law (rate*h) μ
        (fun t ω=>stateMap (NativePairClock.path A.model.value t ω))
        (fun ω=>stateMap.continuous.comp (NativePairClock.path_continuous A.model.value A.model.continuous ω))=
      NativePathLawComparison.law (rate*h) ν
        (fun t ω=>stateMap (NativePairClock.path A'.model.value t ω))
        (fun ω=>stateMap.continuous.comp (NativePairClock.path_continuous A'.model.value A'.model.continuous ω)):=by
  have hbm(b:Bool):StandardTerminalBDG16 (I b) (max (B b) (B' b)):=by
    intro v
    apply (hBDG b v).trans
    gcongr
    exact_mod_cast le_max_left (B b) (B' b)
  have hbm'(b:Bool):StandardTerminalBDG16 (I' b) (max (B b) (B' b)):=by
    intro v
    apply (hBDG' b v).trans
    gcongr
    exact_mod_cast le_max_right (B b) (B' b)
  have hraw:=RawCylindricalCoordinates.map_eq (filtration 𝓕 (clock rate rp)) μ (rate*h) NativeTwoChannelNoiseBasis.both J
    (filtration 𝓖 (clock rate rp)) ν J' hJ hJ'
  have hunit:=InverseClockRawDriver.map_eq 𝓕 μ 𝓖 ν rate rp h NativeTwoChannelNoiseBasis.both J J' hraw
  have hdr:=TwoChannelRawDriver.law_map_of_raw_map 𝓕 μ h
    (inverseIntegral 𝓕 μ rate rp h J) 𝓖 ν (inverseIntegral 𝓖 ν rate rp h J') hunit
  exact NativeSmoothCommonLaw.paths 𝓕 μ h hh κ hκ ha hell hb hβ hK hholder
    (fun b=>inverseIntegral 𝓕 μ rate rp h (I b))
    (TwoChannelRawDriver.channels 𝓕 μ h (inverseIntegral 𝓕 μ rate rp h J)) (fun b=>max (B b) (B' b))
    (fun b=>inverse_bdgPower 𝓕 μ rate rp h 8 (I b) (max (B b) (B' b)) (hbm b)) hpos
    (InverseClockLocality.null_complete 𝓕 μ rate rp hnull)
    (inverse_channel_naturality 𝓕 μ rate rp h I J hIJ)
    (inverse_channel_locality 𝓕 μ rate rp h J hlocal) hLip u₀ A 𝓖 ν
    (fun b=>inverseIntegral 𝓖 ν rate rp h (I' b))
    (TwoChannelRawDriver.channels 𝓖 ν h (inverseIntegral 𝓖 ν rate rp h J'))
    (fun b=>inverse_bdgPower 𝓖 ν rate rp h 8 (I' b) (max (B b) (B' b)) (hbm' b))
    (InverseClockLocality.null_complete 𝓖 ν rate rp hnull')
    (inverse_channel_naturality 𝓖 ν rate rp h I' J' hIJ')
    (inverse_channel_locality 𝓖 ν rate rp h J' hlocal') A' stateMap hdr
end SHE.InverseNativeSmoothCommonLaw
