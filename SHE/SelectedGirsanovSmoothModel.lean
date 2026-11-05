module
public import SHE.StandardRecognizedHilbertBDG
public import SHE.NativeInverseClock
public import SHE.GirsanovRawCoordinates
public import SHE.GirsanovPastLocality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.SelectedGirsanovSmoothModel
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
variable{Ω:Type}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(Q:Measure Ω)[IsProbabilityMeasure Q]
variable(H:ℝ≥0)(hH:(H:ℝ)≤1)
variable(κ:ℝ)(hκ:0<κ){a:ℝ→ℝ}(ha:Measurable a)
variable{ell M L β:ℝ}(hell:0<ell)(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hL:0≤L)
variable(hholder:∀z w,|a z-a w|≤L*|z-w|^β)
variable(K:StandardTerminalIto (C:=Both FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 Q H)
variable(A0 A1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 Q H)
variable(u₀:StateL2)

/-- All facts and the actual full-horizon smooth solution use the supplied
SAME changed scalar integral and its supplied natural Hilbert channels. -/
structure Data where
  rawLaw:CylindricalDriverLaw.Law Q H
    (RawCylindricalCoordinates.value 𝓕 Q H NativeTwoChannelNoiseBasis.both K)
  locality:StandardTerminalPastLocality K
  nullComplete:NullCompleteFiltration.ContainsNullSets 𝓕 Q
  naturality0:NativeObservationNaturality.StandardScalarNaturality A0 (leftIntegral 𝓕 Q H K)
  naturality1:NativeObservationNaturality.StandardScalarNaturality A1 (rightIntegral 𝓕 Q H K)
  B:Bool→ℝ≥0
  bdg:∀b,StandardTerminalBDG16 (if b then A0 else A1) (B b)
  model:NativeSmoothFirstConstruction.Model (NativeInverseClock.base 𝓕) Q
    (NativeClock.time H) (NativeInverseClock.time_le_one H hH)
    κ hκ ha hell hb hβ hL hholder
    (fun b=>NativeInverseClock.unit 𝓕 Q H (if b then A0 else A1)) u₀

def Data.solution
    (D:Data 𝓕 Q H hH κ hκ ha hell hb hβ hL hholder K A0 A1 u₀):
    NativeMildFirst.Data 𝓕 Q H κ hκ ha hell hb A0 A1 u₀:=
  NativeInverseClock.solution 𝓕 Q H κ hκ ha hell hb hβ hL hholder
    (fun b=>if b then A0 else A1) u₀ hH D.model

/-- Given the actual before-exit witness, construct the smooth solution
without selecting a second changed driver. Package3 BDG is explicit and
restricted to this recognized ordinary Brownian integral. -/
theorem exists_data{Lip:ℝ≥0}(hLip:LipschitzWith Lip (fun z=>(a z:ℂ)))
    (μ:Measure Ω)[IsProbabilityMeasure μ]
    (J:StandardTerminalIto (C:=Both FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (T:GirsanovTransportWitness 𝓕 μ Q H J K)
    (hμQ:μ≪Q)(hQμ:Q≪μ)(hlocal:StandardTerminalPastLocality J)
    (B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B)(hpos:0<H)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hG:StandardTerminalGirsanov J)
    (hcap:∀ᵐω∂μ,StochasticExponential.bracket 𝓕 μ H T.control ω≤1)
    (hQ:Q=ExponentialChangeMeasure.measure μ (fun ω=>J.integral T.control ω)
      (StochasticExponential.bracket 𝓕 μ H T.control))
    (h0:NativeObservationNaturality.StandardScalarNaturality A0 (leftIntegral 𝓕 Q H K))
    (h1:NativeObservationNaturality.StandardScalarNaturality A1 (rightIntegral 𝓕 Q H K))
    (hOrdinaryBDG:StandardRecognizedHilbertBDG 𝓕 Q H K):
    Nonempty (Data 𝓕 Q H hH κ hκ ha hell hb hβ hL hholder K A0 A1 u₀):=by
  have hraw:=GirsanovRawCoordinates.law 𝓕 μ H NativeTwoChannelNoiseBasis.both
    NativeTwoChannelNoiseBasis.both_orthonormal J Q K T hμQ hQμ B hBDG hH hpos hG hcap hQ hnull
  have hloc:=GirsanovPastLocality.locality 𝓕 Q H μ J K T hμQ hQμ hlocal
  have hn:NullCompleteFiltration.ContainsNullSets 𝓕 Q:=by
    intro t A hA
    exact hnull t A (hμQ hA)
  obtain ⟨B0,B1,hB0,hB1⟩:=hOrdinaryBDG hraw hloc A0 A1 h0 h1
  let Bs:Bool→ℝ≥0:=fun b=>if b then B0 else B1
  have hBs(b:Bool):StandardTerminalBDG16 (if b then A0 else A1) (Bs b):=by
    cases b
    · exact hB1
    · exact hB0
  have huB(b:Bool):StandardTerminalBDG16
      (NativeInverseClock.unit 𝓕 Q H (if b then A0 else A1)) (Bs b):=by
    apply inverse_bdgPower (NativeInverseClock.base 𝓕) Q NativeClock.rate NativeClock.rate_pos
      (NativeClock.time H) 8
    exact NativeInverseClock.bdg_cast Q (NativeInverseClock.filtration_eq 𝓕).symm
      (NativeInverseClock.span_eq H).symm _ _
      (NativeInverseClock.native_heq 𝓕 Q H (if b then A0 else A1)).symm (Bs b) (hBs b)
  have hnu:NullCompleteFiltration.ContainsNullSets (NativeInverseClock.base 𝓕) Q:=by
    intro t A hA
    exact hn (clock NativeClock.rate NativeClock.rate_pos t) A hA
  obtain ⟨W⟩:=NativeSmoothFirstConstruction.exists_model (NativeInverseClock.base 𝓕) Q
    (NativeClock.time H) (NativeInverseClock.time_le_one H hH)
    κ hκ ha hell hb hβ hL hholder
    (fun b=>NativeInverseClock.unit 𝓕 Q H (if b then A0 else A1)) u₀ Bs huB
    (NativeInverseClock.time_pos H hpos) hnu hLip
  exact ⟨⟨hraw,hloc,hn,h0,h1,Bs,hBs,W⟩⟩
end SHE.SelectedGirsanovSmoothModel
