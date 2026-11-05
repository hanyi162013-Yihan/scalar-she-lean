module
public import SHE.NativeTwoChannelNoiseBasis
public import SHE.RawCylindricalCoordinates
public import SHE.NativeObservationNaturality
public import SHE.OrthogonalItoChannels
public import SHE.StandardTerminalPastLocality
public import SHE.StandardTerminalBDG
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE
open MeasureTheory PredictableL2 FiniteHaar OrthogonalItoChannels
open scoped NNReal ENNReal
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
/-- The ordinary Hilbert BDG theorem from standard stochastic package3,
restricted to a recognized Brownian integral and its SAME natural Haar
channels. This explicitly supplied input concerns ordinary integration;
it contains no heat equation, coefficient, solution or common-law claim.
It is not asserted for arbitrary abstract terminal isometries. -/
def StandardRecognizedHilbertBDG {Ω:Type*}[MeasurableSpace Ω]
    (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(Q:Measure Ω)[IsProbabilityMeasure Q](H:ℝ≥0)
    (K:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 Q H):Prop:=
  CylindricalDriverLaw.Law Q H
      (RawCylindricalCoordinates.value 𝓕 Q H NativeTwoChannelNoiseBasis.both K) →
    StandardTerminalPastLocality K →
    ∀(A0 A1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=LowBands.StateL2) 𝓕 Q H),
      NativeObservationNaturality.StandardScalarNaturality A0 (leftIntegral 𝓕 Q H K) →
      NativeObservationNaturality.StandardScalarNaturality A1 (rightIntegral 𝓕 Q H K) →
      ∃B0 B1:ℝ≥0,StandardTerminalBDG16 A0 B0 ∧ StandardTerminalBDG16 A1 B1
end SHE
