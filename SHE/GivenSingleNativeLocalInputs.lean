module
public import SHE.GivenSingleNativeLocalUniqueness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.GivenSingleNativeLocalInputs
open MeasureTheory PredictableL2 NativeObservationNaturality FiniteHaar OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance localInputs_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance localInputs_realSigma:MeasurableSpace RealL2:=borel _
local instance localInputs_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance localInputs_haarSigma:MeasurableSpace RealHaarInput:=borel _
local instance localInputs_haarBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance localInputs_bothSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance localInputs_bothBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {ι:Type} [Fintype ι] (Ω:ι→Type) [∀i,MeasurableSpace (Ω i)]
variable (𝓕:∀i,Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω i)))
variable (μ:∀i,Measure (Ω i)) [∀i,IsProbabilityMeasure (μ i)] (h:ℝ≥0)

abbrev productFiltration (i:ι) := PredictableTimeDilation.filtration
  (SingleNativeProductFamily.filtration Ω 𝓕 μ i)
  (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)
abbrev productMeasure (i:ι) := SingleNativeProductFamily.measure Ω μ i

variable (D:SmoothApproximation.ScalarData)
variable (J:∀i,StandardTerminalIto (C:=RealL2) (E:=ℝ)
  (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
  (μ i) (NativeClock.rate*h)) (u₀:RealL2)
variable (U:∀i,SingleNativeHeatEquation.Data
  (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
  (μ i) (NativeClock.rate*h) D (J i) u₀)

/-- A record of exactly the ordinary stochastic inputs of the already
proved local theorem. It adds no estimate, equation, conditional model,
state law, comparison or uniqueness assumption. The product and rotated
maps in every field are the actual maps selected from the GIVEN model. -/
structure Inputs where
  products:SingleNativeProductFamily.Products Ω 𝓕 μ h J
  I₀:∀i,StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2)
    (productFiltration Ω 𝓕 μ i) (productMeasure Ω μ i) (NativeClock.rate*h)
  I₁:∀i,StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2)
    (productFiltration Ω 𝓕 μ i) (productMeasure Ω μ i) (NativeClock.rate*h)
  natural₀:∀i,StandardScalarNaturality (I₀ i)
    (leftIntegral (productFiltration Ω 𝓕 μ i) (productMeasure Ω μ i) (NativeClock.rate*h)
      (SingleNativeProductFamily.driver Ω 𝓕 μ h J D u₀ U products i))
  natural₁:∀i,StandardScalarNaturality (I₁ i)
    (rightIntegral (productFiltration Ω 𝓕 μ i) (productMeasure Ω μ i) (NativeClock.rate*h)
      (SingleNativeProductFamily.driver Ω 𝓕 μ h J D u₀ U products i))
  B₀:ι→ℝ≥0
  B₁:ι→ℝ≥0
  Bnext:ι→ℝ≥0
  B:ι→ℕ→ℝ≥0
  bdg₀:∀i,StandardTerminalBDG16 (I₀ i) (B₀ i)
  bdg₁:∀i,StandardTerminalBDG16 (I₁ i) (B₁ i)
  bdgNext:∀i,StandardTerminalBDGPower 1 (I₁ i) (Bnext i)
  girsanov:∀i,StandardTerminalGirsanov (SingleNativeProductFamily.driver Ω 𝓕 μ h J D u₀ U products i)
  recognizedBDG:∀i,StandardChangedHilbertBDG (productFiltration Ω 𝓕 μ i)
    (productMeasure Ω μ i) (NativeClock.rate*h)
    (SingleNativeProductFamily.driver Ω 𝓕 μ h J D u₀ U products i)
  finiteIto:∀i,StandardFiniteIto.Universal (productFiltration Ω 𝓕 μ i) (productMeasure Ω μ i)
    (NativeClock.rate*h) (SingleNativeProductFamily.physical Ω 𝓕 μ h J products i)
  locality:∀i,StandardTerminalPastLocality (SingleNativeProductFamily.physical Ω 𝓕 μ h J products i)
  fubini:∀i,StandardItoStoppedParameterFubini (SingleNativeProductFamily.physical Ω 𝓕 μ h J products i)
  novikov:∀i,StandardTerminalNovikov (SingleNativeProductFamily.physical Ω 𝓕 μ h J products i)
  bdg:∀i p,0<p→StandardTerminalBDGPower p (SingleNativeProductFamily.physical Ω 𝓕 μ h J products i) (B i p)

theorem laws_eq (hh:(h:ℝ)≤1) (hpos:0<h) (hNative:NativeClock.rate*h≤1)
    (A:Inputs Ω 𝓕 μ h D J u₀ U) :
    ∀i j:ι,NativePathLawComparison.law (NativeClock.rate*h) (μ i) (U i).value (U i).continuous=
      NativePathLawComparison.law (NativeClock.rate*h) (μ j) (U j).value (U j).continuous :=
  GivenSingleNativeLocalUniqueness.laws_eq Ω 𝓕 μ h hh hpos hNative D J u₀ U
    A.products A.I₀ A.I₁ A.natural₀ A.natural₁ A.B₀ A.B₁ A.Bnext A.B
    A.bdg₀ A.bdg₁ A.bdgNext A.girsanov A.recognizedBDG
    A.finiteIto A.locality A.fubini A.novikov A.bdg
end SHE.GivenSingleNativeLocalInputs
