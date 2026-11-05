module
public import SHE.SingleNativeProductFamily
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.GivenSingleNativeLocalUniqueness
open MeasureTheory PredictableL2 NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance family_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance family_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance family_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=1)).repr.toHomeomorph.secondCountableTopology
local instance family_realSecond:SecondCountableTopology RealL2:=realCircleIdentification.toHomeomorph.secondCountableTopology
local instance family_realSigma:MeasurableSpace RealL2:=borel _
local instance family_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance family_bothSigma:MeasurableSpace (Both RealL2):=borel _
local instance family_bothBorel:BorelSpace (Both RealL2):=⟨rfl⟩
local instance family_haarSigma:MeasurableSpace RealHaarInput:=borel _
local instance family_haarBorel:BorelSpace RealHaarInput:=⟨rfl⟩
variable {ι:Type}[Fintype ι](Ω:ι→Type)[∀i,MeasurableSpace (Ω i)]
variable (𝓕:∀i,Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω i)))
  (μ:∀i,Measure (Ω i))[∀i,IsProbabilityMeasure (μ i)]
variable (h:ℝ≥0)(hh:(h:ℝ)≤1)(hpos:0<h)(hNative:(NativeClock.rate*h:ℝ≥0)≤1)
  (D:SmoothApproximation.ScalarData)
variable (J:∀i,StandardTerminalIto (C:=RealL2) (E:=ℝ) (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h))
variable (u₀:RealL2)
variable (U:∀i,SingleNativeHeatEquation.Data (PredictableTimeDilation.filtration (𝓕 i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h) D (J i) u₀)
variable (P:SingleNativeProductFamily.Products Ω 𝓕 μ h J)
variable (I₀ I₁:∀i,StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2)
  (PredictableTimeDilation.filtration (SingleNativeProductFamily.filtration Ω 𝓕 μ i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (SingleNativeProductFamily.measure Ω μ i) (NativeClock.rate*h))
variable (hIJ₀:∀i,StandardScalarNaturality (I₀ i) (leftIntegral (PredictableTimeDilation.filtration (SingleNativeProductFamily.filtration Ω 𝓕 μ i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (SingleNativeProductFamily.measure Ω μ i) (NativeClock.rate*h) (SingleNativeProductFamily.driver Ω 𝓕 μ h J D u₀ U P i)))
  (hIJ₁:∀i,StandardScalarNaturality (I₁ i) (rightIntegral (PredictableTimeDilation.filtration (SingleNativeProductFamily.filtration Ω 𝓕 μ i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (SingleNativeProductFamily.measure Ω μ i) (NativeClock.rate*h) (SingleNativeProductFamily.driver Ω 𝓕 μ h J D u₀ U P i)))
variable (BI0 BI1 Bnext:ι→ℝ≥0)(B:ι→ℕ→ℝ≥0)
  (hBI0:∀i,StandardTerminalBDG16 (I₀ i) (BI0 i))(hBI1:∀i,StandardTerminalBDG16 (I₁ i) (BI1 i))
  (hBDGnext:∀i,StandardTerminalBDGPower 1 (I₁ i) (Bnext i))
variable (hGirsanov:∀i,StandardTerminalGirsanov (SingleNativeProductFamily.driver Ω 𝓕 μ h J D u₀ U P i))
  (hRecognizedBDG:∀i,StandardChangedHilbertBDG
    (PredictableTimeDilation.filtration (SingleNativeProductFamily.filtration Ω 𝓕 μ i)
      (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
    (SingleNativeProductFamily.measure Ω μ i) (NativeClock.rate*h)
    (SingleNativeProductFamily.driver Ω 𝓕 μ h J D u₀ U P i))
variable (hPhysicalFiniteIto:∀i,StandardFiniteIto.Universal (PredictableTimeDilation.filtration (SingleNativeProductFamily.filtration Ω 𝓕 μ i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)) (SingleNativeProductFamily.measure Ω μ i) (NativeClock.rate*h) (SingleNativeProductFamily.physical Ω 𝓕 μ h J P i))
  (hPhysicalLocality:∀i,StandardTerminalPastLocality (SingleNativeProductFamily.physical Ω 𝓕 μ h J P i))
  (hPhysicalFubini:∀i,StandardItoStoppedParameterFubini (SingleNativeProductFamily.physical Ω 𝓕 μ h J P i))
  (hPhysicalNovikov:∀i,StandardTerminalNovikov (SingleNativeProductFamily.physical Ω 𝓕 μ h J P i))
  (hPhysicalBDG:∀i p,0<p→StandardTerminalBDGPower p (SingleNativeProductFamily.physical Ω 𝓕 μ h J P i) (B i p))

include hh hpos hNative hIJ₀ hIJ₁ hBI0 hBI1 hBDGnext hGirsanov hRecognizedBDG
  hPhysicalFiniteIto hPhysicalLocality hPhysicalFubini hPhysicalNovikov hPhysicalBDG in
/-- Fixed-interval uniqueness for the GIVEN bare, single-physical-noise
observable equations on arbitrary spaces. Independent-noise enlargement,
zero-auxiliary row transport, the split mild equations, and preservation
of the actual continuous-path laws are proved internally. `P` is precisely
the ordinary product-Ito constructor component of package 1; the other
hypotheses are ordinary packages on its actual product/rotated maps. -/
theorem laws_eq:
    ∀i j:ι,NativePathLawComparison.law (NativeClock.rate*h) (μ i) (U i).value (U i).continuous=
      NativePathLawComparison.law (NativeClock.rate*h) (μ j) (U j).value (U j).continuous:=by
  have he:=GivenOriginalNativeLocalUniqueness.laws_eq_of_physical
    (Ω:=fun i=>IndependentNoiseCompletion.Space (μ i) (μ i))
    (𝓕:=SingleNativeProductFamily.filtration Ω 𝓕 μ)
    (μ:=SingleNativeProductFamily.measure Ω μ)
    (h:=h) (hh:=hh) (hpos:=hpos) (hNative:=hNative) (D:=D)
    (Bphysical:=SingleNativeProductFamily.physical Ω 𝓕 μ h J P)
    (u₀:=u₀) (U:=SingleNativeProductFamily.augmented Ω 𝓕 μ h J D u₀ U P)
    (I₀:=I₀) (I₁:=I₁) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
    (hnull:=SingleNativeProductFamily.contains_null Ω 𝓕 μ)
    (BI0:=BI0) (BI1:=BI1) (Bnext:=Bnext) (B:=B)
    (hBI0:=hBI0) (hBI1:=hBI1) (hBDGnext:=hBDGnext)
    (hGirsanov:=hGirsanov) (hRecognizedBDG:=hRecognizedBDG)
    hPhysicalFiniteIto hPhysicalLocality hPhysicalFubini hPhysicalNovikov hPhysicalBDG
  intro i j
  exact (SingleNativeProductFamily.same_law Ω 𝓕 μ h J D u₀ U P i).symm.trans
    ((he i j).trans (SingleNativeProductFamily.same_law Ω 𝓕 μ h J D u₀ U P j))
end SHE.GivenSingleNativeLocalUniqueness
