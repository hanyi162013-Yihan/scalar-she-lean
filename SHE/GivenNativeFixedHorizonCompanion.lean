module

public import SHE.GivenFixedHorizonCompanion
public import SHE.GivenFirstResidualPair
public import SHE.MixedNativePairConstruction
public import SHE.MixedNativePairMild
public import SHE.NativePairKernels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.GivenNativeFixedHorizonCompanion
open MeasureTheory PredictableTimeDilation PredictableL2 LowBands FiniteHaar ContinuousHeatMild
open scoped NNReal ENNReal
local instance givenFirstNativePair_finite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance givenFirstNativePair_stateSigma : MeasurableSpace StateL2 := borel _
local instance givenFirstNativePair_stateBorel : BorelSpace StateL2 := ⟨rfl⟩
local instance givenFirstNativePair_nativeSigma : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance givenFirstNativePair_nativeBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance givenFirstNativePair_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance givenFirstNativePair_columnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ)≤1) {Λ : ℝ} (hΛ : 0≤Λ)
variable (κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ h)

include hΛ

/-- Native-clock realization of the smooth companion of a GIVEN rough
first mild solution. Only aV has a Lipschitz hypothesis; the horizon is prescribed independently. The
first physical path is preserved exactly by the proved clock map. -/
theorem exists_native_companion {HU HV β : ℝ} (hβ : 0<β) (hHU : 0≤HU) (hHV : 0≤HV)
    (hholderU : ∀ z w,|aU z-aU w|≤HU*|z-w|^β)
    (hholderV : ∀ z w,|aV z-aV w|≤HV*|z-w|^β) {LV : ℝ≥0}
    (hLipV : LipschitzWith LV (fun z=>(aV z:ℂ)))
    (hpos : 0<h) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B₀ B₁ : ℝ≥0) (hBDG₀ : StandardTerminalBDG16 I₀ B₀) (hBDG₁ : StandardTerminalBDG16 I₁ B₁)
    (u₀ v₀ : StateL2)
    (S : GivenFirstResidualPair.FirstSolution 𝓕 μ h hh ((NativeClock.rate:ℝ)*κ)
      (mul_pos NativeClock.rate_pos hκ) (haU.const_mul (NativeClock.rate:ℝ))
      (mul_pos NativeClock.rate_pos hell) (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hbU)
      I₀ I₁ u₀) :
    ∃ T : MixedNativeAdditiveResidualPair.Solution
      (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h)
      Λ κ hκ haU haV hell hbU hbV
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₀)
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₁) u₀ v₀,
      T.first=NativePairClock.path S.value := by
  obtain ⟨T,hfirst,_⟩:=GivenFixedHorizonCompanion.exists_companion 𝓕 μ h hh
    (mul_nonneg NativeClock.rate.2 hΛ) ((NativeClock.rate:ℝ)*κ) (mul_pos NativeClock.rate_pos hκ)
    (haU.const_mul (NativeClock.rate:ℝ)) (haV.const_mul (NativeClock.rate:ℝ))
    (mul_pos NativeClock.rate_pos hell) (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hbU)
    (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hbV)
    hβ (mul_nonneg NativeClock.rate.2 hHV) (NativeAdditiveResidualPair.scaled_holder hholderV)
    (NativeAdditiveResidualPair.scaled_lipschitz hLipV) I₀ I₁
    hpos hnull B₀ B₁ hBDG₀ hBDG₁ u₀ v₀ S
  refine ⟨MixedNativeAdditiveResidualPair.of_unit 𝓕 μ h hh hΛ κ hκ haU haV hell hbU hbV
    (NonlinearHaarIntegrand.coefficientField_measurable haU hell hbU hβ hHU hholderU)
    (NonlinearHaarIntegrand.coefficientField_measurable haV hell hbV hβ hHV hholderV)
    I₀ I₁ u₀ v₀ T,?_⟩
  change NativePairClock.path T.first=NativePairClock.path S.value
  rw [hfirst]

end SHE.GivenNativeFixedHorizonCompanion
