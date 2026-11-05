module

public import SHE.GivenNativeFixedHorizonCompanion
public import SHE.GivenNativeMildCompanion
public import SHE.GivenFirstNativePair
public import SHE.NativeFirstRealization
public import SHE.TimeDilationRoundTrip
public import SHE.MixedNativePairConstruction
public import SHE.MixedNativePairMild
public import SHE.NativePairKernels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.GivenNativeFirstFixedHorizon
open MeasureTheory PredictableTimeDilation PredictableL2 LowBands FiniteHaar ContinuousHeatMild
open scoped NNReal ENNReal
local instance givenNativeFirstCompanion_finite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance givenNativeFirstCompanion_stateSigma : MeasurableSpace StateL2 := borel _
local instance givenNativeFirstCompanion_stateBorel : BorelSpace StateL2 := ⟨rfl⟩
local instance givenNativeFirstCompanion_nativeSigma : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance givenNativeFirstCompanion_nativeBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance givenNativeFirstCompanion_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance givenNativeFirstCompanion_columnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ)≤1) {Λ : ℝ} (hΛ : 0≤Λ)
variable (κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (J₀ J₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2)
  (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h))

include hh hΛ in
/-- A supplied native rough first solution acquires its smooth companion
on the EXACT original two native Itô integrals. The unit-clock first
solution and its BDG estimates are derived, rather than supplied. Only
the companion coefficient has a Lipschitz/Picard hypothesis. -/
theorem exists_companion {HU HV β : ℝ} (hβ : 0<β) (hHU : 0≤HU) (hHV : 0≤HV)
    (hholderU : ∀ z w,|aU z-aU w|≤HU*|z-w|^β)
    (hholderV : ∀ z w,|aV z-aV w|≤HV*|z-w|^β) {LV : ℝ≥0}
    (hLipV : LipschitzWith LV (fun z=>(aV z:ℂ)))
    (hpos : 0<h)
    (hnull : NullCompleteFiltration.ContainsNullSets
      (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ)
    (B₀ B₁ : ℝ≥0) (hBDG₀ : StandardTerminalBDG16 J₀ B₀) (hBDG₁ : StandardTerminalBDG16 J₁ B₁)
    (u₀ v₀ : StateL2)
    (S : NativeFirstClockPull.FirstSolution 𝓕 μ h κ hκ haU hell hbU J₀ J₁ u₀) :
    ∃ T : MixedNativeAdditiveResidualPair.Solution
      (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h)
      Λ κ hκ haU haV hell hbU hbV J₀ J₁ u₀ v₀,
      T.first=S.value := by
  let I₀:=inverseIntegral 𝓕 μ NativeClock.rate NativeClock.rate_pos h J₀
  let I₁:=inverseIntegral 𝓕 μ NativeClock.rate NativeClock.rate_pos h J₁
  have hnunit : NullCompleteFiltration.ContainsNullSets 𝓕 μ := by
    intro t A hA
    have he:=hnull (clock NativeClock.rate NativeClock.rate_pos t) A hA
    rwa [filtration_clock] at he
  have hB₀ : StandardTerminalBDG16 I₀ B₀:=
    inverse_bdgPower 𝓕 μ NativeClock.rate NativeClock.rate_pos h 8 J₀ B₀ hBDG₀
  have hB₁ : StandardTerminalBDG16 I₁ B₁:=
    inverse_bdgPower 𝓕 μ NativeClock.rate NativeClock.rate_pos h 8 J₁ B₁ hBDG₁
  obtain ⟨T,hT⟩:=GivenNativeFixedHorizonCompanion.exists_native_companion 𝓕 μ h hh hΛ κ hκ haU haV hell hbU hbV
    I₀ I₁ hβ hHU hHV hholderU hholderV hLipV hpos hnunit B₀ B₁ hB₀ hB₁ u₀ v₀
    (NativeFirstRealization.to_unit 𝓕 μ h hh κ hκ haU hell hbU J₀ J₁ u₀ S)
  have hfirst : T.first=S.value:=hT.trans (NativeFirstRealization.first_round_trip
    𝓕 μ h hh κ hκ haU hell hbU J₀ J₁ u₀ S)
  let T' : MixedNativeAdditiveResidualPair.Solution
      (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h)
      Λ κ hκ haU haV hell hbU hbV J₀ J₁ u₀ v₀ :=
    { first:=T.first
      second:=T.second
      first_continuous:=T.first_continuous
      second_continuous:=T.second_continuous
      first_predictable:=T.first_predictable
      second_predictable:=T.second_predictable
      first_coefficient:=T.first_coefficient
      second_coefficient:=T.second_coefficient
      additiveInput:=T.additiveInput
      residualInput:=T.residualInput
      controlledAdditiveInput:=T.controlledAdditiveInput
      controlledResidualInput:=T.controlledResidualInput
      additive_kernel:=T.additive_kernel
      residual_kernel:=T.residual_kernel
      controlled_additive_kernel:=T.controlled_additive_kernel
      controlled_residual_kernel:=T.controlled_residual_kernel
      first_mild:=by
        intro t ht
        have he:=T.first_mild t ht
        simpa only [I₀,I₁,integral_inverseIntegral] using he
      second_mild:=by
        intro t ht
        have he:=T.second_mild t ht
        simpa only [I₀,I₁,integral_inverseIntegral] using he }
  exact ⟨T',hfirst⟩

end SHE.GivenNativeFirstFixedHorizon

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.GivenNativeMildFixedHorizon
open MeasureTheory PredictableTimeDilation PredictableL2 LowBands FiniteHaar ContinuousHeatMild
open scoped NNReal ENNReal
local instance givenNativeMildCompanion_finite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance givenNativeMildCompanion_stateSigma : MeasurableSpace StateL2 := borel _
local instance givenNativeMildCompanion_stateBorel : BorelSpace StateL2 := ⟨rfl⟩
local instance givenNativeMildCompanion_nativeSigma : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance givenNativeMildCompanion_nativeBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance givenNativeMildCompanion_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance givenNativeMildCompanion_columnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ)≤1) {Λ : ℝ} (hΛ : 0≤Λ)
variable (κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (J₀ J₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2)
  (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h))

include hh hΛ in
/-- A supplied native rough first solution acquires its smooth companion
on the EXACT original two native Itô integrals. The unit-clock first
solution and its BDG estimates are derived, rather than supplied. Only
the companion coefficient has a Lipschitz/Picard hypothesis. -/
theorem exists_companion {HU HV β : ℝ} (hβ : 0<β) (hHU : 0≤HU) (hHV : 0≤HV)
    (hholderU : ∀ z w,|aU z-aU w|≤HU*|z-w|^β)
    (hholderV : ∀ z w,|aV z-aV w|≤HV*|z-w|^β) {LV : ℝ≥0}
    (hLipV : LipschitzWith LV (fun z=>(aV z:ℂ)))
    (hpos : 0<h)
    (hnull : NullCompleteFiltration.ContainsNullSets
      (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ)
    (B₀ B₁ : ℝ≥0) (hBDG₀ : StandardTerminalBDG16 J₀ B₀) (hBDG₁ : StandardTerminalBDG16 J₁ B₁)
    (u₀ v₀ : StateL2)
    (S : NativeFirstMildData.Data 𝓕 μ h κ hκ haU hell hbU J₀ J₁ u₀) :
    ∃ T : MixedNativeAdditiveResidualPair.Solution
      (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h)
      Λ κ hκ haU haV hell hbU hbV J₀ J₁ u₀ v₀,
      T.first=S.value := by
  obtain ⟨N,hN⟩:=NativeMildFirstRealization.exists_first_solution
    𝓕 μ h hh κ hκ haU hell hbU J₀ J₁ u₀ S hpos B₀ B₁ hBDG₀ hBDG₁
  obtain ⟨T,hT⟩:=GivenNativeFirstFixedHorizon.exists_companion 𝓕 μ h hh hΛ κ hκ haU haV hell hbU hbV
    J₀ J₁ hβ hHU hHV hholderU hholderV hLipV hpos hnull B₀ B₁ hBDG₀ hBDG₁ u₀ v₀ N
  exact ⟨T,hT.trans hN⟩

end SHE.GivenNativeMildFixedHorizon
