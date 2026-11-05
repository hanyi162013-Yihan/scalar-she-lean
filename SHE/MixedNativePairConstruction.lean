module

public import SHE.NativePairConstruction
public import SHE.MixedNativePairMild
public import SHE.NativePairKernels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.MixedNativeAdditiveResidualPair
open MeasureTheory PredictableTimeDilation PredictableL2 LowBands FiniteHaar ContinuousHeatMild
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A native-clock continuous pair with literal additive and residual
Haar kernels. The two mild equations are conclusions of the construction. -/
structure Solution (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)
    (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ → ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
    (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
    (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (u₀ v₀ : StateL2) where
  first : ℝ≥0 → Ω → StateL2
  second : ℝ≥0 → Ω → StateL2
  first_continuous : ∀ ω,Continuous (fun t => first t ω)
  second_continuous : ∀ ω,Continuous (fun t => second t ω)
  first_predictable : StronglyMeasurable[𝓕.predictable] (Function.uncurry first)
  second_predictable : StronglyMeasurable[𝓕.predictable] (Function.uncurry second)
  first_coefficient : StronglyMeasurable[𝓕.predictable] (coefficientFunction haU hell hbU first)
  second_coefficient : StronglyMeasurable[𝓕.predictable] (coefficientFunction haV hell hbV second)
  additiveInput : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h
  residualInput : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h
  controlledAdditiveInput : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h
  controlledResidualInput : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h
  additive_kernel : ∀ t,t≤h → additiveInput t=ᵐ[energyMeasure μ h]
    fun p => NativeHeatObservation.kernel κ κ hκ ((t:ℝ)-(p.1:ℝ),AdditiveHaarForcing.constantField κ hκ)
  residual_kernel : ∀ t,t≤h → residualInput t=ᵐ[energyMeasure μ h]
    fun p => NativeHeatObservation.kernel ell M hell ((t:ℝ)-(p.1:ℝ),coefficientFunction haU hell hbU first p)
  controlled_additive_kernel : ∀ t,t≤h → controlledAdditiveInput t=ᵐ[energyMeasure μ h]
    fun p => Real.exp (-Λ*((t:ℝ)-(p.1:ℝ))) •
      NativeHeatObservation.kernel κ κ hκ ((t:ℝ)-(p.1:ℝ),AdditiveHaarForcing.constantField κ hκ)
  controlled_residual_kernel : ∀ t,t≤h → controlledResidualInput t=ᵐ[energyMeasure μ h]
    fun p => Real.exp (-Λ*((t:ℝ)-(p.1:ℝ))) •
      NativeHeatObservation.kernel ell M hell ((t:ℝ)-(p.1:ℝ),coefficientFunction haV hell hbV second p)
  first_mild : ∀ t,t≤h → first t=ᵐ[μ]
    fun ω => NativeHeatObservation.heat (t:ℝ) u₀+I₀.integral (additiveInput t) ω+I₁.integral (residualInput t) ω
  second_mild : ∀ t,t≤h → second t=ᵐ[μ]
    fun ω => Real.exp (-Λ*(t:ℝ)) • NativeHeatObservation.heat (t:ℝ) v₀+
      Λ • NativeClock.volterra Λ (fun s => first s ω) t+
      I₀.integral (controlledAdditiveInput t) ω+I₁.integral (controlledResidualInput t) ω

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ)≤1) {Λ : ℝ} (hΛ : 0≤Λ)
variable (κ : ℝ) (hκ : 0<κ) {aU aV : ℝ → ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (hmU : Measurable (NonlinearHaarIntegrand.coefficientField aU haU ell M hell hbU))
variable (hmV : Measurable (NonlinearHaarIntegrand.coefficientField aV haV ell M hell hbV))
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
variable (u₀ v₀ : StateL2)

def of_unit (S : MixedAdditiveResidualPair.Solution 𝓕 μ h hh (mul_nonneg NativeClock.rate.2 hΛ)
    ((NativeClock.rate:ℝ)*κ) (mul_pos NativeClock.rate_pos hκ)
    (haU.const_mul (NativeClock.rate:ℝ)) (haV.const_mul (NativeClock.rate:ℝ)) (mul_pos NativeClock.rate_pos hell)
    (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hbU) (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hbV) I₀ I₁ u₀ v₀) :
    Solution (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h)
      Λ κ hκ haU haV hell hbU hbV
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₀)
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₁) u₀ v₀ where
  first := NativePairClock.path S.first
  second := NativePairClock.path S.second
  first_continuous := NativePairClock.path_continuous S.first S.first_continuous
  second_continuous := NativePairClock.path_continuous S.second S.second_continuous
  first_predictable := NativePairClock.path_predictable 𝓕 S.first S.first_predictable
  second_predictable := NativePairClock.path_predictable 𝓕 S.second S.second_predictable
  first_coefficient := NativePairClock.coefficient_predictable 𝓕 haU hell hbU hmU S.first S.first_predictable
  second_coefficient := NativePairClock.coefficient_predictable 𝓕 haV hell hbV hmV S.second S.second_predictable
  additiveInput := NativePairClock.additiveInput 𝓕 μ h hh κ hκ 0 (by norm_num)
  residualInput := NativePairClock.residualInput 𝓕 μ h hh (Λ := 0) (by norm_num) haU hell hbU hmU S.first S.first_predictable
  controlledAdditiveInput := NativePairClock.additiveInput 𝓕 μ h hh κ hκ Λ hΛ
  controlledResidualInput := NativePairClock.residualInput 𝓕 μ h hh hΛ haV hell hbV hmV S.second S.second_predictable
  additive_kernel := NativePairClock.additiveInput_zero_ae 𝓕 μ h hh κ hκ
  residual_kernel := NativePairClock.residualInput_zero_ae 𝓕 μ h hh haU hell hbU hmU S.first S.first_predictable
  controlled_additive_kernel := NativePairClock.additiveInput_ae 𝓕 μ h hh κ hκ Λ hΛ
  controlled_residual_kernel := NativePairClock.residualInput_ae 𝓕 μ h hh hΛ haV hell hbV hmV S.second S.second_predictable
  first_mild := MixedNativePairMild.first_mild 𝓕 μ h hh hΛ κ hκ haU haV hell hbU hbV hmU I₀ I₁ u₀ v₀ S
  second_mild := MixedNativePairMild.second_mild 𝓕 μ h hh hΛ κ hκ haU haV hell hbU hbV hmV I₀ I₁ u₀ v₀ S

include hh hΛ in
/-- Actual native-clock aU(U)/aV(V) coupling on the same additive and
residual noises, constructed from the two ordinary unit-clock Itô
integrals. No mild equation or model applicability is supplied. -/
theorem exists_pair {HU HV β : ℝ} (hβ : 0<β) (hHU : 0≤HU) (hHV : 0≤HV)
    (hholderU : ∀ z w,|aU z-aU w|≤HU*|z-w|^β)
    (hholderV : ∀ z w,|aV z-aV w|≤HV*|z-w|^β) {LU LV : ℝ≥0}
    (hLipU : LipschitzWith LU (fun z => (aU z:ℂ)))
    (hLipV : LipschitzWith LV (fun z => (aV z:ℂ)))
    (hsmallU : 2*CompanionHeat.picardConstant ((NativeClock.rate:ℝ)*ell)
      ((NativeClock.rate:ℝ)*M) (NativeClock.rate*LU)*(h:ℝ)^(1/2:ℝ)≤1/4)
    (hsmallV : 2*CompanionHeat.picardConstant ((NativeClock.rate:ℝ)*ell)
      ((NativeClock.rate:ℝ)*M) (NativeClock.rate*LV)*(h:ℝ)^(1/2:ℝ)≤1/4)
    (hpos : 0<h) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B₀ B₁ : ℝ≥0) (hBDG₀ : StandardTerminalBDG16 I₀ B₀) (hBDG₁ : StandardTerminalBDG16 I₁ B₁) :
    Nonempty (Solution (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h)
      Λ κ hκ haU haV hell hbU hbV
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₀)
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₁) u₀ v₀) := by
  obtain ⟨S⟩ := MixedAdditiveResidualPair.exists_pair 𝓕 μ h hh (mul_nonneg NativeClock.rate.2 hΛ)
    ((NativeClock.rate:ℝ)*κ) (mul_pos NativeClock.rate_pos hκ)
    (haU.const_mul (NativeClock.rate:ℝ)) (haV.const_mul (NativeClock.rate:ℝ))
    (mul_pos NativeClock.rate_pos hell)
    (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hbU)
    (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hbV)
    hβ (mul_nonneg NativeClock.rate.2 hHU) (mul_nonneg NativeClock.rate.2 hHV)
    (NativeAdditiveResidualPair.scaled_holder hholderU)
    (NativeAdditiveResidualPair.scaled_holder hholderV)
    (NativeAdditiveResidualPair.scaled_lipschitz hLipU)
    (NativeAdditiveResidualPair.scaled_lipschitz hLipV)
    hsmallU hsmallV I₀ I₁ hpos hnull B₀ B₁ hBDG₀ hBDG₁ u₀ v₀
  exact ⟨of_unit 𝓕 μ h hh hΛ κ hκ haU haV hell hbU hbV
    (NonlinearHaarIntegrand.coefficientField_measurable haU hell hbU hβ hHU hholderU)
    (NonlinearHaarIntegrand.coefficientField_measurable haV hell hbV hβ hHV hholderV)
    I₀ I₁ u₀ v₀ S⟩

end SHE.MixedNativeAdditiveResidualPair
