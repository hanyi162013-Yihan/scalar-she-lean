module

public import SHE.NativePairClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativePairClock
open MeasureTheory PredictableTimeDilation PredictableL2 LowBands FiniteHaar ContinuousHeatMild
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ)≤1)

theorem additiveInput_ae (κ : ℝ) (hκ : 0<κ) (D : ℝ) (hD : 0≤D)
    (t : ℝ≥0) (ht : t≤NativeClock.rate*h) :
    additiveInput 𝓕 μ h hh κ hκ D hD t=ᵐ[energyMeasure μ (NativeClock.rate*h)]
      fun p => Real.exp (-D*((t:ℝ)-(p.1:ℝ))) • NativeHeatObservation.kernel κ κ hκ
        ((t:ℝ)-(p.1:ℝ),AdditiveHaarForcing.constantField κ hκ) := by
  exact ClockedHaarIntegral.input_ae 𝓕 μ NativeClock.rate NativeClock.rate_pos h hh hD hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const t ht

theorem residualInput_ae {Λ : ℝ} (hΛ : 0≤Λ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
    (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
    (hm : Measurable (NonlinearHaarIntegrand.coefficientField a ha ell M hell hb))
    (U : ℝ≥0→Ω→StateL2) (hU : StronglyMeasurable[𝓕.predictable] (Function.uncurry U))
    (t : ℝ≥0) (ht : t≤NativeClock.rate*h) :
    residualInput 𝓕 μ h hh hΛ ha hell hb hm U hU t=ᵐ[energyMeasure μ (NativeClock.rate*h)]
      fun p => Real.exp (-Λ*((t:ℝ)-(p.1:ℝ))) • NativeHeatObservation.kernel ell M hell
        ((t:ℝ)-(p.1:ℝ),coefficientFunction ha hell hb (path U) p) := by
  exact ClockedHaarIntegral.input_ae 𝓕 μ NativeClock.rate NativeClock.rate_pos h hh hΛ
    hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (coefficientFunction ha hell hb (path U)) (coefficient_predictable 𝓕 ha hell hb hm U hU) t ht

theorem additiveInput_zero_ae (κ : ℝ) (hκ : 0<κ) (t : ℝ≥0) (ht : t≤NativeClock.rate*h) :
    additiveInput 𝓕 μ h hh κ hκ 0 (by norm_num) t=ᵐ[energyMeasure μ (NativeClock.rate*h)]
      fun p => NativeHeatObservation.kernel κ κ hκ
        ((t:ℝ)-(p.1:ℝ),AdditiveHaarForcing.constantField κ hκ) := by
  simpa only [neg_zero,zero_mul,Real.exp_zero,one_smul] using additiveInput_ae 𝓕 μ h hh κ hκ 0 (by norm_num) t ht

theorem residualInput_zero_ae {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
    (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
    (hm : Measurable (NonlinearHaarIntegrand.coefficientField a ha ell M hell hb))
    (U : ℝ≥0→Ω→StateL2) (hU : StronglyMeasurable[𝓕.predictable] (Function.uncurry U))
    (t : ℝ≥0) (ht : t≤NativeClock.rate*h) :
    residualInput 𝓕 μ h hh (Λ := 0) (by norm_num) ha hell hb hm U hU t=ᵐ[energyMeasure μ (NativeClock.rate*h)]
      fun p => NativeHeatObservation.kernel ell M hell
        ((t:ℝ)-(p.1:ℝ),coefficientFunction ha hell hb (path U) p) := by
  simpa only [neg_zero,zero_mul,Real.exp_zero,one_smul] using residualInput_ae 𝓕 μ h hh
    (Λ := 0) (by norm_num) ha hell hb hm U hU t ht

end SHE.NativePairClock
