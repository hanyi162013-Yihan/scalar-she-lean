module

public import SHE.ClockedPairIntegral
public import SHE.NativeClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.NativePairClock
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
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ)≤1) {Λ : ℝ} (hΛ : 0≤Λ)
variable {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (hm : Measurable (NonlinearHaarIntegrand.coefficientField a ha ell M hell hb))

 def path (U : ℝ≥0→Ω→StateL2) : ℝ≥0→Ω→StateL2 :=
  ClockedPairFields.path NativeClock.rate NativeClock.rate_pos U

theorem path_continuous (U : ℝ≥0→Ω→StateL2) (hU : ∀ ω,Continuous (fun t => U t ω)) (ω : Ω) :
    Continuous (fun t => path U t ω) :=
  ClockedPairFields.path_continuous _ _ _ hU ω

theorem path_predictable (U : ℝ≥0→Ω→StateL2)
    (hU : StronglyMeasurable[𝓕.predictable] (Function.uncurry U)) :
    StronglyMeasurable[(filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)).predictable]
      (Function.uncurry (path U)) :=
  ClockedPairFields.path_predictable 𝓕 _ _ _ hU

include hm in
theorem coefficient_predictable (U : ℝ≥0→Ω→StateL2)
    (hU : StronglyMeasurable[𝓕.predictable] (Function.uncurry U)) :
    StronglyMeasurable[(filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)).predictable]
      (coefficientFunction ha hell hb (path U)) :=
  ClockedPairFields.coefficient_predictable 𝓕 _ _ ha hell hb hm U hU

 def additiveInput (κ : ℝ) (hκ : 0<κ) (D : ℝ) (hD : 0≤D) (t : ℝ≥0) :
    Process (E := RealHaarIntegrand.Columns)
      (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h) :=
  ClockedHaarIntegral.input 𝓕 μ NativeClock.rate NativeClock.rate_pos h hh hD hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const t

 def residualInput (U : ℝ≥0→Ω→StateL2)
    (hU : StronglyMeasurable[𝓕.predictable] (Function.uncurry U)) (t : ℝ≥0) :
    Process (E := RealHaarIntegrand.Columns)
      (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h) :=
  ClockedHaarIntegral.input 𝓕 μ NativeClock.rate NativeClock.rate_pos h hh hΛ
    hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (coefficientFunction ha hell hb (path U)) (coefficient_predictable 𝓕 ha hell hb hm U hU) t

 theorem additive_terminal_eq (κ : ℝ) (hκ : 0<κ) (D : ℝ) (hD : 0≤D)
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (t : ℝ≥0) (ht : t≤NativeClock.rate*h) :
    (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I).integral
      (additiveInput 𝓕 μ h hh κ hκ D hD t)=
    DampedFixedIntegral.value 𝓕 μ h hh (mul_nonneg NativeClock.rate.2 hD)
      (mul_pos NativeClock.rate_pos hκ) (mul_nonneg NativeClock.rate.2 hκ.le)
      (fun _ => AdditiveHaarForcing.constantField ((NativeClock.rate:ℝ)*κ) (mul_pos NativeClock.rate_pos hκ))
      stronglyMeasurable_const I (NativeClock.time t) (ClockedPairIntegral.time_le _ _ _ ht) :=
  ClockedPairIntegral.terminal_eq 𝓕 μ NativeClock.rate NativeClock.rate_pos h hh hD hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    (fun _ => AdditiveHaarForcing.constantField ((NativeClock.rate:ℝ)*κ) (mul_pos NativeClock.rate_pos hκ))
    stronglyMeasurable_const (ClockedPairFields.unitField_constant _ _ κ hκ) I t ht

 theorem residual_terminal_eq (U : ℝ≥0→Ω→StateL2)
    (hU : StronglyMeasurable[𝓕.predictable] (Function.uncurry U))
    (hg : StronglyMeasurable[𝓕.predictable]
      (coefficientFunction (ha.const_mul (NativeClock.rate:ℝ)) (mul_pos NativeClock.rate_pos hell)
        (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hb) U))
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (t : ℝ≥0) (ht : t≤NativeClock.rate*h) :
    (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I).integral
      (residualInput 𝓕 μ h hh hΛ ha hell hb hm U hU t)=
    DampedFixedIntegral.value 𝓕 μ h hh (mul_nonneg NativeClock.rate.2 hΛ) (mul_pos NativeClock.rate_pos hell)
      (mul_nonneg NativeClock.rate.2 (hell.le.trans ((hb 0).1.trans (hb 0).2)))
      (coefficientFunction (ha.const_mul (NativeClock.rate:ℝ)) (mul_pos NativeClock.rate_pos hell)
        (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hb) U) hg I
      (NativeClock.time t) (ClockedPairIntegral.time_le _ _ _ ht) :=
  ClockedPairIntegral.terminal_eq 𝓕 μ NativeClock.rate NativeClock.rate_pos h hh
    hΛ hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (coefficientFunction ha hell hb (path U)) (coefficient_predictable 𝓕 ha hell hb hm U hU) _
    hg (ClockedPairFields.unitField_coefficient _ _ ha hell hb U) I t ht

end SHE.NativePairClock
