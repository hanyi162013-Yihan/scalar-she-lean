module

public import SHE.NativePairClock
public import SHE.NativePairKernels
public import SHE.NativeMildFirst

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.NativeMildFromUnit
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
variable (h : ℝ≥0) (hh : (h:ℝ)≤1)
variable (κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (hm : Measurable (NonlinearHaarIntegrand.coefficientField a ha ell M hell hb))
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
variable (u₀:StateL2)(U:ℝ≥0→Ω→StateL2)
variable(hUc:∀ω,Continuous (fun t=>U t ω))
variable(hUp:StronglyMeasurable[𝓕.predictable] (Function.uncurry U))
variable(hUf:StronglyMeasurable[𝓕.predictable]
  (coefficientFunction (ha.const_mul (NativeClock.rate:ℝ)) (mul_pos NativeClock.rate_pos hell)
    (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hb) U))
variable(hmild:∀(t:ℝ≥0)(ht:t≤h),U t=ᵐ[μ] fun ω=>RealHeat.realHeat (t:ℝ) u₀+
  AdditiveResidualPair.additiveTerminal 𝓕 μ h hh (Λ:=0) (by norm_num)
    ((NativeClock.rate:ℝ)*κ) (mul_pos NativeClock.rate_pos hκ) I₀ t ht ω+
  DampedFixedIntegral.value 𝓕 μ h hh (Λ:=0) (by norm_num) (mul_pos NativeClock.rate_pos hell)
    (mul_nonneg NativeClock.rate.2 (hell.le.trans ((hb 0).1.trans (hb 0).2)))
    (coefficientFunction (ha.const_mul (NativeClock.rate:ℝ)) (mul_pos NativeClock.rate_pos hell)
      (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hb) U) hUf I₁ t ht ω)
include hmild in
/-- The actual constructed two-channel solution satisfies the native
heat equation. The clocked integral and its literal Haar kernel have
already been constructed; no native mild equation is an assumption. -/
theorem mild (t : ℝ≥0) (ht : t≤NativeClock.rate*h) :
    NativePairClock.path U t=ᵐ[μ] (fun ω => NativeHeatObservation.heat (t:ℝ) u₀+
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₀).integral
        (NativePairClock.additiveInput 𝓕 μ h hh κ hκ 0 (by norm_num) t) ω+
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₁).integral
        (NativePairClock.residualInput 𝓕 μ h hh (Λ := 0) (by norm_num) ha hell hb hm
          U hUp t) ω) := by
  have hA := NativePairClock.additive_terminal_eq 𝓕 μ h hh κ hκ 0 (by norm_num) I₀ t ht
  have hR := NativePairClock.residual_terminal_eq 𝓕 μ h hh (Λ := 0) (by norm_num)
    ha hell hb hm U hUp hUf I₁ t ht
  simp only [mul_zero] at hA hR
  filter_upwards [hmild (NativeClock.time t) (ClockedPairIntegral.time_le _ _ _ ht)] with ω hω
  change U (NativeClock.time t) ω=_
  have hAω := congrArg (fun v : Lp StateL2 2 μ => v ω) hA
  have hRω := congrArg (fun v : Lp StateL2 2 μ => v ω) hR
  have hHeat := congrArg (fun L : StateL2→L[ℝ]StateL2 => L u₀) (NativeClock.heat_time t)
  exact hω.trans (congrArg₂ (fun x y : StateL2 => x+y)
    (congrArg₂ (fun x y : StateL2 => x+y) hHeat hAω.symm) hRω.symm)


/-- Exact deterministic reclocking preserves the actual first equation
and provides its literal native Haar kernels. -/
def of_unit :NativeMildFirst.Data
    (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h)
    κ hκ ha hell hb
    (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₀)
    (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₁) u₀ where
  value:=NativePairClock.path U
  continuous:=NativePairClock.path_continuous U hUc
  predictable:=NativePairClock.path_predictable 𝓕 U hUp
  coefficient:=NativePairClock.coefficient_predictable 𝓕 ha hell hb hm U hUp
  additiveInput:=NativePairClock.additiveInput 𝓕 μ h hh κ hκ 0 (by norm_num)
  residualInput:=NativePairClock.residualInput 𝓕 μ h hh (Λ:=0) (by norm_num) ha hell hb hm U hUp
  additive_kernel:=NativePairClock.additiveInput_zero_ae 𝓕 μ h hh κ hκ
  residual_kernel:=NativePairClock.residualInput_zero_ae 𝓕 μ h hh ha hell hb hm U hUp
  mild:=mild 𝓕 μ h hh κ hκ ha hell hb hm I₀ I₁ u₀ U hUp hUf hmild
end SHE.NativeMildFromUnit
