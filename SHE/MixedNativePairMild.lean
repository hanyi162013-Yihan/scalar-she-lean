module

public import SHE.NativePairClock
public import SHE.MixedAdditiveResidualPair

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.MixedNativePairMild
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
variable (κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M)
variable (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (hmU : Measurable (NonlinearHaarIntegrand.coefficientField aU haU ell M hell hbU))
variable (hmV : Measurable (NonlinearHaarIntegrand.coefficientField aV haV ell M hell hbV))
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
variable (u₀ v₀ : StateL2)
variable (S : MixedAdditiveResidualPair.Solution 𝓕 μ h hh (mul_nonneg NativeClock.rate.2 hΛ)
  ((NativeClock.rate:ℝ)*κ) (mul_pos NativeClock.rate_pos hκ)
  (haU.const_mul (NativeClock.rate:ℝ)) (haV.const_mul (NativeClock.rate:ℝ)) (mul_pos NativeClock.rate_pos hell)
  (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hbU) (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hbV) I₀ I₁ u₀ v₀)

/-- The actual constructed two-channel solution satisfies the native
heat equation. The clocked integral and its literal Haar kernel have
already been constructed; no native mild equation is an assumption. -/
theorem first_mild (t : ℝ≥0) (ht : t≤NativeClock.rate*h) :
    NativePairClock.path S.first t=ᵐ[μ] (fun ω => NativeHeatObservation.heat (t:ℝ) u₀+
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₀).integral
        (NativePairClock.additiveInput 𝓕 μ h hh κ hκ 0 (by norm_num) t) ω+
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₁).integral
        (NativePairClock.residualInput 𝓕 μ h hh (Λ := 0) (by norm_num) haU hell hbU hmU
          S.first S.first_predictable t) ω) := by
  have hA := NativePairClock.additive_terminal_eq 𝓕 μ h hh κ hκ 0 (by norm_num) I₀ t ht
  have hR := NativePairClock.residual_terminal_eq 𝓕 μ h hh (Λ := 0) (by norm_num)
    haU hell hbU hmU S.first S.first_predictable S.first_coefficient I₁ t ht
  simp only [mul_zero] at hA hR
  filter_upwards [S.first_mild (NativeClock.time t) (ClockedPairIntegral.time_le _ _ _ ht)] with ω hω
  change S.first (NativeClock.time t) ω=_
  have hAω := congrArg (fun v : Lp StateL2 2 μ => v ω) hA
  have hRω := congrArg (fun v : Lp StateL2 2 μ => v ω) hR
  have hHeat := congrArg (fun L : StateL2→L[ℝ]StateL2 => L u₀) (NativeClock.heat_time t)
  exact hω.trans (congrArg₂ (fun x y : StateL2 => x+y)
    (congrArg₂ (fun x y : StateL2 => x+y) hHeat hAω.symm) hRω.symm)

/-- The controlled equation keeps the physical damping Λ, the same
additive channel, and the same residual Haar channel after reclocking. -/
theorem second_mild (t : ℝ≥0) (ht : t≤NativeClock.rate*h) :
    NativePairClock.path S.second t=ᵐ[μ] (fun ω =>
      Real.exp (-Λ*(t:ℝ)) • NativeHeatObservation.heat (t:ℝ) v₀+
      Λ • NativeClock.volterra Λ (fun s => NativePairClock.path S.first s ω) t+
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₀).integral
        (NativePairClock.additiveInput 𝓕 μ h hh κ hκ Λ hΛ t) ω+
      (PredictableTimeDilation.integral 𝓕 μ NativeClock.rate NativeClock.rate_pos h I₁).integral
        (NativePairClock.residualInput 𝓕 μ h hh hΛ haV hell hbV hmV
          S.second S.second_predictable t) ω) := by
  have hA := NativePairClock.additive_terminal_eq 𝓕 μ h hh κ hκ Λ hΛ I₀ t ht
  have hR := NativePairClock.residual_terminal_eq 𝓕 μ h hh hΛ
    haV hell hbV hmV S.second S.second_predictable S.second_coefficient I₁ t ht
  have hexp : -((NativeClock.rate:ℝ)*Λ)*(NativeClock.time t:ℝ)=-Λ*(t:ℝ) := by
    rw [NativeClock.time_coe,NativeClock.rate_coe]
    field_simp [NativeHeatObservation.timeScale_pos.ne']
  filter_upwards [S.second_mild (NativeClock.time t) (ClockedPairIntegral.time_le _ _ _ ht)] with ω hω
  change S.second (NativeClock.time t) ω=_
  have hAω := congrArg (fun v : Lp StateL2 2 μ => v ω) hA
  have hRω := congrArg (fun v : Lp StateL2 2 μ => v ω) hR
  have hHeat : Real.exp (-((NativeClock.rate:ℝ)*Λ)*(NativeClock.time t:ℝ)) •
      RealHeat.realHeat (NativeClock.time t:ℝ) v₀=
      Real.exp (-Λ*(t:ℝ)) • NativeHeatObservation.heat (t:ℝ) v₀ := by
    rw [hexp,NativeClock.heat_time]
  have hControl := NativeClock.volterra_time Λ (fun s => S.first s ω) t
  exact hω.trans (congrArg₂ (fun x y : StateL2 => x+y)
    (congrArg₂ (fun x y : StateL2 => x+y)
      (congrArg₂ (fun x y : StateL2 => x+y) hHeat hControl) hAω.symm) hRω.symm)

end SHE.MixedNativePairMild
