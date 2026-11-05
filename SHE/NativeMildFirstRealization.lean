module

public import SHE.NativeMildUnitEquation
public import SHE.MildFirstL2Realization
public import SHE.TimeDilationStatePush
public import SHE.ClockedOriginalIntegral
public import SHE.TimeDilationPathPull
public import SHE.NativePairKernels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.NativeMildFirstRealization
open MeasureTheory Set PredictableTimeDilation PredictableL2 LowBands FiniteHaar ContinuousHeatMild
open scoped NNReal ENNReal
local instance nativeMildFirstRealization_finite : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance nativeMildFirstRealization_stateSigma : MeasurableSpace StateL2:=borel _
local instance nativeMildFirstRealization_stateBorel : BorelSpace StateL2:=⟨rfl⟩
local instance nativeMildFirstRealization_nativeSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeMildFirstRealization_nativeBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeMildFirstRealization_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance nativeMildFirstRealization_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ)≤1)
variable (κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
local notation "rate"=>NativeClock.rate
local notation "ratePos"=>NativeClock.rate_pos
variable (J₀ J₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) (filtration 𝓕 (clock rate ratePos)) μ (rate*h))
variable (u₀ : StateL2)

variable (S : NativeFirstMildData.Data 𝓕 μ h κ hκ ha hell hb J₀ J₁ u₀)
local notation "U"=>pullPath rate ratePos S.value
local notation "g"=>coefficientFunction (ha.const_mul (rate:ℝ)) (mul_pos ratePos hell)
  (HaarFieldScaling.scaled_bounds ratePos hb) U
local notation "hg"=>NativeFirstMildData.unit_coefficient_predictable 𝓕 μ h κ hκ ha hell hb J₀ J₁ u₀ S
local notation "I₀"=>inverseIntegral 𝓕 μ rate ratePos h J₀
local notation "I₁"=>inverseIntegral 𝓕 μ rate ratePos h J₁

include hh in
/-- The finite predictable L² representative is derived for a GIVEN
native mild first solution. The proof uses the actual two heat
convolutions, exact same-noise inverse clock and fixed-time equality;
no a priori solution energy, Picard or coefficient Lipschitz is used. -/
theorem exists_first_solution (hpos : 0<h) (B₀ B₁ : ℝ≥0)
    (hBDG₀ : StandardTerminalBDG16 J₀ B₀) (hBDG₁ : StandardTerminalBDG16 J₁ B₁) :
    ∃ N : NativeFirstClockPull.FirstSolution 𝓕 μ h κ hκ ha hell hb J₀ J₁ u₀,N.value=S.value := by
  have hb₀ : StandardTerminalBDG16 I₀ B₀:=inverse_bdgPower 𝓕 μ rate ratePos h 8 J₀ B₀ hBDG₀
  have hb₁ : StandardTerminalBDG16 I₁ B₁:=inverse_bdgPower 𝓕 μ rate ratePos h 8 J₁ B₁ hBDG₁
  have hUm:=NativeFirstMildData.unitPath_predictable 𝓕 μ h κ hκ ha hell hb J₀ J₁ u₀ S
  obtain ⟨w,hw⟩:=MildFirstL2Realization.exists_process 𝓕 μ h hh
    (mul_pos ratePos hκ) (mul_nonneg rate.2 hκ.le)
    (mul_pos ratePos hell) (mul_nonneg rate.2 (hell.le.trans ((hb 0).1.trans (hb 0).2)))
    (fun _=>AdditiveHaarForcing.constantField ((rate:ℝ)*κ) (mul_pos ratePos hκ))
    stronglyMeasurable_const g hg I₀ I₁ hpos B₀ B₁ hb₀ hb₁ u₀ U hUm
    (NativeMildUnitEquation.unit_mild 𝓕 μ h hh κ hκ ha hell hb J₀ J₁ u₀ S)
  let wnative:=pushStateProcess 𝓕 μ rate ratePos h w
  have he : wnative=ᵐ[energyMeasure μ (rate*h)] Function.uncurry S.value := by
    have hh':=pushStateProcess_ae 𝓕 μ rate ratePos h w U hw
    filter_upwards [hh'] with p hp
    exact hp.trans (congrArg (fun t=>S.value t p.2) ((clock rate ratePos).apply_symm_apply p.1))
  exact ⟨{ process:=wnative
           value:=S.value
           continuous:=S.continuous
           predictable:=S.predictable
           ae:=he
           coefficient:=S.coefficient
           additiveInput:=S.additiveInput
           residualInput:=S.residualInput
           additive_kernel:=S.additive_kernel
           residual_kernel:=S.residual_kernel
           mild:=S.mild },rfl⟩

end SHE.NativeMildFirstRealization
