module

public import SHE.NativeFirstClockPull
public import SHE.TimeDilationPathPull
public import SHE.NativePairKernels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.NativeFirstMildData
open MeasureTheory Set PredictableTimeDilation PredictableL2 LowBands FiniteHaar ContinuousHeatMild
open scoped NNReal ENNReal
local instance nativeFirstMildData_finite : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance nativeFirstMildData_stateSigma : MeasurableSpace StateL2:=borel _
local instance nativeFirstMildData_stateBorel : BorelSpace StateL2:=⟨rfl⟩
local instance nativeFirstMildData_nativeSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeFirstMildData_nativeBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeFirstMildData_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance nativeFirstMildData_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ)≤1)
variable (κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
local notation "rate"=>NativeClock.rate
local notation "ratePos"=>NativeClock.rate_pos
variable (J₀ J₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) (filtration 𝓕 (clock rate ratePos)) μ (rate*h))
variable (u₀ : StateL2)

/-- A given native-clock additive/residual mild first solution, with
literal heat-Haar kernels. Finite predictable L² energy is derived later.
The original native integrals are arbitrary; no prior unit-clock
realization, Lipschitz coefficient or uniqueness is assumed. -/
structure Data where
  value : ℝ≥0→Ω→StateL2
  continuous : ∀ ω,Continuous (fun t=>value t ω)
  predictable : StronglyMeasurable[(filtration 𝓕 (clock rate ratePos)).predictable] (Function.uncurry value)
  coefficient : StronglyMeasurable[(filtration 𝓕 (clock rate ratePos)).predictable] (coefficientFunction ha hell hb value)
  additiveInput : ℝ≥0→Process (E:=RealHaarIntegrand.Columns) (filtration 𝓕 (clock rate ratePos)) μ (rate*h)
  residualInput : ℝ≥0→Process (E:=RealHaarIntegrand.Columns) (filtration 𝓕 (clock rate ratePos)) μ (rate*h)
  additive_kernel : ∀ t,t≤rate*h→ additiveInput t=ᵐ[energyMeasure μ (rate*h)]
    fun p=>NativeHeatObservation.kernel κ κ hκ
      ((t:ℝ)-(p.1:ℝ),AdditiveHaarForcing.constantField κ hκ)
  residual_kernel : ∀ t,t≤rate*h→ residualInput t=ᵐ[energyMeasure μ (rate*h)]
    fun p=>NativeHeatObservation.kernel ell M hell
      ((t:ℝ)-(p.1:ℝ),coefficientFunction ha hell hb value p)
  mild : ∀ t,t≤rate*h→value t=ᵐ[μ] fun ω=>NativeHeatObservation.heat (t:ℝ) u₀+
    J₀.integral (additiveInput t) ω+J₁.integral (residualInput t) ω

variable (S : Data 𝓕 μ h κ hκ ha hell hb J₀ J₁ u₀)

local notation "U"=>pullPath rate ratePos S.value

omit [IsProbabilityMeasure μ] in
theorem unitPath_predictable : StronglyMeasurable[𝓕.predictable] (Function.uncurry U):=
  pullPath_predictable 𝓕 rate ratePos S.value S.predictable

omit [IsProbabilityMeasure μ] in
theorem unit_coefficient_predictable : StronglyMeasurable[𝓕.predictable]
    (coefficientFunction (ha.const_mul (rate:ℝ)) (mul_pos ratePos hell)
      (HaarFieldScaling.scaled_bounds ratePos hb) U) := by
  have he:=ClockedPairFields.unitField_coefficient rate ratePos ha hell hb U
  rw [path_pullPath] at he
  rw [← he]
  exact ClockedHaarIntegral.unitField_predictable 𝓕 rate ratePos _ S.coefficient

end SHE.NativeFirstMildData
