module

public import SHE.NativeFirstUnitMild
public import SHE.TimeDilationRoundTrip
public import SHE.ClockedOriginalIntegral
public import SHE.TimeDilationPathPull
public import SHE.NativePairKernels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.NativeFirstRealization
open MeasureTheory Set PredictableTimeDilation PredictableL2 LowBands FiniteHaar ContinuousHeatMild
open scoped NNReal ENNReal
local instance nativeFirstRealization_finite : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance nativeFirstRealization_stateSigma : MeasurableSpace StateL2:=borel _
local instance nativeFirstRealization_stateBorel : BorelSpace StateL2:=⟨rfl⟩
local instance nativeFirstRealization_nativeSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeFirstRealization_nativeBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeFirstRealization_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance nativeFirstRealization_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ)≤1)
variable (κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
local notation "rate"=>NativeClock.rate
local notation "ratePos"=>NativeClock.rate_pos
variable (J₀ J₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) (filtration 𝓕 (clock rate ratePos)) μ (rate*h))
variable (u₀ : StateL2)

variable (S : NativeFirstClockPull.FirstSolution 𝓕 μ h κ hκ ha hell hb J₀ J₁ u₀)
local notation "U"=>pullPath rate ratePos S.value
local notation "g"=>coefficientFunction (ha.const_mul (rate:ℝ)) (mul_pos ratePos hell)
  (HaarFieldScaling.scaled_bounds ratePos hb) U
local notation "hg"=>NativeFirstClockPull.unit_coefficient_predictable 𝓕 μ h κ hκ ha hell hb J₀ J₁ u₀ S
local notation "I₀"=>inverseIntegral 𝓕 μ rate ratePos h J₀
local notation "I₁"=>inverseIntegral 𝓕 μ rate ratePos h J₁

/-- Exact unit-clock realization of an arbitrary supplied native first
solution. This realization is DERIVED, preserving the given state path
and original additive/residual noise coordinates through the round trip. -/
def to_unit : GivenFirstResidualPair.FirstSolution 𝓕 μ h hh
    ((rate:ℝ)*κ) (mul_pos ratePos hκ) (ha.const_mul (rate:ℝ)) (mul_pos ratePos hell)
    (HaarFieldScaling.scaled_bounds ratePos hb) I₀ I₁ u₀ where
  process:=pullStateProcess 𝓕 μ rate ratePos h S.process
  value:=U
  continuous:=pullPath_continuous rate ratePos S.value S.continuous
  predictable:=pullPath_predictable 𝓕 rate ratePos S.value S.predictable
  ae:=pullStateProcess_ae 𝓕 μ rate ratePos h S.process S.value S.ae
  coefficient:=hg
  mild:=by
    intro t ht
    exact NativeFirstUnitMild.unit_mild 𝓕 μ h hh κ hκ ha hell hb J₀ J₁ u₀ S t ht

/-- The actual first path returns POINTWISE to its supplied native
version after inverse-clock realization and physical-clock transport. -/
theorem first_round_trip :
    NativePairClock.path (to_unit 𝓕 μ h hh κ hκ ha hell hb J₀ J₁ u₀ S).value=S.value :=
  path_pullPath rate ratePos S.value

end SHE.NativeFirstRealization
