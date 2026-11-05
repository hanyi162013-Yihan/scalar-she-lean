module

public import SHE.NativePairClock
public import SHE.NativePairKernels
public import SHE.NativeMildFirst
public import SHE.NativeMildFromUnit
import all SHE.NativeMildFromUnit
public import SHE.AdditiveSmoothMild
import all SHE.AdditiveSmoothMild
public import SHE.NativePairConstruction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.NativeSmoothFirstConstruction
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
variable {K β:ℝ}(hβ:0<β)(hK:0≤K)(hholder:∀z w,|a z-a w|≤K*|z-w|^β)
variable (I:Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ h)
variable(u₀:StateL2)
local notation "rate"=>NativeClock.rate
local notation "rp"=>NativeClock.rate_pos
local notation "aScaled"=>(ha.const_mul (rate:ℝ))
local notation "ellScaled"=>(mul_pos rp hell)
local notation "boundsScaled"=>(HaarFieldScaling.scaled_bounds rp hb)
local notation "holderScaled"=>(NativeAdditiveResidualPair.scaled_holder hholder)


/-- The actual smooth unit-clock model at the native coefficient scale. -/
abbrev Model:=AdditiveSmoothMild.Solution
  (a:=fun z=>(rate:ℝ)*a z) (ell:=(rate:ℝ)*ell) (M:=(rate:ℝ)*M) (K:=(rate:ℝ)*K) (β:=β)
  (𝓕:=𝓕) (μ:=μ) (H:=h) (hH:=hh) (κ:=(rate:ℝ)*κ) (hκ:=mul_pos rp hκ)
  (ha:=aScaled) (hell:=ellScaled) (hb:=boundsScaled) (hβ:=hβ)
  (hK:=mul_nonneg rate.2 hK) (hholder:=holderScaled) (I:=I) u₀

/-- The same actual smooth paths and literal integrals give the
native first-solution data needed by the stopped comparison. -/
def native(A:Model 𝓕 μ h hh κ hκ ha hell hb hβ hK hholder I u₀):
    NativeMildFirst.Data (filtration 𝓕 (clock rate rp)) μ (rate*h) κ hκ ha hell hb
      (PredictableTimeDilation.integral 𝓕 μ rate rp h (I true))
      (PredictableTimeDilation.integral 𝓕 μ rate rp h (I false)) u₀:=
  NativeMildFromUnit.of_unit 𝓕 μ h hh κ hκ ha hell hb
    (NonlinearHaarIntegrand.coefficientField_measurable ha hell hb hβ hK hholder)
    (I true) (I false) u₀ A.model.value A.model.continuous A.predictable A.coefficient A.mild

variable(B:Bool→ℝ≥0)(hBDG:∀b,StandardTerminalBDG16 (I b) (B b))
variable(hpos:0<h)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
include hBDG hpos hnull in
/-- Ordinary smooth Picard construction supplies this native model
on the full fixed interval, with no solution/existence input. -/
theorem exists_model{L:ℝ≥0}(hLip:LipschitzWith L (fun z=>(a z:ℂ))):
    Nonempty (Model 𝓕 μ h hh κ hκ ha hell hb hβ hK hholder I u₀):=by
  exact AdditiveSmoothMild.exists_solution 𝓕 μ h hh ((rate:ℝ)*κ) (mul_pos rp hκ)
    aScaled ellScaled boundsScaled hβ (mul_nonneg rate.2 hK) holderScaled I B hBDG hpos hnull
    (NativeAdditiveResidualPair.scaled_lipschitz hLip) u₀
end SHE.NativeSmoothFirstConstruction
