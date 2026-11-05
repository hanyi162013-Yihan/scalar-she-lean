module

public import SHE.NativeScalarFourierWeight
public import SHE.NativeMultiplierFourierIntegral
public import SHEStochastic.NativePhysicalState
public import SHEStochastic.NativeRemainderObservation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.NativeFourierHeatCoordinate
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open HeatParameterCover HeatParameterPullback
open scoped ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def coordinate (a : ℂ →L[ℝ] ℝ) (n : ℤ) : RealL2 →L[ℝ] ℝ :=
  a.comp ((NativeFourierNoiseRows.coefficient n).comp NativeHeatObservation.embed)

def weight (a : ℂ →L[ℝ] ℝ) (n : ℤ) : C(HeatCircle, ℝ) :=
  ⟨NativeScalarFourierWeight.value 1 a n,
    continuous_const.mul (a.continuous.comp (fourier (-n)).continuous)⟩

theorem weight_norm_bound (a : ℂ →L[ℝ] ℝ) (n : ℤ) : ‖weight a n‖ ≤ ‖a‖ := by
  apply ((weight a n).norm_le (norm_nonneg a)).mpr
  intro x
  simpa only [weight, ContinuousMap.coe_mk, norm_one, one_mul] using NativeScalarFourierWeight.bound 1 a n x

/-- A real Fourier coordinate of the original native state is the
already proved signed spatial Fourier average of its physical state. -/
theorem coordinate_integral (a : ℂ →L[ℝ] ℝ) (n : ℤ) (u : RealL2) :
    coordinate a n u = ∫ x : HeatCircle, weight a n x * NativePhysicalState.push u x ∂haarAddCircle := by
  have he : fourierCoeff (NativeHeatObservation.embed u) n =
      fourierCoeff (fun x : HeatCircle ↦ (NativePhysicalState.push u x : ℂ)) n := by
    unfold fourierCoeff
    apply integral_congr_ae
    filter_upwards [NativePhysicalState.embed_eq_push u] with x hx
    rw [hx]
  have hi := NativeScalarFourierWeight.integral (NativePhysicalState.push u)
    ((Lp.memLp _).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) 1 a n
  change a (NativeFourierNoiseRows.coefficient n (NativeHeatObservation.embed u)) = _
  rw [NativeMultiplierFourierIntegral.coefficient_apply, he]
  simpa only [weight, ContinuousMap.coe_mk, one_mul] using hi.symm

theorem coordinate_heat (a : ℂ →L[ℝ] ℝ) (n : ℤ) {t : ℝ} (ht : 0 ≤ t) (u : RealL2) :
    coordinate a n (NativeHeatObservation.heat t u) = Real.exp (-t * (n : ℝ) ^ 2) * coordinate a n u := by
  change a (NativeFourierNoiseRows.coefficient n (NativeHeatObservation.embed (NativeHeatObservation.heat t u))) =
    Real.exp (-t * (n : ℝ) ^ 2) * a (NativeFourierNoiseRows.coefficient n (NativeHeatObservation.embed u))
  rw [NativeHeatObservation.embed_heat ht, NativeMultiplierFourierIntegral.coefficient_apply,
    NativeMultiplierFourierIntegral.coefficient_apply, circleHeatOperator_fourierCoeff]
  change a (Real.exp (-t * (n : ℝ) ^ 2) • fourierCoeff (NativeHeatObservation.embed u) n) =
    Real.exp (-t * (n : ℝ) ^ 2) • a (fourierCoeff (NativeHeatObservation.embed u) n)
  exact map_smul a _ _

theorem coordinate_remainder (a : ℂ →L[ℝ] ℝ) (n : ℤ) (Y : C(Parameter, ℝ)) (t : ShortTime) :
    coordinate a n (NativeRemainderObservation.remainder Y t) =
      ∫ x : HeatCircle, weight a n x * Y (point t x) ∂haarAddCircle := by
  rw [coordinate_integral]
  change (∫ x : HeatCircle, weight a n x *
    NativePhysicalState.push (NativePhysicalState.pull (PhysicalHeatParameterSection.value 2 Y t)) x ∂haarAddCircle) = _
  rw [NativePhysicalState.push_pull]
  apply integral_congr_ae
  filter_upwards [PhysicalHeatParameterSection.value_ae 2 Y t] with x hx
  rw [hx]

/-- Real and imaginary Fourier weights are eigenfunctions of the
literal physical heat average, with the exact physical time exponent. -/
theorem weight_average (a : ℂ →L[ℝ] ℝ) (n : ℤ) {r : ℝ} (hr : 0 < r) (x : HeatCircle) :
    (∫ y : HeatCircle, weight a n y * RealCausalHeatKernel.value x r y ∂haarAddCircle) =
      Real.exp (-r * (n : ℝ) ^ 2) * weight a n x := by
  have hk : (fun y : HeatCircle ↦ (RealCausalHeatKernel.value x r y : ℂ)) =ᵐ[haarAddCircle]
      (circleHeat r x : HeatCircle → ℂ) := by
    have he := (SHE.NativeHeatSpan.kernel_physical_ae hr x).trans (SHE.ProfileVariance.heatPhysical_ae hr x)
    exact he.mono fun y hy ↦ (RealCausalHeatKernel.complex_eq hr x y).symm.trans hy
  have he : fourierCoeff (fun y : HeatCircle ↦ (RealCausalHeatKernel.value x r y : ℂ)) n = heatCoeff r x n := by
    calc
      _ = fourierCoeff (circleHeat r x) n := by
        unfold fourierCoeff
        apply integral_congr_ae
        filter_upwards [hk] with y hy
        rw [hy]
      _ = _ := circleHeat_fourierCoeff hr x n
  have hi := NativeScalarFourierWeight.integral (RealCausalHeatKernel.value x r)
    ((RealCausalHeatKernel.value x r).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) 1 a n
  have hi' : (∫ y : HeatCircle, weight a n y * RealCausalHeatKernel.value x r y ∂haarAddCircle) = a (heatCoeff r x n) := by
    simpa only [weight, ContinuousMap.coe_mk, one_mul, he] using hi
  refine hi'.trans ?_
  change a (fourier (-n) x * (Real.exp (-r * (n : ℝ) ^ 2) : ℂ)) =
    Real.exp (-r * (n : ℝ) ^ 2) * (1 * a (fourier (-n) x))
  rw [one_mul, mul_comm]
  change a (Real.exp (-r * (n : ℝ) ^ 2) • fourier (-n) x) =
    Real.exp (-r * (n : ℝ) ^ 2) • a (fourier (-n) x)
  exact map_smul a _ _

theorem kernel_average (a : ℂ →L[ℝ] ℝ) (n : ℤ) {r : ℝ} (hr : 0 < r) :
    (∫ x : HeatCircle, weight a n x • RealCausalHeatKernel.value x r ∂haarAddCircle) =
      Real.exp (-r * (n : ℝ) ^ 2) • weight a n := by
  have hc : Continuous (fun x : HeatCircle ↦ weight a n x • RealCausalHeatKernel.value x r) :=
    (weight a n).continuous.smul (RealCausalHeatKernel.continuous_center hr)
  have hi : Integrable (fun x : HeatCircle ↦ weight a n x • RealCausalHeatKernel.value x r) haarAddCircle :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  ext y
  rw [ContinuousMap.integral_apply hi]
  change (∫ x : HeatCircle, weight a n x * RealCausalHeatKernel.value x r y ∂haarAddCircle) =
    Real.exp (-r * (n : ℝ) ^ 2) * weight a n y
  calc
    _ = ∫ x : HeatCircle, weight a n x * RealCausalHeatKernel.value y r x ∂haarAddCircle :=
      integral_congr_ae (Eventually.of_forall fun x ↦ congrArg (fun z : ℝ ↦ weight a n x * z)
        (RealCausalHeatKernel.symm hr x y))
    _ = _ := weight_average a n hr y

end SHEStochastic.NativeFourierHeatCoordinate
