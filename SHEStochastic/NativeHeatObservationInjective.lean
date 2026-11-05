module

public import SHEStochastic.NativePhysicalState
public import SHEStochastic.ContinuousKernelLpAction
public import SHE.LpIntegralFubini
public import BrownianMotion.Continuity.KolmogorovChentsov

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.NativeHeatObservationInjective
open MeasureTheory ProbabilityTheory SHE SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter Set
open scoped ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem circle_heat_injective (t : ℝ) (ht : 0 ≤ t) : Function.Injective (circleHeatOperator t ht) := by
  intro u v h
  apply (fourierBasis (T := 2 * Real.pi)).repr.injective
  apply lp.ext
  funext n
  have he := congrArg (fun w : CircleL2 ↦ fourierCoeff w n) h
  change fourierCoeff (circleHeatOperator t ht u) n = fourierCoeff (circleHeatOperator t ht v) n at he
  rw [circleHeatOperator_fourierCoeff, circleHeatOperator_fourierCoeff] at he
  have hn : (Real.exp (-t * (n : ℝ) ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  simpa only [fourierBasis_repr] using mul_left_cancel₀ hn he

theorem embed_injective : Function.Injective NativeHeatObservation.embed := by
  intro u v h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hh := NativeHeatObservation.embed_norm (u - v)
  rw [map_sub, h, sub_self, norm_zero] at hh
  exact hh.symm

theorem heat_injective (t : ℝ) (ht : 0 ≤ t) : Function.Injective (NativeHeatObservation.heat t) := by
  intro u v h
  apply embed_injective
  apply circle_heat_injective t ht
  have hh := congrArg NativeHeatObservation.embed h
  simpa only [NativeHeatObservation.embed_heat ht] using hh

theorem continuous_center {r : ℝ} (hr : 0 < r) (u : RealL2) :
    Continuous (fun x : HeatCircle ↦ NativeHeatObservation.functional r x u) := by
  let L : C(HeatCircle, ℝ) →L[ℝ] ℝ :=
    (LpIntegralFubini.setIntegralCLM (E := ℝ) haarAddCircle univ).comp
      (ContinuousKernelLpAction.operator haarAddCircle (NativePhysicalState.push u))
  have hc := L.continuous.comp (RealCausalHeatKernel.continuous_center hr)
  convert hc using 1
  funext x
  change NativeHeatObservation.functional r x u =
    ∫ a in univ, ContinuousKernelLpAction.operator haarAddCircle (NativePhysicalState.push u)
      (RealCausalHeatKernel.value x r) a ∂haarAddCircle
  rw [Measure.restrict_univ, NativePhysicalState.functional_integral hr]
  apply integral_congr_ae
  exact (ContinuousKernelLpAction.operator_ae haarAddCircle (NativePhysicalState.push u)
    (RealCausalHeatKernel.value x r)).symm

theorem heat_state_ae {r : ℝ} (hr : 0 < r) (u : RealL2) :
    NativePhysicalState.push (NativeHeatObservation.heat r u) =ᵐ[haarAddCircle]
      fun x ↦ NativeHeatObservation.functional r x u := by
  rw [NativePhysicalState.push_heat hr.le, PhysicalHeatState.state_eq_value hr]
  simpa only [NativeHeatObservation.functional_physical hr] using
    PhysicalHeatSmoothing.value_ae 2 r hr (NativeHeatObservation.embed u)

/-- One positive heat age and all spatial centers determine the state;
no limit of observation ages is necessary. -/
theorem eq_of_observations {r : ℝ} (hr : 0 < r) (u v : RealL2)
    (he : ∀ x : HeatCircle, NativeHeatObservation.functional r x u = NativeHeatObservation.functional r x v) :
    u = v := by
  apply heat_injective r hr.le
  apply NativePhysicalState.push.injective
  apply Lp.ext
  filter_upwards [heat_state_ae hr u, heat_state_ae hr v] with x hu hv
  exact hu.trans ((he x).trans hv.symm)

/-- Fixed-center almost-sure observation equalities determine the actual
random L2 states. Separability and center continuity supply one common
null set; no extra state measurability or moment assumption is introduced. -/
theorem ae_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {r : ℝ} (hr : 0 < r) (U V : Ω → RealL2)
    (he : ∀ x : HeatCircle, (fun ω ↦ NativeHeatObservation.functional r x (U ω)) =ᵐ[μ]
      fun ω ↦ NativeHeatObservation.functional r x (V ω)) : U =ᵐ[μ] V := by
  have hu : ∀ᵐ ω ∂μ, Continuous (fun x : HeatCircle ↦ NativeHeatObservation.functional r x (U ω)) :=
    Eventually.of_forall fun ω ↦ continuous_center hr (U ω)
  have hv : ∀ᵐ ω ∂μ, Continuous (fun x : HeatCircle ↦ NativeHeatObservation.functional r x (V ω)) :=
    Eventually.of_forall fun ω ↦ continuous_center hr (V ω)
  have hh := indistinguishable_of_edist_modification hu hv
    (fun x ↦ (he x).mono fun _ h ↦ edist_eq_zero.mpr h)
  exact hh.mono fun ω hω ↦ eq_of_observations hr (U ω) (V ω) (fun x ↦ edist_eq_zero.mp (hω x))

theorem ae_eq_on {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {r : ℝ} (hr : 0 < r) (U V : Ω → RealL2) (A : Ω → Prop)
    (he : ∀ x : HeatCircle, ∀ᵐ ω ∂μ, A ω →
      NativeHeatObservation.functional r x (U ω) = NativeHeatObservation.functional r x (V ω)) :
    ∀ᵐ ω ∂μ, A ω → U ω = V ω := by
  classical
  let W (ω : Ω) := if A ω then U ω else V ω
  have hh := ae_eq μ hr W V (fun x ↦ (he x).mono fun ω hω ↦ by
    by_cases hA : A ω
    · simpa only [W, if_pos hA] using hω hA
    · simp only [W, if_neg hA])
  exact hh.mono fun ω hω hA ↦ by simpa only [W, if_pos hA] using hω

end SHEStochastic.NativeHeatObservationInjective
