module

public import SHE.NativeObservationEndpoint
public import SHE.NativeObservationNaturality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Deterministic stopping of genuine predictable L² inputs and its
exact identification with the original-target physical heat rows. -/
noncomputable section
namespace SHE.StoppedItoInputs
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationCovariance
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)

def before (t : ℝ) : Set (ℝ≥0 × Ω) := {p | (p.1:ℝ) < t}

theorem before_measurable (t : ℝ) : MeasurableSet[𝓕.predictable] (before (Ω := Ω) t) :=
  measurableSet_lt (PredictableClock.real_time_measurable 𝓕) measurable_const

def stop (t : ℝ) (v : Process (E := C) 𝓕 μ h) : Process (E := C) 𝓕 μ h :=
  ((Lp.memLp v).indicator (before_measurable 𝓕 t).nullMeasurableSet).toLp
    ((before t).indicator v)

theorem stop_ae (t : ℝ) (v : Process (E := C) 𝓕 μ h) :
    stop 𝓕 μ h t v =ᵐ[energyMeasure μ h] (before t).indicator v :=
  ae_eq_of_ae_eq_trim ((Lp.memLp v).indicator (before_measurable 𝓕 t).nullMeasurableSet).coeFn_toLp

theorem stop_stopped (t : ℝ≥0) (v : Process (E := C) 𝓕 μ h) :
    ∀ᵐ p ∂energyMeasure μ h,t < p.1 → stop 𝓕 μ h t v p=0 := by
  filter_upwards [stop_ae 𝓕 μ h t v] with p hp htp
  rw [hp,Set.indicator_of_notMem]
  change ¬ (p.1:ℝ) < (t:ℝ)
  exact not_lt.mpr (by exact_mod_cast htp.le)

theorem stop_zero (v : Process (E := C) 𝓕 μ h) : stop 𝓕 μ h 0 v=0 := by
  apply Lp.ext
  have hs := ((Lp.memLp v).indicator (before_measurable 𝓕 0).nullMeasurableSet).coeFn_toLp
  filter_upwards [hs,
    Lp.coeFn_zero C 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕))] with p hp hz
  unfold stop
  rw [hp,hz,Set.indicator_of_notMem (show p ∉ before (Ω := Ω) 0 from not_lt.mpr p.1.2)]
  rfl

variable [NormedSpace ℝ C]

theorem stopped_integral_adapted (I : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h)
    (t : ℝ≥0) (v : Process (E := C) 𝓕 μ h) :
    ∃ Z : Ω → ℝ,StronglyMeasurable[𝓕 t] Z ∧ I.integral (stop 𝓕 μ h t v)=ᵐ[μ] Z :=
  I.adapted t _ (stop_stopped 𝓕 μ h t v)

section Native
open FiniteHaar StoppedFourier
local instance stoppedItoInputs_rowSigma : MeasurableSpace RealHaarInput := borel RealHaarInput
local instance stoppedItoInputs_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable [IsProbabilityMeasure μ]

/-- Restricting the endpoint noise row to times before t gives exactly
the observed native mild-convolution input. Both are actual predictable
L² classes; no equality of noise coefficients is assumed. -/
theorem stop_endpoint_process {ell M T t : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (hT : (h:ℝ) ≤ T) (ht : t < T) (x : HeatCircle) :
    stop 𝓕 μ h t (NativeObservationEndpoint.process 𝓕 μ h hell hM f hf hT x)=
      NativeObservationProcess.process 𝓕 μ h hell hM f hf ht x := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  filter_upwards [stop_ae 𝓕 μ h t (NativeObservationEndpoint.process 𝓕 μ h hell hM f hf hT x),
    NativeObservationEndpoint.process_ae 𝓕 μ h hell hM f hf hT x,
    NativeObservationProcess.process_ae 𝓕 μ h hell hM f hf ht x] with p hs hf hr
  rw [hs,hr,NativeObservationProcess.integrand_eq hell f ht]
  by_cases hp : (p.1:ℝ) < t
  · rw [Set.indicator_of_mem (show p ∈ before (Ω := Ω) t from hp),hf,NativeObservationEndpoint.fullIntegrand,
      ite_eq_left (hp.trans ht),ite_eq_left hp]
  · rw [Set.indicator_of_notMem (show p ∉ before (Ω := Ω) t from hp),ite_eq_right hp]

end Native
end SHE.StoppedItoInputs
