module

public import SHEStochastic.GlobalRemainderObservation
public import SHEStochastic.UnboundedGlobalHeatContinuity
public import SHEStochastic.PhysicalConditionalFieldEquality
public import SHEStochastic.NativeHeatObservationInjective

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.GlobalLocalizedRemainderObservation
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter Set
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback UnboundedGlobalJointMoments GlobalHeatRowPhysicalIntegration
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) (hH : 0<H) {R : ℝ}
  (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

/-- A locally assembled convolution has the correct native stochastic
heat observations before the exit. The continuous cutoff modification is
constructed internally, and Fubini removes the spatial exceptional sets. -/
theorem observation (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ ω, Continuous (fun p ↦ Y p ω)) (r : Ω → WithTop ℝ≥0) (hr : IsStoppingTime F r)
    (hlocal : ∀ p, ∀ᵐ ω ∂μ, (GlobalHeatParameter.time H p : WithTop ℝ≥0) < r ω →
      Y p ω = UnboundedGlobalHeatContinuity.observation F U hU hG hβ hβ1 μ H hbound P e p ω)
    (T δ : ℝ≥0) (hTH : T ≤ H) (hδ : 0 < δ)
    (hTD : T + δ ≤ H) (x : HeatCircle) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < r ω →
      NativeHeatObservation.functional δ x
        (NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hc ω⟩ (unitTime H hH T hTH)) =
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H T
          (UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H (T + δ) hTD x hbound)) ω := by
  obtain ⟨Z, hZm, hZe, hZc⟩ := UnboundedGlobalHeatContinuity.exists_native_continuous_modification
    F U hU hG hβ hβ1 μ H hbound P e
  let t : ShortTime := unitTime H hH T hTH
  let A : Set Ω := {ω | (T : WithTop ℝ≥0) < r ω}
  have hA : MeasurableSet A := by
    simpa only [A, compl_setOf, not_le] using ((F.le T) _ (hr T)).compl
  have heq (a : HeatCircle) : ∀ᵐ ω ∂μ, ω ∈ A → Y (point t a) ω = Z (point t a) ω := by
    filter_upwards [hlocal (point t a), hZe (point t a)] with ω hy hz hω
    have ht : GlobalHeatParameter.time H (point t a)=T :=
      NNReal.eq (GlobalHeatParameter.time_point H hH ⟨T,T.property,hTH⟩ a)
    have hh : (GlobalHeatParameter.time H (point t a) : WithTop ℝ≥0) < r ω := by rw [ht]; exact hω
    exact (hy hh).trans hz.symm
  have hfield := PhysicalConditionalFieldEquality.ae_eq μ Y Z hm hc hZm hZc t A hA heq
  have hobs := GlobalRemainderObservation.stochastic_observation F U hU hG hβ hβ1 μ H hH hbound
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) T δ hTH hδ hTD x Z hZm hZc hZe
  filter_upwards [hfield, hobs] with ω hf ho hω
  have he := congrArg NativePhysicalState.pull (hf hω)
  exact (congrArg (NativeHeatObservation.functional δ x) he).trans ho

/-- A local positive-heat equation identifies the actual original L2
state with its heat orbit plus the assembled continuous remainder before
the exit. One admissible positive heat age suffices for all centers. -/
theorem state_eq (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ ω, Continuous (fun p ↦ Y p ω)) (r : Ω → WithTop ℝ≥0) (hr : IsStoppingTime F r)
    (hlocal : ∀ p, ∀ᵐ ω ∂μ, (GlobalHeatParameter.time H p : WithTop ℝ≥0) < r ω →
      Y p ω = UnboundedGlobalHeatContinuity.observation F U hU hG hβ hβ1 μ H hbound P e p ω)
    (T δ : ℝ≥0) (hTH : T ≤ H) (hδ : 0 < δ)
    (hTD : T + δ ≤ H)
    (u₀ : Ω → RealL2) (W : Ω → RealL2)
    (hequation : ∀ x : HeatCircle, ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < r ω →
      NativeHeatObservation.functional δ x (W ω) = NativeHeatObservation.functional (T + δ) x (u₀ ω) +
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (StoppedItoInputs.stop F μ H T
            (UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H (T + δ) hTD x hbound)) ω) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < r ω → W ω = NativeHeatObservation.heat T (u₀ ω) +
      NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hc ω⟩ (unitTime H hH T hTH) := by
  apply NativeHeatObservationInjective.ae_eq_on μ hδ W
    (fun ω ↦ NativeHeatObservation.heat T (u₀ ω) +
      NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hc ω⟩ (unitTime H hH T hTH))
    (fun ω ↦ (T : WithTop ℝ≥0) < r ω)
  intro x
  have hmean (ω : Ω) : NativeHeatObservation.functional δ x (NativeHeatObservation.heat T (u₀ ω)) =
      NativeHeatObservation.functional (T + δ) x (u₀ ω) := by
    have hage : (δ : ℝ) + (T : ℝ) = ((T + δ : ℝ≥0) : ℝ) := by
      change (δ : ℝ) + (T : ℝ) = (T : ℝ) + (δ : ℝ)
      ring
    have hh := (NativeHeatObservation.functional_heat hδ T.property x (u₀ ω)).trans
      (congrArg (fun s : ℝ ↦ NativeHeatObservation.functional s x (u₀ ω)) hage)
    convert hh using 1 <;> rfl
  filter_upwards [hequation x,
    observation F U hU hG hβ hβ1 μ H hH hbound P e Y hm hc r hr hlocal T δ hTH hδ hTD x]
    with ω he ho hω
  calc
    _ = NativeHeatObservation.functional (T + δ) x (u₀ ω) +
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (StoppedItoInputs.stop F μ H T
            (UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H (T + δ) hTD x hbound)) ω := he hω
    _ = NativeHeatObservation.functional δ x (NativeHeatObservation.heat T (u₀ ω)) +
        NativeHeatObservation.functional δ x
          (NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hc ω⟩ (unitTime H hH T hTH)) := by
      convert (congrArg₂ (fun a b : ℝ ↦ a + b) (hmean ω) (ho hω)).symm using 1 <;> rfl
    _ = _ := by
      convert ((NativeHeatObservation.functional δ x).map_add _ _).symm using 1 <;> rfl

end SHEStochastic.GlobalLocalizedRemainderObservation
