module

public import SHEStochastic.GlobalLocalizedRemainderObservation
public import SHEStochastic.GlobalNativeFourierRemainder

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.GlobalLocalizedFourierRemainder
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter Set
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback UnboundedGlobalJointMoments
open GlobalHeatRowPhysicalIntegration
open scoped NNReal ENNReal

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0×Ω → Lp E 2 (haarAddCircle (T := 2*Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G)
  (hβ : 0<β) (hβ1 : β<1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) (hH : 0<H)
  {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R)
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2*Real.pi))))

/-- A locally pasted continuous heat field has the SAME Fourier Ito
coordinates as its bounded predictable input before the prescribed exit. -/
theorem coordinate
    (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ ω, Continuous (fun p => Y p ω))
    (r : Ω → WithTop ℝ≥0) (hr : IsStoppingTime F r)
    (hlocal : ∀ p, ∀ᵐ ω ∂μ,
      (GlobalHeatParameter.time H p : WithTop ℝ≥0)<r ω →
      Y p ω = UnboundedGlobalHeatContinuity.observation F U hU hG hβ hβ1 μ H
        hbound P e p ω)
    (T : ℝ≥0) (hTH : T≤H) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0)<r ω →
      NativeFourierHeatCoordinate.coordinate a m
        (NativeRemainderObservation.remainder
          ⟨fun p => Y p ω, hc ω⟩ (unitTime H hH T hTH)) =
        Real.exp (-(T : ℝ)*(m : ℝ)^2)*
          (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
            (StoppedItoInputs.stop F μ H T
              (FourierHeatInput.growingInput F U hU hG hβ hβ1 μ H hbound a m)) ω := by
  obtain ⟨Z,hZm,hZe,hZc⟩ :=
    UnboundedGlobalHeatContinuity.exists_native_continuous_modification
      F U hU hG hβ hβ1 μ H hbound P e
  let t : ShortTime := unitTime H hH T hTH
  let A : Set Ω := {ω | (T : WithTop ℝ≥0)<r ω}
  have hA : MeasurableSet A := by
    simpa only [A,compl_setOf,not_le] using ((F.le T) _ (hr T)).compl
  have heq (x : HeatCircle) : ∀ᵐ ω ∂μ, ω∈A → Y (point t x) ω=Z (point t x) ω := by
    filter_upwards [hlocal (point t x),hZe (point t x)] with ω hy hz hω
    have ht : GlobalHeatParameter.time H (point t x)=T :=
      NNReal.eq (GlobalHeatParameter.time_point H hH ⟨T,T.property,hTH⟩ x)
    have hx : (GlobalHeatParameter.time H (point t x) : WithTop ℝ≥0)<r ω := by
      rw [ht]
      exact hω
    exact (hy hx).trans hz.symm
  have hfield := PhysicalConditionalFieldEquality.ae_eq μ Y Z hm hc hZm hZc t A hA heq
  have hfourier := GlobalNativeFourierRemainder.coordinate F U hU hG hβ hβ1 μ H
    hH hbound (FiniteCylindricalIto.terminalIto P.toCoordinates e) a m T hTH Z hZm hZc hZe
  filter_upwards [hfield,hfourier] with ω hf hfo hω
  have he := congrArg NativePhysicalState.pull (hf hω)
  exact (congrArg (NativeFourierHeatCoordinate.coordinate a m) he).trans hfo

end SHEStochastic.GlobalLocalizedFourierRemainder
