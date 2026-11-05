module

public import SHEStochastic.UnboundedGlobalJointMoments
public import SHEStochastic.HeatParameterContinuity
public import SHEStochastic.HeatParameterInitialBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.UnboundedGlobalHeatContinuity
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle
open UnboundedGlobalJointMoments UnboundedHeatIncrementCaps HeatParameterCover
open scoped NNReal ENNReal

local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2*Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)

def observation (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) {R : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2*Real.pi)))) (p : Parameter) (ω : Ω) : ℝ :=
  (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
    (parameterInput F U hU hG hβ hβ1 μ H hbound p) ω

/-- Joint continuity of the actual native unbounded-coefficient heat
convolution on every finite horizon, including time zero. The compact
cover and native BDG/Chentsov proofs are reused unchanged. -/
theorem exists_native_continuous_modification (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2*Real.pi)))) :
    ∃ Y : Parameter → Ω → ℝ, (∀ p, Measurable (Y p)) ∧
      (∀ p, Y p=ᵐ[μ] observation F U hU hG hβ hβ1 μ H hbound P e p) ∧
      ∀ ω, Continuous (fun p ↦ Y p ω) := by
  apply HeatParameterContinuity.exists_of_dyadic_moments μ
    (observation F U hU hG hβ hβ1 μ H hbound P e)
    (fun p ↦ (Lp.stronglyMeasurable ((FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (parameterInput F U hU hG hβ hβ1 μ H hbound p))).measurable)
    (exponent β) (exponent_pos hβ1)
    (fun k ↦ (NativeScalarBDG.constant k:ℝ≥0∞)*jointConstant G C β R H^(2^k))
  · intro k
    have hc := jointConstant_finite G C β R H
    finiteness
  · exact fun k p q ↦ native_moment F U hU hG hβ hβ1 μ H p q hbound P e k

theorem observation_zero (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2*Real.pi)))) (p : Parameter)
    (hp : GlobalHeatParameter.time H p=0) : observation F U hU hG hβ hβ1 μ H hbound P e p=ᵐ[μ] 0 := by
  have hz : parameterInput F U hU hG hβ hβ1 μ H hbound p=0 :=
    UnboundedFiniteHorizonInput.input_zero F U hU hG hβ hβ1 μ H _ _ _ hbound hp
  change (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral _=ᵐ[μ] _
  rw [hz,map_zero]
  exact Lp.coeFn_zero _ _ _

/-- On a single event the full-horizon continuous convolution is
bounded on the compact parameter domain and has uniformly zero
initial trace. These properties are derived from the actual integral. -/
theorem exists_closed_version (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2*Real.pi)))) :
    ∃ Y : Parameter → Ω → ℝ, (∀ p, Measurable (Y p)) ∧
      (∀ p, Y p=ᵐ[μ] observation F U hU hG hβ hβ1 μ H hbound P e p) ∧
      (∀ ω, Continuous (fun p ↦ Y p ω)) ∧
      ∀ᵐ ω ∂μ, (∀ p, Y (HeatParameterCoordinates.zeroTime p) ω=0) ∧
        (∃ M : ℝ, 0≤M ∧ ∀ p, |Y p ω|≤M) ∧
        ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ p : Parameter, |p.val 0|<δ → |Y p ω|<ε := by
  obtain ⟨Y,hYm,hYe,hYc⟩ := exists_native_continuous_modification F U hU hG hβ hβ1 μ H hbound P e
  have hz (p : Parameter) : Y (HeatParameterCoordinates.zeroTime p)=ᵐ[μ] 0 :=
    (hYe _).trans (observation_zero F U hU hG hβ hβ1 μ H hbound P e _ (GlobalHeatParameter.zeroTime_time H p))
  refine ⟨Y,hYm,hYe,hYc,?_⟩
  filter_upwards [HeatParameterInitialBound.simultaneous_zero μ Y hYc hz] with ω hω
  exact ⟨hω,HeatParameterInitialBound.bounded (fun p ↦ Y p ω) (hYc ω),
    fun _ hε ↦ HeatParameterInitialBound.uniformly_small (fun p ↦ Y p ω) (hYc ω) hω hε⟩

end SHEStochastic.UnboundedGlobalHeatContinuity
