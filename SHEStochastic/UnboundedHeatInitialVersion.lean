module

public import SHEStochastic.UnboundedHeatContinuity
public import SHEStochastic.HeatParameterInitialBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.UnboundedHeatInitialVersion
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle
open UnboundedHeatFamily HeatParameterCover HeatParameterCoordinates UnboundedHeatContinuity
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)

theorem family_zero (a : HeatCircle) : family F U hU hG hβ hβ1 0 a = 0 := by
  funext p
  apply norm_eq_zero.mp
  have he : ENNReal.ofReal (‖family F U hU hG hβ hβ1 0 a p‖ ^ 2) = 0 := by
    rw [energy]
    apply dif_neg
    simp only [NNReal.coe_zero, zero_sub, not_lt, neg_nonpos]
    convert p.1.property using 1 <;> rfl
  have hs := ENNReal.ofReal_eq_zero.mp he
  nlinarith [norm_nonneg (family F U hU hG hβ hβ1 0 a p)]

theorem input_zero (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (a : HeatCircle) {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R) :
    input F U hU hG hβ hβ1 μ H 0 (by positivity) (by norm_num) a hbound = 0 := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let ν := (energyMeasure μ H).trim (predictable_le_product F)
  have hz : MemLp (0 : ℝ≥0 × Ω → Lp V 2 (haarAddCircle (T := 2 * Real.pi))) 2 ν := MemLp.zero
  exact (MemLp.toLp_congr (memLp F U hU hG hβ hβ1 μ H 0 (by positivity) (by norm_num) a hbound)
    hz (Filter.Eventually.of_forall fun p ↦ congrFun (family_zero F U hU hG hβ hβ1 a) p)).trans
      (MemLp.toLp_zero hz)

/-- The native convolution has zero initial trace, without making any
uniform-continuity assumption on the initial data itself. -/
theorem observation_zero (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
    (p : Parameter) (hp : time H p = 0) :
    observation F U hU hG hβ hβ1 μ H hbound P e p =ᵐ[μ] 0 := by
  have hi : UnboundedHeatJointMoments.parameterInput F U hU hG hβ hβ1 μ H hbound p = 0 := by
    dsimp [UnboundedHeatJointMoments.parameterInput]
    simpa only [hp] using input_zero F U hU hG hβ hβ1 μ H (center p) hbound
  change (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral _ =ᵐ[μ] _
  rw [hi, map_zero]
  exact Lp.coeFn_zero _ _ _

/-- Actual native stochastic convolution: a continuous modification with
an almost-sure finite compact bound and a uniformly vanishing initial
trace. All three properties are derived from spatial L² localization. -/
theorem exists_uniformly_vanishing_version (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) :
    ∃ Y : Parameter → Ω → ℝ, (∀ p, Measurable (Y p)) ∧
      (∀ p, Y p =ᵐ[μ] observation F U hU hG hβ hβ1 μ H hbound P e p) ∧
      (∀ ω, Continuous (fun p ↦ Y p ω)) ∧
      ∀ᵐ ω ∂μ, (∀ p, Y (zeroTime p) ω = 0) ∧
        (∃ M : ℝ, 0 ≤ M ∧ ∀ p, |Y p ω| ≤ M) ∧
          ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
            ∀ p : Parameter, |p.val 0| < δ → |Y p ω| < ε := by
  obtain ⟨Y, hYm, hYe, hYc⟩ := exists_native_continuous_modification F U hU hG hβ hβ1 μ H hbound P e
  have hz (p : Parameter) : Y (zeroTime p) =ᵐ[μ] 0 :=
    (hYe (zeroTime p)).trans (observation_zero F U hU hG hβ hβ1 μ H hbound P e
      (zeroTime p) (zeroTime_time H p))
  refine ⟨Y, hYm, hYe, hYc, ?_⟩
  filter_upwards [HeatParameterInitialBound.simultaneous_zero μ Y hYc hz] with ω hω
  exact ⟨hω, HeatParameterInitialBound.bounded (fun p ↦ Y p ω) (hYc ω),
    fun _ hε ↦ HeatParameterInitialBound.uniformly_small (fun p ↦ Y p ω) (hYc ω) hω hε⟩

end SHEStochastic.UnboundedHeatInitialVersion
