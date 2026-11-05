module

public import SHEStochastic.UnboundedHeatJointMoments
public import SHEStochastic.HeatParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.UnboundedHeatContinuity
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle
open UnboundedHeatJointMoments UnboundedHeatIncrementCaps HeatParameterCover
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

def observation (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) {R : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
    (p : Parameter) (ω : Ω) : ℝ :=
  (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
    (parameterInput F U hU hG hβ hβ1 μ H hbound p) ω

/-- Joint continuity, including time zero, is proved for the actual
native convolution of any predictable spatial-L²-bounded state. The
moment order is chosen from β, rather than restricting β artificially. -/
theorem exists_native_continuous_modification (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) :
    ∃ Y : Parameter → Ω → ℝ, (∀ p, Measurable (Y p)) ∧
      (∀ p, Y p =ᵐ[μ] observation F U hU hG hβ hβ1 μ H hbound P e p) ∧
        ∀ ω, Continuous (fun p ↦ Y p ω) := by
  apply HeatParameterContinuity.exists_of_dyadic_moments μ
    (observation F U hU hG hβ hβ1 μ H hbound P e)
    (fun p ↦ (Lp.stronglyMeasurable ((FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (parameterInput F U hU hG hβ hβ1 μ H hbound p))).measurable)
    (exponent β) (exponent_pos hβ1)
    (fun k ↦ (NativeScalarBDG.constant k:ℝ≥0∞)*jointConstant G C β R^(2^k))
  · intro k
    have hc := jointConstant_finite G C β R
    finiteness
  · exact fun k p q ↦ native_moment F U hU hG hβ hβ1 μ H p q hbound P e k

end SHEStochastic.UnboundedHeatContinuity
