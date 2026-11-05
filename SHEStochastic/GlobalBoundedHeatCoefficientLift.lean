module

public import SHEStochastic.UnboundedGlobalJointMoments
public import SHEStochastic.BoundedHeatCoefficientLift
public import SHEStochastic.HolderCoefficientContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.GlobalBoundedHeatCoefficientLift
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle
open HolderCoefficientIntegrability BoundedHeatCoefficientLift
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)

def input (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hT : T ≤ H) (a : HeatCircle) :
    Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H :=
  UnboundedFiniteHorizonInput.input F (field U hG hβ hβ1) (predictable F U hU hG hβ hβ1)
    (projection_holder B) (by norm_num) (by norm_num) μ H T hT a
    (Filter.Eventually.of_forall (norm_bound U hG hβ hβ1 B hb))

theorem input_ae (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hT : T ≤ H) (a : HeatCircle) :
    input F U hU hG hβ hβ1 B hb μ H T hT a =ᵐ[energyMeasure μ H]
      family F U hU hG hβ hβ1 B T a :=
  UnboundedFiniteHorizonInput.input_ae F _ _ (projection_holder B) (by norm_num) (by norm_num) μ H T hT a _

theorem input_stop (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hT : T ≤ H) (a : HeatCircle) :
    StoppedItoInputs.stop F μ H T (input F U hU hG hβ hβ1 B hb μ H T hT a) =
      input F U hU hG hβ hβ1 B hb μ H T hT a :=
  UnboundedFiniteHorizonInput.input_stop F _ _ (projection_holder B) (by norm_num) (by norm_num) μ H T hT a _

/-- A fixed moment constant depending ONLY on the coefficient bound.
The original coefficient's Lipschitz/Hölder seminorm and the solution's
L2 size do not enter this constant. -/
def momentConstant (B H : ℝ≥0) : ℝ≥0∞ :=
  (NativeScalarBDG.constant 5 : ℝ≥0∞) *
    UnboundedGlobalJointMoments.jointConstant (BallProjection.project (E := V) B)
      (universalConstant B) (1 / 2) B H ^ (2 ^ 5)

theorem momentConstant_finite (H : ℝ≥0) : momentConstant (V := V) B H < ⊤ := by
  have hc := UnboundedGlobalJointMoments.jointConstant_finite
    (BallProjection.project (E := V) B) (universalConstant B) (1 / 2) B H
  unfold momentConstant
  finiteness

theorem native_moment (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
    (p q : HeatParameterCover.Parameter) :
    (∫⁻ sample, ENNReal.ofReal (‖
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (input F U hU hG hβ hβ1 B hb μ H (GlobalHeatParameter.time H p)
          (GlobalHeatParameter.time_le_horizon H p)
          (HeatParameterCoordinates.center p)) sample -
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (input F U hU hG hβ hβ1 B hb μ H (GlobalHeatParameter.time H q)
          (GlobalHeatParameter.time_le_horizon H q)
          (HeatParameterCoordinates.center q)) sample‖ ^ 64) ∂μ) ≤
      momentConstant (V := V) B H * edist p q ^ (4 : ℝ) := by
  have hm := UnboundedGlobalJointMoments.native_moment F (field U hG hβ hβ1)
    (predictable F U hU hG hβ hβ1) (projection_holder B) (by norm_num) (by norm_num)
    μ H p q (Filter.Eventually.of_forall (norm_bound U hG hβ hβ1 B hb)) P e 5
  convert hm using 1 <;>
    norm_num [input, UnboundedGlobalJointMoments.parameterInput, momentConstant,
      UnboundedHeatIncrementCaps.exponent]

end SHEStochastic.GlobalBoundedHeatCoefficientLift
