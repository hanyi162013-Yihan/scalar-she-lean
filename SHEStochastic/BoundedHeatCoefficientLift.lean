module

public import SHEStochastic.UnboundedHeatJointMoments
public import SHEStochastic.HolderCoefficientContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.BoundedHeatCoefficientLift
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle
open HolderCoefficientIntegrability
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

def universalConstant (B : ℝ≥0) : ℝ≥0 := max (2 * B) 1

/-- A single bounded Lipschitz projection is globally half-Hölder.
Interpolation reuses mathlib's Hölder theorem and Hilbert-ball projection. -/
theorem projection_holder (B : ℝ≥0) :
    HolderWith (universalConstant B) (1 / 2) (BallProjection.project (E := V) B) := by
  have hzero : HolderWith (2 * B) 0 (BallProjection.project (E := V) B) := by
    intro x y
    simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
    rw [edist_dist, dist_eq_norm]
    have hb : ‖BallProjection.project B x - BallProjection.project B y‖ ≤ (2 * B : ℝ≥0) :=
      (norm_sub_le _ _).trans ((add_le_add (BallProjection.norm_le_radius B x)
        (BallProjection.norm_le_radius B y)).trans_eq (by push_cast; ring))
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hb
  exact hzero.of_le_of_le (BallProjection.lipschitz B).holderWith (by norm_num) (by norm_num)

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)

/-- Reuse the coefficient's actual L2 class as the new state. -/
def field (p : ℝ≥0 × Ω) : Lp V 2 (haarAddCircle (T := 2 * Real.pi)) :=
  coefficient hβ hβ1 hG (U p)

include hU in
theorem predictable : StronglyMeasurable[F.predictable] (field U hG hβ hβ1) :=
  (HolderCoefficientContinuity.continuous haarAddCircle hβ hβ1 hG).comp_stronglyMeasurable hU

include hb in
theorem norm_bound (p : ℝ≥0 × Ω) : ‖field U hG hβ hβ1 p‖ ≤ B := by
  have ha : ∀ᵐ x ∂haarAddCircle, ‖field U hG hβ hβ1 p x‖ ≤ B :=
    (coefficient_ae hβ hβ1 hG (U p)).mono fun x hx ↦ by
      change ‖coefficient hβ hβ1 hG (U p) x‖ ≤ B
      rw [hx]
      exact hb (U p x)
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound B.property ha

include hb in
/-- The auxiliary projection changes no coefficient value, so its
heat rows are precisely the original bounded coefficient heat rows. -/
theorem projection_agrees (p : ℝ≥0 × Ω) :
    (fun x ↦ BallProjection.project B (field U hG hβ hβ1 p x)) =ᵐ[haarAddCircle]
      fun x ↦ G (U p x) := by
  filter_upwards [coefficient_ae hβ hβ1 hG (U p)] with x hx
  change BallProjection.project B (coefficient hβ hβ1 hG (U p) x) = _
  rw [hx, BallProjection.of_norm_le B (hb (U p x))]

def family (T : ℝ≥0) (a : HeatCircle) :
    ℝ≥0 × Ω → Lp V 2 (haarAddCircle (T := 2 * Real.pi)) :=
  UnboundedHeatFamily.family F (field U hG hβ hβ1) (predictable F U hU hG hβ hβ1)
    (projection_holder B) (by norm_num) (by norm_num) T a

include hb in
theorem family_ae (T : ℝ≥0) (a : HeatCircle) (p : ℝ≥0 × Ω) :
    family F U hU hG hβ hβ1 B T a p =ᵐ[haarAddCircle]
      fun x ↦ RealCausalHeatKernel.value a ((T : ℝ) - p.1) x • G (U p x) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  filter_upwards [HolderStateRows.row_ae (field U hG hβ hβ1)
    (predictable F U hU hG hβ hβ1) (projection_holder B)
    (by norm_num : (0 : ℝ≥0) < 1 / 2) (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)
    (UnboundedHeatFamily.kernelFamily T a) p,
    projection_agrees U hG hβ hβ1 B hb p] with x hr hp
  exact hr.trans (congrArg (fun v ↦ RealCausalHeatKernel.value a ((T : ℝ) - p.1) x • v) hp)

def input (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hT : T ≤ H) (hT1 : (T : ℝ) ≤ 1) (a : HeatCircle) :
    Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H :=
  UnboundedHeatFamily.input F (field U hG hβ hβ1) (predictable F U hU hG hβ hβ1)
    (projection_holder B) (by norm_num) (by norm_num) μ H T hT hT1 a
    (Filter.Eventually.of_forall (norm_bound U hG hβ hβ1 B hb))

theorem input_ae (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hT : T ≤ H) (hT1 : (T : ℝ) ≤ 1) (a : HeatCircle) :
    input F U hU hG hβ hβ1 B hb μ H T hT hT1 a =ᵐ[energyMeasure μ H]
      family F U hU hG hβ hβ1 B T a :=
  UnboundedHeatFamily.input_ae F _ _ (projection_holder B) (by norm_num) (by norm_num) μ H T hT hT1 a _

theorem input_stop (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hT : T ≤ H) (hT1 : (T : ℝ) ≤ 1) (a : HeatCircle) :
    StoppedItoInputs.stop F μ H T (input F U hU hG hβ hβ1 B hb μ H T hT hT1 a) =
      input F U hU hG hβ hβ1 B hb μ H T hT hT1 a :=
  UnboundedHeatFamily.input_stop F _ _ (projection_holder B) (by norm_num) (by norm_num) μ H T hT hT1 a _

/-- A fixed moment constant depending ONLY on the coefficient bound.
The original coefficient's Lipschitz/Hölder seminorm and the solution's
L2 size do not enter this constant. -/
def momentConstant (B : ℝ≥0) : ℝ≥0∞ :=
  (NativeScalarBDG.constant 5 : ℝ≥0∞) *
    UnboundedHeatJointMoments.jointConstant (BallProjection.project (E := V) B)
      (universalConstant B) (1 / 2) B ^ (2 ^ 5)

theorem momentConstant_finite : momentConstant (V := V) B < ⊤ := by
  have hc := UnboundedHeatJointMoments.jointConstant_finite
    (BallProjection.project (E := V) B) (universalConstant B) (1 / 2) B
  unfold momentConstant
  finiteness

theorem native_moment (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
    (p q : HeatParameterCover.Parameter) :
    (∫⁻ sample, ENNReal.ofReal (‖
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (input F U hU hG hβ hβ1 B hb μ H (HeatParameterCoordinates.time H p)
          (HeatParameterCoordinates.time_le_horizon H p) (HeatParameterCoordinates.time_le_one H p)
          (HeatParameterCoordinates.center p)) sample -
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (input F U hU hG hβ hβ1 B hb μ H (HeatParameterCoordinates.time H q)
          (HeatParameterCoordinates.time_le_horizon H q) (HeatParameterCoordinates.time_le_one H q)
          (HeatParameterCoordinates.center q)) sample‖ ^ 64) ∂μ) ≤
      momentConstant (V := V) B * edist p q ^ (4 : ℝ) := by
  have hm := UnboundedHeatJointMoments.native_moment F (field U hG hβ hβ1)
    (predictable F U hU hG hβ hβ1) (projection_holder B) (by norm_num) (by norm_num)
    μ H p q (Filter.Eventually.of_forall (norm_bound U hG hβ hβ1 B hb)) P e 5
  convert hm using 1 <;>
    norm_num [input, UnboundedHeatJointMoments.parameterInput, momentConstant,
      UnboundedHeatIncrementCaps.exponent]

end SHEStochastic.BoundedHeatCoefficientLift
