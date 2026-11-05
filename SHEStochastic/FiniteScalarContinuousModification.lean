module

public import SHEStochastic.FiniteScalarTerminalIto
public import SHEStochastic.ContinuousMartingaleExtension
public import SHEStochastic.FilteredItoContinuousModification

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.FiniteScalarItoProcess
open MeasureTheory ProbabilityTheory FiniteScalarIto
open scoped NNReal ENNReal
variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : Family F μ H ι)

def continuousModel (i : ι) : ContinuousMartingaleExtension.Model
    (Lp ℝ 2 (inputMeasure F μ H)) (Simple F H) F μ H where
  embedding := embedding F μ H
  dense := embedding_dense F μ H
  process :=
    { toFun := simpleProcess P.toCoordinates i
      map_add' := fun V U ↦ by
        funext t ω
        exact congrFun (FilteredItoProcess.itoSimpleProcess_add
          (clipped_measurable P.toCoordinates i) V.val U.val t) ω
      map_smul' := fun c V ↦ by
        funext t ω
        exact congrFun (FilteredItoProcess.itoSimpleProcess_smul
          (clipped_measurable P.toCoordinates i) c V.val t) ω }
  martingale := simple_martingale P.toCoordinates i
  continuous := fun V ω ↦ FilteredItoProcess.itoSimpleProcess_pathContinuous
    (clipped_measurable P.toCoordinates i) (clipped_continuous P i) V.val ω
  atTime := prefixCLM P.toCoordinates i
  representative V t := by rw [prefixCLM_simple]; exact simpleLp_ae P.toCoordinates i V t
  terminal_bound V := by rw [prefixCLM_simple, simpleLp_terminal, simpleLp_norm]

theorem exists_continuous_modification (i : ι) (v : Lp ℝ 2 (inputMeasure F μ H)) :
    ∃ X : ℝ≥0 → Ω → ℝ, (∀ t, t ≤ H → X t =ᵐ[μ] prefixCLM P.toCoordinates i t v) ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Set.Icc 0 H)) :=
  (continuousModel P i).exists_continuous_modification v

end SHEStochastic.FiniteScalarItoProcess
