module

public import SHEStochastic.MatrixContinuousMild
public import SHEStochastic.RandomVectorHeatInitialProcess
public import SHEStochastic.MatrixTimeMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixRandomMildExistence
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℝ≥0} (G : MatrixNonlinearCoefficient.Coefficient d)

/-- Native matrix mild equation with the original random L2 initial state. -/
def Equation (hH : (H : ℝ) ≤ 1) (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (U : ℝ≥0 × Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)
    (Z : Ω → Physical (d := d)) : Prop := ∀ t (ht : t ≤ H),
  (fun ω => U (t,ω)) =ᵐ[μ] fun ω => VectorAnalyticHeat.heat t (Z ω)+
    MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
      (MatrixContinuousMild.field G U hU).value (MatrixContinuousMild.field G U hU).upper
        (MatrixContinuousMild.field G U hU).measurable N t ht ω

/-- Lipschitz matrix approximations admit continuous predictable solutions
for square-integrable time-zero states, on the same space and native noise.
The shared forced Picard proof supplies the complete stochastic equation. -/
theorem exists_solution (hH : (H : ℝ) ≤ 1) (hH0 : 0 < H)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (N : FiniteScalarIto.Family F μ H (d × HaarNode)) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ z w, ‖G.value z-G.value w‖ ≤ L*‖z-w‖)
    (Z : Ω → Physical (d := d)) (hZ₀ : StronglyMeasurable[F 0] Z) (hZ : MemLp Z 2 μ) :
    ∃ (U : ℝ≥0 × Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U),
      (∀ ω, Continuous (fun t => U (t,ω))) ∧ Equation G hH N U hU Z :=
  MatrixContinuousMild.exists_forced G hH hH0 hnull N hL hLip
    (RandomVectorHeatInitialProcess.function Z) (RandomVectorHeatInitialProcess.predictable F Z hZ₀)
    (RandomVectorHeatInitialProcess.continuous_paths Z)
    (RandomVectorHeatInitialProcess.process F μ H Z hZ₀ hZ)
    (RandomVectorHeatInitialProcess.process_ae F μ H Z hZ₀ hZ)

variable (hH : (H : ℝ) ≤ 1) (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (U : ℝ≥0 × Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)
    (Z : Ω → Physical (d := d))

/-- Every actual mild solution has this common increment bound after
subtracting the random heat initial state. No Lipschitz or higher derivative
constant occurs, so the estimate is uniform under smooth approximation. -/
theorem stochastic_increment_moment16 (he : Equation G hH N U hU Z)
    (s t : ℝ≥0) (hsH : s ≤ H) (htH : t ≤ H) :
    (∫⁻ ω, ENNReal.ofReal
      (‖(U (s,ω)-VectorAnalyticHeat.heat s (Z ω))-(U (t,ω)-VectorAnalyticHeat.heat t (Z ω))‖^16) ∂μ) ≤
      ENNReal.ofReal (MatrixTimeMoments.momentConstant d (NativeMatrixEquation.cap G)*((s : ℝ)-(t : ℝ))^2) := by
  let a := MatrixContinuousMild.field G U hU
  have hident : ∀ᵐ ω ∂μ,
      (U (s,ω)-VectorAnalyticHeat.heat s (Z ω))-(U (t,ω)-VectorAnalyticHeat.heat t (Z ω)) =
        MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
          a.value a.upper a.measurable N s hsH ω-
        MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
          a.value a.upper a.measurable N t htH ω := by
    filter_upwards [he s hsH,he t htH] with ω hs ht
    rw [hs,ht]
    abel
  calc
    _ = ∫⁻ ω, ENNReal.ofReal
        (‖MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
            a.value a.upper a.measurable N s hsH ω-
          MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
            a.value a.upper a.measurable N t htH ω‖^16) ∂μ :=
      lintegral_congr_ae (hident.mono fun _ h => congrArg (fun z => ENNReal.ofReal (‖z‖^16)) h)
    _ ≤ _ := MatrixTimeMoments.symmetric_increment_moment16 hH (NativeMatrixEquation.cap_nonneg G) a N s t hsH htH


end SHEStochastic.MatrixRandomMildExistence
