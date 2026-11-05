module

public import SHEStochastic.FiniteCylindricalIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.FiniteScalarIto
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : Coordinates F μ H ι)

def oneStep (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H t : ℝ≥0) (ht : t ≤ H) : Simple F H :=
  FilteredItoCLM.iocSP_T (𝓖 := F) (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)
    (show (0 : ℝ≥0) ≤ t from zero_le) ht (MeasurableSet.univ : MeasurableSet[F 0] (Set.univ : Set Ω))

theorem zero_ae (i : ι) : P.W i 0 =ᵐ[μ] fun _ ↦ 0 := by
  have hl := BrownianCoordinates.eval_law F μ H P.W P.law i 0 zero_le
  rw [gaussianReal_zero_var] at hl
  exact hl.ae_eq_of_dirac

theorem simpleValue_oneStep (i : ι) (t : ℝ≥0) (ht : t ≤ H) :
    simpleValue P i (oneStep F H t ht) = fun ω ↦ P.W i t ω - P.W i 0 ω := by
  let V := oneStep F H t ht
  have he := FilteredItoProcess.itoSimpleProcess_eq_itoSimple (measurable_coordinate P i)
    V.val V.property
  funext ω
  change FilteredItoL2.itoSimple (measurable_coordinate P i) V.val ω = _
  rw [← he]
  change ((ElementaryPredictableSet.IocProd 0 t
    (MeasurableSet.univ : MeasurableSet[F 0] (Set.univ : Set Ω))).indicator (1 : ℝ)).integral
      (ContinuousLinearMap.mul ℝ ℝ) (P.W i) H ω = _
  rw [ElementaryPredictableSet.integral_indicator_apply]
  simp [ElementaryPredictableSet.IocProd, stoppedProcess]
  change P.W i (min t H) ω = P.W i t ω
  rw [min_eq_left ht]

/-- The finite-horizon scalar integral is anchored to the actual given
coordinate, rather than an unspecified isometry with the same norm. -/
theorem rawIsometry_oneStep (i : ι) (t : ℝ≥0) (ht : t ≤ H) :
    rawIsometry P i (embedding F μ H (oneStep F H t ht)) =ᵐ[μ] P.W i t := by
  rw [rawIsometry_simple]
  filter_upwards [(memLp_simpleValue P i (oneStep F H t ht)).coeFn_toLp, zero_ae P i] with ω hv hz
  change simpleLp P i (oneStep F H t ht) ω = _
  change simpleLp P i (oneStep F H t ht) ω = simpleValue P i (oneStep F H t ht) ω at hv
  rw [hv, simpleValue_oneStep]
  change P.W i t ω - P.W i 0 ω = P.W i t ω
  rw [hz, sub_zero]

end SHEStochastic.FiniteScalarIto

namespace SHEStochastic.FiniteCylindricalIto
open MeasureTheory
open scoped NNReal ENNReal
variable {Ω ι C : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Coordinates F μ H ι) (e : HilbertBasis ι ℝ C)

theorem rawIntegral_oneStep (i : ι) (t : ℝ≥0) (ht : t ≤ H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    rawIntegral P e
      (L2HilbertSum.lift (FiniteScalarIto.inputMeasure F μ H) (ColumnsHilbertSum.unit e i)
        (FiniteScalarIto.embedding F μ H (FiniteScalarIto.oneStep F H t ht))) =ᵐ[μ] P.W i t := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  rw [rawIntegral_unit]
  exact FiniteScalarIto.rawIsometry_oneStep P i t ht

end SHEStochastic.FiniteCylindricalIto
