module

public import SHEStochastic.NativeMatrixCoefficient
public import SHEStochastic.NativeInputPairing

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.NativeMatrixSquareRealization
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixSquareCoefficient
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (Q : ℝ≥0 × Ω → Profile d) (A : ∀ p, Data (Q p))
  (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
    (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))
  (hA : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
    (F.predictable.prod inferInstance) inferInstance (fun z => (A z.1).value z.2))

def forward (p : ℝ≥0 × Ω) : Input (d := d) →ₗᵢ[ℝ] Input (d := d) := (A p).rotation.toLinearIsometry

include hQ hA in
theorem measurable :
    @Measurable ((ℝ≥0 × Ω) × Input (d := d)) (Input (d := d))
      (F.predictable.prod (borel _)) (borel _) (fun z => forward Q A z.1 z.2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hQ' : Measurable (fun z : ((ℝ≥0 × Ω) × Input (d := d)) × AddCircle (1 : ℝ) => (Q z.1.1).value z.2) :=
    hQ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hA' : Measurable (fun z : ((ℝ≥0 × Ω) × Input (d := d)) × AddCircle (1 : ℝ) => (A z.1.1).value z.2) :=
    hA.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  exact MatrixSquareParameterAction.rotation (fun z : (ℝ≥0 × Ω) × Input (d := d) => Q z.1)
    (fun z => A z.1) hQ' hA' Prod.snd measurable_snd

include hQ hA in
/-- The same reverse rotation transports every predictable L2 row, so
it also applies to analytic-clock and stopped future-target inputs. -/
theorem exists_transport (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ B : FiniteScalarIto.Family F μ H (d × HaarNode), ∀ v : Process (E := Input (d := d)) F μ H,
      (FiniteCylindricalIto.terminalIto B.toCoordinates MatrixPredictableHaarRotation.basis).integral
        (PredictableItoRotation.processIsometry F μ H (NativeMatrixCoefficient.isometry Q A)
          (NativeMatrixCoefficient.measurable F Q A hQ hA) v) =
      (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral v := by
  obtain ⟨B,hB⟩ := NativePredictableRotation.exists_family N MatrixPredictableHaarRotation.basis
    MatrixPredictableHaarRotation.basis (forward Q A) (measurable F Q A hQ hA) hnull
  refine ⟨B,fun v => ?_⟩
  rw [hB]
  apply congrArg (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
  apply NativeInputPairing.process_ext
  filter_upwards [PredictableItoRotation.processIsometry_ae F μ H (forward Q A) (measurable F Q A hQ hA)
    (PredictableItoRotation.processIsometry F μ H (NativeMatrixCoefficient.isometry Q A)
      (NativeMatrixCoefficient.measurable F Q A hQ hA) v),
    PredictableItoRotation.processIsometry_ae F μ H (NativeMatrixCoefficient.isometry Q A)
      (NativeMatrixCoefficient.measurable F Q A hQ hA) v] with p hp hi
  rw [hp,hi]
  exact (A p).rotation.apply_symm_apply _

include hQ hA in
/-- A solution constructed with covariance-adapted Haar noise has a
realization with the literal original square diffusion, on the same space.
The reverse predictable unitary is used for every observation at once. -/
theorem exists_family (U : ℝ) (hU : 0 ≤ U) (hUpper : ∀ p, (Q p).upper ≤ U)
    (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ B : FiniteScalarIto.Family F μ H (d × HaarNode), ∀ t ht u,
      (FiniteCylindricalIto.terminalIto B.toCoordinates MatrixPredictableHaarRotation.basis).integral
        (NativeMatrixCoefficient.input F μ H U hU Q hUpper A hQ hA t ht u) =
      (innerSL ℝ u).compLpL 2 μ (NativeMatrixConvolution.value N U hU Q hUpper hQ t ht) := by
  obtain ⟨B,hB⟩ := exists_transport F μ H Q A hQ hA N hnull
  refine ⟨B,fun t ht u => ?_⟩
  rw [MatrixObservationIntegral.commutes]
  exact hB (MatrixObservationInput.input F μ H U hU Q hUpper hQ t ht u)

end SHEStochastic.NativeMatrixSquareRealization
