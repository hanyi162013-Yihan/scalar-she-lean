module

public import SHEStochastic.MatrixSquareParameterAction
public import SHEStochastic.MatrixObservationIntegral
public import SHEStochastic.HilbertLpObservations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeMatrixCoefficient
open MeasureTheory SHE SHE.FiniteHaar SHE.PredictableL2 MatrixInfiniteHaar MatrixSquareCoefficient
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (U : ℝ) (hU : 0 ≤ U) (Q : ℝ≥0 × Ω → Profile d) (hUpper : ∀ p, (Q p).upper ≤ U)
  (A : ∀ p, Data (Q p))
  (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
    (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))
  (hA : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
    (F.predictable.prod inferInstance) inferInstance (fun z => (A z.1).value z.2))

def isometry (p : ℝ≥0 × Ω) : Input (d := d) →ₗᵢ[ℝ] Input (d := d) :=
  (A p).rotation.symm.toLinearIsometry

include hQ hA in
theorem measurable :
    @Measurable ((ℝ≥0 × Ω) × Input (d := d)) (Input (d := d))
      (F.predictable.prod (borel _)) (borel _) (fun z => isometry Q A z.1 z.2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hQ' : Measurable (fun z : ((ℝ≥0 × Ω) × Input (d := d)) × AddCircle (1 : ℝ) => (Q z.1.1).value z.2) :=
    hQ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hA' : Measurable (fun z : ((ℝ≥0 × Ω) × Input (d := d)) × AddCircle (1 : ℝ) => (A z.1.1).value z.2) :=
    hA.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  exact MatrixSquareParameterAction.inverse (fun z : (ℝ≥0 × Ω) × Input (d := d) => Q z.1)
    (fun z => A z.1) hQ' hA' Prod.snd measurable_snd

/-- The actual square-coefficient observation input is constructed by
the already proved predictable unitary isometry. Its next theorem identifies
its representative with the literal `G* heat* u` row. -/
def input (t : ℝ≥0) (ht : t ≤ H) (u : Physical (d := d)) : Process (E := Input (d := d)) F μ H :=
  PredictableItoRotation.processIsometry F μ H (isometry Q A) (measurable F Q A hQ hA)
    (MatrixObservationInput.input F μ H U hU Q hUpper hQ t ht u)

def row (τ : ℝ) (p : ℝ≥0 × Ω) (u : Physical (d := d)) : Input (d := d) :=
  if 0 < τ then (A p).factor.adjoint ((VectorHeat.heat τ).adjoint u) else 0

theorem input_ae (t : ℝ≥0) (ht : t ≤ H) (u : Physical (d := d)) :
    input F μ H U hU Q hUpper A hQ hA t ht u =ᵐ[energyMeasure μ H]
      (fun p : ℝ≥0 × Ω => row Q A ((t : ℝ)-(p.1 : ℝ)) p u) := by
  filter_upwards [PredictableItoRotation.processIsometry_ae F μ H (isometry Q A) (measurable F Q A hQ hA)
    (MatrixObservationInput.input F μ H U hU Q hUpper hQ t ht u),
    MatrixObservationInput.input_ae F μ H U hU Q hUpper hQ t ht u] with p hp hrow
  change PredictableItoRotation.processIsometry F μ H (isometry Q A) (measurable F Q A hQ hA)
    (MatrixObservationInput.input F μ H U hU Q hUpper hQ t ht u) p = _
  rw [hp, hrow]
  by_cases ht' : 0 < (t : ℝ)-(p.1 : ℝ)
  · simp only [MatrixCausalHeatRows.row, row, if_pos ht']
    exact (A p).reconstruct_adjoint _
  · simp only [MatrixCausalHeatRows.row, row, if_neg ht', map_zero]

/-- A concrete square diffusion with covariance `GG*` can be replaced
by the completed infinite Haar factor on the original space and filtration.
The equality holds for every actual native scalar spatial observation. -/
theorem exists_haar_family (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ B : FiniteScalarIto.Family F μ H (d × HaarNode), ∀ t ht u,
      (innerSL ℝ u).compLpL 2 μ (NativeMatrixConvolution.value B U hU Q hUpper hQ t ht) =
        (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
          (input F μ H U hU Q hUpper A hQ hA t ht u) := by
  obtain ⟨B, hB⟩ := NativePredictableRotation.exists_family N MatrixPredictableHaarRotation.basis
    MatrixPredictableHaarRotation.basis (isometry Q A) (measurable F Q A hQ hA) hnull
  refine ⟨B, fun t ht u => ?_⟩
  rw [MatrixObservationIntegral.commutes]
  exact hB _

/-- Consequently a vector random variable satisfying the literal square
coefficient mild observation equation has the same Haar realization. -/
theorem replace (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (Z : (t : ℝ≥0) → t ≤ H → Lp (Physical (d := d)) 2 μ)
    (hZ : ∀ t ht u, (innerSL ℝ u).compLpL 2 μ (Z t ht) =
      (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
        (input F μ H U hU Q hUpper A hQ hA t ht u)) :
    ∃ B : FiniteScalarIto.Family F μ H (d × HaarNode), ∀ t ht,
      Z t ht = NativeMatrixConvolution.value B U hU Q hUpper hQ t ht := by
  obtain ⟨B, hB⟩ := exists_haar_family F μ H U hU Q hUpper A hQ hA N hnull
  refine ⟨B, fun t ht => ?_⟩
  apply HilbertLpObservations.ext μ VectorWhiteCoordinates.basis
  intro k
  rw [hZ, hB]

end SHEStochastic.NativeMatrixCoefficient
