module

public import SHEStochastic.MatrixHaarRotationInverse
public import SHEStochastic.NativePredictableRotation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixPredictableHaarRotation
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator

variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩

def basis : HilbertBasis (d × FiniteHaar.HaarNode) ℝ (Input (d := d)) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)

def isometry (Q : ℝ≥0 × Ω → Profile d) (p : ℝ≥0 × Ω) :
    Input (d := d) →ₗᵢ[ℝ] Input (d := d) :=
  (MatrixHaarNoiseRotation.rotation (Q p)).symm.toLinearIsometry

/-- The inverse infinite Haar innovation rotation is jointly
predictable in its actual noise input whenever the covariance field
is jointly predictable in time, probability and space. -/
theorem measurable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} (Q : ℝ≥0 × Ω → Profile d)
    (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2)) :
    @Measurable ((ℝ≥0 × Ω) × Input (d := d)) (Input (d := d))
      (F.predictable.prod (borel (Input (d := d)))) (borel (Input (d := d)))
      (fun p => isometry Q p.1 p.2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hK : Measurable (fun z : ((ℝ≥0 × Ω) × Input (d := d)) × AddCircle (1 : ℝ) =>
      (Q z.1.1).value z.2) :=
    hQ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  exact MatrixHaarRotationInverse.measurable (fun p : (ℝ≥0 × Ω) × Input (d := d) => Q p.1)
    hK Prod.snd measurable_snd

/-- Reuse the native predictable-rotation construction for the actual
infinite matrix Haar unitary. The resulting Brownian family carries
the native integral on every predictable `ℓ²` process. -/
def exists_family {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {H : ℝ≥0}
    (P : FiniteScalarIto.Family F μ H (d × FiniteHaar.HaarNode))
    (Q : ℝ≥0 × Ω → Profile d)
    (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))
    (hNull : NullCompleteFiltration.ContainsNullSets F μ) :=
  NativePredictableRotation.exists_family (A := Input (d := d)) (C := Input (d := d))
    (F := F) (μ := μ) (H := H) P (basis (d := d)) (basis (d := d))
    (isometry Q) (measurable (F := F) Q hQ) hNull

end SHEStochastic.MatrixPredictableHaarRotation
