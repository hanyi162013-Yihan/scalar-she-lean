module

public import SHEStochastic.MatrixObservationInput
public import SHEStochastic.NativeMatrixConvolution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixObservationIntegral
open MeasureTheory SHE SHE.FiniteHaar SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
variable (N : FiniteScalarIto.Family F μ H (d × HaarNode))
  (U : ℝ) (hU : 0 ≤ U) (Q : ℝ≥0 × Ω → Profile d) (hUpper : ∀ p, (Q p).upper ≤ U)
  (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
    (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))

/-- Spatial tests commute with the actual native vector convolution.
The right side uses the very same infinite Haar observation input. -/
theorem commutes (t : ℝ≥0) (ht : t ≤ H) (u : Physical (d := d)) :
    (innerSL ℝ u).compLpL 2 μ (NativeMatrixConvolution.value N U hU Q hUpper hQ t ht) =
      FiniteCylindricalIto.rawIntegral N.toCoordinates MatrixPredictableHaarRotation.basis
        (FiniteCylindricalIto.processTransport
          (MatrixObservationInput.input F μ H U hU Q hUpper hQ t ht u)) := by
  exact HilbertTerminalIto.commutes F μ H VectorWhiteCoordinates.basis
    (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis)
    (innerSL ℝ u) (MatrixFixedHaarInput.input F μ H U hU Q hUpper hQ t ht)

theorem observation_ae (t : ℝ≥0) (ht : t ≤ H) (u : Physical (d := d)) :
    (fun ω => inner ℝ u (NativeMatrixConvolution.value N U hU Q hUpper hQ t ht ω)) =ᵐ[μ]
      FiniteCylindricalIto.rawIntegral N.toCoordinates MatrixPredictableHaarRotation.basis
        (FiniteCylindricalIto.processTransport
          (MatrixObservationInput.input F μ H U hU Q hUpper hQ t ht u)) := by
  have hh := (innerSL ℝ u).coeFn_compLpL (NativeMatrixConvolution.value N U hU Q hUpper hQ t ht)
  rw [commutes] at hh
  exact hh.symm

end SHEStochastic.MatrixObservationIntegral
