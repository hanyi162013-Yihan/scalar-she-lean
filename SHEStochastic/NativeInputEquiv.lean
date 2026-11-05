module

public import SHEStochastic.NativeRowRepresentatives

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeInputEquiv
open MeasureTheory SHE SHE.PredictableL2
open scoped ENNReal NNReal

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

/-- Inverse of the existing identity transport between the two equal
predictable L2 input measures. No representatives or integrals change. -/
def inverse : Lp C 2 (FiniteScalarIto.inputMeasure F μ H) →ₗᵢ[ℝ] Process (E := C) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact Lp.compMeasurePreservingₗᵢ ℝ id
    ⟨measurable_id, by
      rw [Measure.map_id]
      exact FilteredScalarIto.processMeasure_eq (𝓖 := F) (μ := μ) H
        (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)⟩

theorem inverse_ae (u : Lp C 2 (FiniteScalarIto.inputMeasure F μ H)) :
    inverse F μ H u =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)] u := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact Lp.coeFn_compMeasurePreserving _ _

theorem transport_inverse (u : Lp C 2 (FiniteScalarIto.inputMeasure F μ H)) :
    FiniteCylindricalIto.processTransport (inverse F μ H u) = u := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.ext
  have hi := inverse_ae F μ H u
  have hle : ae (FiniteScalarIto.inputMeasure F μ H) ≤
      ae ((energyMeasure μ H).trim (predictable_le_product F)) := by
    rw [NativeRowRepresentatives.inputMeasure_eq]
  exact (FiniteCylindricalIto.processTransport_ae _).trans (hi.filter_mono hle)

theorem inverse_transport (u : Process (E := C) F μ H) :
    inverse F μ H (FiniteCylindricalIto.processTransport u) = u := by
  apply (FiniteCylindricalIto.processTransport (F := F) (μ := μ) (H := H)).injective
  exact transport_inverse F μ H _

end SHEStochastic.NativeInputEquiv
