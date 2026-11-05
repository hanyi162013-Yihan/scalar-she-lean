module

public import SHEStochastic.MatrixCausalHeatRows
public import SHEStochastic.NativeRowRepresentatives

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixObservationInput
open MeasureTheory SHE SHE.FiniteHaar SHE.PredictableL2 MatrixInfiniteHaar MatrixCausalHeatRows
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (U : ℝ) (hU : 0 ≤ U) (Q : ℝ≥0 × Ω → Profile d)
    (hUpper : ∀ p, (Q p).upper ≤ U)
    (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))
local notation "ν" => ((energyMeasure μ H).trim (predictable_le_product F))

/-- Actual predictable Hilbert input for a vector spatial observation,
obtained by applying its bounded linear test to the native HS kernel. -/
def input (t : ℝ≥0) (ht : t ≤ H) (u : Physical (d := d)) : Process (E := Input (d := d)) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (HilbertColumns.mapCLM (innerSL ℝ u)).compLpL 2 ν
    (MatrixFixedHaarInput.input F μ H U hU Q hUpper hQ t ht)

theorem input_ae (t : ℝ≥0) (ht : t ≤ H) (u : Physical (d := d)) :
    input F μ H U hU Q hUpper hQ t ht u =ᵐ[energyMeasure μ H]
      (fun p : ℝ≥0 × Ω => row ((t : ℝ)-(p.1 : ℝ)) (Q p) u) := by
  have hh := ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM (innerSL ℝ u)).coeFn_compLpL
    (MatrixFixedHaarInput.input F μ H U hU Q hUpper hQ t ht))
  filter_upwards [hh, MatrixFixedHaarInput.input_ae F μ H U hU Q hUpper hQ t ht] with p hp hq
  change ((HilbertColumns.mapCLM (innerSL ℝ u)).compLpL 2 ν
    (MatrixFixedHaarInput.input F μ H U hU Q hUpper hQ t ht)) p = _
  rw [hp, hq, mapped_kernel]

include hQ in
theorem predictable (t : ℝ≥0) (u : Physical (d := d)) :
    StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => row ((t : ℝ)-(p.1 : ℝ)) (Q p) u) := by
  have hh := (HilbertColumns.mapCLM (innerSL ℝ u)).continuous.comp_stronglyMeasurable
    (MatrixHaarKernel.predictable F Q hQ t)
  simpa only [mapped_kernel] using hh

theorem native_ae (t : ℝ≥0) (ht : t ≤ H) (u : Physical (d := d)) :
    FiniteCylindricalIto.processTransport (input F μ H U hU Q hUpper hQ t ht u) =ᵐ[FiniteScalarIto.inputMeasure F μ H]
      (fun p : ℝ≥0 × Ω => row ((t : ℝ)-(p.1 : ℝ)) (Q p) u) :=
  NativeRowRepresentatives.transport_ae _ _ (predictable F Q hQ t u) (input_ae F μ H U hU Q hUpper hQ t ht u)

end SHEStochastic.MatrixObservationInput
