module

public import SHEStochastic.MatrixHaarHeatRows
public import SHEStochastic.MatrixFixedHaarInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixCausalHeatRows
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Scalar observation rows of the actual causal vector convolution.
The zero extension includes nonpositive heat ages. -/
def row (t : ℝ) (P : Profile d) (u : Physical (d := d)) : Input (d := d) :=
  if 0 < t then MatrixHaarHeatRows.row t P u else 0

theorem mapped_kernel (t : ℝ) (P : Profile d) (u : Physical (d := d)) :
    HilbertColumns.mapCLM (innerSL ℝ u) (MatrixHaarKernel.kernel t P) = row t P u := by
  by_cases ht : 0 < t
  · apply lp.ext
    funext k
    rw [HilbertColumns.mapCLM_apply]
    simp only [row, if_pos ht]
    rw [MatrixHaarHeatRows.coordinate ht]
    exact (real_inner_comm u (MatrixHaarKernel.kernel t P k)).symm
  · rw [MatrixFixedHaarInput.kernel_zero (not_lt.mp ht), map_zero, row, if_neg ht]

theorem cross_pairing (s t : ℝ) (P : Profile d) (u v : Physical (d := d)) :
    inner ℝ (row s P u) (row t P v) = if 0 < s ∧ 0 < t then
      inner ℝ u (VectorHeat.heat s (multiplier P ((VectorHeat.heat t).adjoint v))) else 0 := by
  by_cases hs : 0 < s <;> by_cases ht : 0 < t
  · simp only [row, if_pos hs, if_pos ht, if_pos (And.intro hs ht)]
    unfold MatrixHaarHeatRows.row
    rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, covariance,
      ContinuousLinearMap.adjoint_inner_left]
  · simp [row, hs, ht]
  · simp [row, hs, ht]
  · simp [row, hs, ht]

theorem measurable {Z : Type*} [MeasurableSpace Z] (τ : Z → ℝ) (hτ : Measurable τ)
    (Q : Z → Profile d)
    (hQ : Measurable (fun z : Z × AddCircle (1 : ℝ) => (Q z.1).value z.2))
    (u : Physical (d := d)) :
    @Measurable Z (Input (d := d)) _ (borel _) (fun z => row (τ z) (Q z) u) := by
  letI : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
  letI : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩
  letI : MeasurableSpace (Input (d := d)) := borel _
  letI : BorelSpace (Input (d := d)) := ⟨rfl⟩
  have hh := (HilbertColumns.mapCLM (innerSL ℝ u)).continuous.measurable.comp
    (MatrixHaarKernel.measurable τ hτ Q hQ)
  simpa only [Function.comp_def, mapped_kernel] using hh

end SHEStochastic.MatrixCausalHeatRows
