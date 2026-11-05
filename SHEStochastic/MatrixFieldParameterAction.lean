module

public import SHEStochastic.MatrixHaarParameterColumns
public import SHEStochastic.MeasurableHilbertL2Realization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixFieldParameterAction
open MeasureTheory Matrix MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {d P : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace P]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩

theorem fixed (K : P → AddCircle (1 : ℝ) → Matrix d d ℝ)
    (hK : Measurable (fun z : P × AddCircle (1 : ℝ) => K z.1 z.2))
    (hSection : ∀ p, Measurable (K p)) (B : P → ℝ≥0)
    (hB : ∀ p, ∀ᵐ x ∂μ, ‖K p x‖ ≤ B p) (v : Physical (d := d)) :
    Measurable (fun p => MatrixFieldOperator.operator (K p) (hSection p) (B p) (hB p) v) := by
  let F : P × AddCircle (1 : ℝ) → EuclideanSpace ℝ d :=
    fun z => Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (K z.1 z.2) (v z.2)
  have hc : Continuous (fun z : Matrix d d ℝ × EuclideanSpace ℝ d =>
      Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) z.1 z.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM (n := d) (𝕜 := ℝ)
  have hv : Measurable (fun z : P × AddCircle (1 : ℝ) => v z.2) :=
    (Lp.stronglyMeasurable v).measurable.comp measurable_snd
  have hp : Measurable (fun z : P × AddCircle (1 : ℝ) => (K z.1 z.2, v z.2)) := hK.prodMk hv
  have hm : Measurable F := by convert! hc.measurable.comp hp using 1
  apply MeasurableHilbertL2Realization.measurable F hm
    (fun p => MatrixFieldOperator.operator (K p) (hSection p) (B p) (hB p) v)
  intro p
  exact BoundedFieldOperator.operator_ae (MatrixFieldOperator.field (K p) (hSection p) (B p) (hB p)) v

/-- Jointly measurable bounded matrix fields act measurably on
variable vector `L²` inputs. The proof reuses the fixed complete white
basis and the general column-measurability synthesis theorem. -/
theorem action (K : P → AddCircle (1 : ℝ) → Matrix d d ℝ)
    (hK : Measurable (fun z : P × AddCircle (1 : ℝ) => K z.1 z.2))
    (hSection : ∀ p, Measurable (K p)) (B : P → ℝ≥0)
    (hB : ∀ p, ∀ᵐ x ∂μ, ‖K p x‖ ≤ B p)
    (u : P → Physical (d := d)) (hu : Measurable u) :
    Measurable (fun p => MatrixFieldOperator.operator (K p) (hSection p) (B p) (hB p) (u p)) := by
  let S := fun p => (MatrixFieldOperator.operator (K p) (hSection p) (B p) (hB p)).comp
    (VectorWhiteCoordinates.analysis (d := d)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hs (i : d × SHE.FiniteHaar.HaarNode) : Measurable (fun p => S p (lp.single 2 i 1)) := by
    change Measurable (fun p => MatrixFieldOperator.operator (K p) (hSection p) (B p) (hB p)
      (VectorWhiteCoordinates.analysis.symm (lp.single 2 i 1)))
    rw [VectorWhiteCoordinates.synthesis_single]
    exact fixed K hK hSection B hB _
  have hz := VectorWhiteCoordinates.analysis.continuous.measurable.comp hu
  have hh := MeasurableHilbertSynthesis.action (VectorWhiteCoordinates.basis (d := d)) S hs
    (fun p => VectorWhiteCoordinates.analysis (u p)) hz
  change Measurable (fun p => MatrixFieldOperator.operator (K p) (hSection p) (B p) (hB p)
    (VectorWhiteCoordinates.analysis.symm (VectorWhiteCoordinates.analysis (u p)))) at hh
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hh

end SHEStochastic.MatrixFieldParameterAction
