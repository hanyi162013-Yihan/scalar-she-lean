module

public import SHEStochastic.MatrixFieldParameterAction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixHaarParameterAction
open MeasureTheory MatrixInfiniteHaar
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {d P : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace P]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩

variable (Q : P → Profile d)
  (hQ : Measurable (fun z : P × AddCircle (1 : ℝ) => (Q z.1).value z.2))

include hQ in
theorem synthesis (z : P → Input (d := d)) (hz : Measurable z) :
    Measurable (fun p => MatrixInfiniteHaar.synthesis (Q p) (z p)) := by
  apply MeasurableHilbertSynthesis.action (VectorWhiteCoordinates.basis (d := d))
    (fun p => MatrixInfiniteHaar.synthesis (Q p)) _ z hz
  intro i
  simpa only [MatrixInfiniteHaar.synthesis_single] using MatrixHaarParameterColumns.column Q hQ i

include hQ in
theorem analysis (u : P → Physical (d := d)) (hu : Measurable u) :
    Measurable (fun p => (MatrixInfiniteHaar.synthesis (Q p)).adjoint (u p)) := by
  apply MeasurableHilbertSynthesis.adjoint_action (fun p => MatrixInfiniteHaar.synthesis (Q p)) _ u hu
  intro i
  simpa only [MatrixInfiniteHaar.synthesis_single] using MatrixHaarParameterColumns.column Q hQ i

include hQ in
theorem squareRoot (z : P → Input (d := d)) (hz : Measurable z) :
    Measurable (fun p => MatrixSqrtReference.factor (Q p) (z p)) := by
  have hK := CFC.measurable_sqrt.comp hQ
  have hu := VectorWhiteCoordinates.analysis.symm.continuous.measurable.comp hz
  have hh := MatrixFieldParameterAction.action (fun p x => CFC.sqrt ((Q p).value x)) hK
    (fun p => CFC.measurable_sqrt.comp (Q p).measurable)
    (fun p => NNReal.sqrt (Q p).bound) (fun p => MatrixSqrtReference.sqrt_bound (Q p))
    (fun p => VectorWhiteCoordinates.analysis.symm (z p)) hu
  exact hh

theorem rotation_eq (A : Profile d) (z : Input (d := d)) :
    MatrixHaarNoiseRotation.rotation A z=
      (MatrixInfiniteHaar.synthesis A).adjoint (MatrixSqrtReference.factor A z) := rfl

include hQ in
/-- The genuine infinite unitary noise change acts measurably on
variable inputs for every jointly measurable elliptic matrix profile. -/
theorem rotation (z : P → Input (d := d)) (hz : Measurable z) :
    Measurable (fun p => MatrixHaarNoiseRotation.rotation (Q p) (z p)) := by
  simpa only [rotation_eq] using analysis Q hQ _ (squareRoot Q hQ z hz)

end SHEStochastic.MatrixHaarParameterAction
