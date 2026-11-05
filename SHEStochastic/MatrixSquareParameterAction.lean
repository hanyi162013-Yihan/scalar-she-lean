module

public import SHEStochastic.MatrixSquareCoefficient
public import SHEStochastic.MatrixHaarParameterAction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixSquareParameterAction
open MeasureTheory MatrixInfiniteHaar MatrixSquareCoefficient
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Z : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Z]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (Q : Z → Profile d) (A : ∀ z, Data (Q z))
  (hQ : Measurable (fun z : Z × AddCircle (1 : ℝ) => (Q z.1).value z.2))
  (hA : Measurable (fun z : Z × AddCircle (1 : ℝ) => (A z.1).value z.2))

include hA in
theorem factor (u : Z → Input (d := d)) (hu : Measurable u) :
    Measurable (fun z => (A z).factor (u z)) :=
  MatrixFieldParameterAction.action (fun z x => (A z).value x) hA
    (fun z => (A z).measurable) (fun z => (A z).bound) (fun z => (A z).norm_bound)
    (fun z => VectorWhiteCoordinates.analysis.symm (u z))
    (VectorWhiteCoordinates.analysis.symm.continuous.measurable.comp hu)

include hQ hA in
theorem rotation (u : Z → Input (d := d)) (hu : Measurable u) :
    Measurable (fun z => (A z).rotation (u z)) := by
  simpa only [MatrixSquareCoefficient.Data.rotation_eq] using
    MatrixHaarParameterAction.analysis Q hQ _ (factor Q A hA u hu)

include hQ hA in
theorem inverse (u : Z → Input (d := d)) (hu : Measurable u) :
    Measurable (fun z => (A z).rotation.symm (u z)) := by
  let S := fun z => (A z).rotation.toContinuousLinearEquiv.toContinuousLinearMap
  have hs (i : d × SHE.FiniteHaar.HaarNode) : Measurable (fun z => S z (lp.single 2 i 1)) :=
    rotation Q A hQ hA _ measurable_const
  have hh := MeasurableHilbertSynthesis.adjoint_action S hs u hu
  have he (z : Z) : (S z).adjoint = (A z).rotation.symm.toContinuousLinearEquiv.toContinuousLinearMap :=
    (A z).rotation.adjoint_eq_symm
  simp only [he] at hh
  exact hh

end SHEStochastic.MatrixSquareParameterAction
