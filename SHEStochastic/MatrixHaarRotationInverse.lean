module

public import SHEStochastic.MatrixHaarParameterAction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixHaarRotationInverse
open MeasureTheory MatrixInfiniteHaar
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
variable {d P : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace P]
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩

/-- The inverse unitary action is measurable too, obtained from its
actual adjoint and the already checked column-measurability theorem. -/
theorem measurable (Q : P → Profile d)
    (hQ : Measurable (fun z : P × AddCircle (1 : ℝ) => (Q z.1).value z.2))
    (z : P → Input (d := d)) (hz : Measurable z) :
    Measurable (fun p => (MatrixHaarNoiseRotation.rotation (Q p)).symm (z p)) := by
  let S := fun p => (MatrixHaarNoiseRotation.rotation (Q p)).toContinuousLinearEquiv.toContinuousLinearMap
  have hs (i : d × SHE.FiniteHaar.HaarNode) : Measurable (fun p => S p (lp.single 2 i 1)) :=
    MatrixHaarParameterAction.rotation Q hQ _ measurable_const
  have hh := MeasurableHilbertSynthesis.adjoint_action S hs z hz
  have he (p : P) : (S p).adjoint=(MatrixHaarNoiseRotation.rotation (Q p)).symm.toContinuousLinearEquiv.toContinuousLinearMap :=
    (MatrixHaarNoiseRotation.rotation (Q p)).adjoint_eq_symm
  simp only [he] at hh
  convert! hh using 1 <;> rfl

/-- Testing the Haar noise after inverse unitary rotation gives the
literal square-root coefficient tested against the original noise. -/
theorem reconstruct_adjoint (Q : Profile d) (u : Physical (d := d)) :
    (MatrixHaarNoiseRotation.rotation Q).symm ((MatrixInfiniteHaar.factor Q).adjoint u)=
      (MatrixSqrtReference.factor Q).adjoint u := by
  let J := (MatrixHaarNoiseRotation.rotation Q).toContinuousLinearEquiv.toContinuousLinearMap
  have hh : (MatrixInfiniteHaar.factor Q).comp J=MatrixSqrtReference.factor Q := by
    apply ContinuousLinearMap.ext
    exact MatrixHaarNoiseRotation.reconstruct Q
  have ha := congrArg (fun K : Input (d := d) →L[ℝ] Physical (d := d) => K.adjoint) hh
  rw [ContinuousLinearMap.adjoint_comp] at ha
  have hJ : J.adjoint=(MatrixHaarNoiseRotation.rotation Q).symm.toContinuousLinearEquiv.toContinuousLinearMap :=
    (MatrixHaarNoiseRotation.rotation Q).adjoint_eq_symm
  rw [hJ] at ha
  exact congrArg (fun K : Physical (d := d) →L[ℝ] Input (d := d) => K u) ha

end SHEStochastic.MatrixHaarRotationInverse
