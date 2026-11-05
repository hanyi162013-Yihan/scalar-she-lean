module

public import SHEStochastic.MatrixUnboundedNativeRowTransport
public import SHEStochastic.NativeNoiseEquivalence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.MatrixUnboundedNativeItoTransport
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace
    (Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi))) := borel _
local instance : BorelSpace
    (Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi))) := ⟨rfl⟩

/-- The native spatial Haar basis is exactly the old matrix noise basis
after the fixed circle-rescaling isometry. -/
theorem basis :
    NativeNoiseEquivalence.basis (VectorNativeHaarBasis.analysis (n := n)).symm
      (VectorNativeHaarBasis.basis (n := n)) =
      MatrixPredictableHaarRotation.basis (d := Fin n) := by
  apply DFunLike.ext
  intro k
  rw [NativeNoiseEquivalence.basis_apply,VectorNativeHaarBasis.basis_eq]
  change (VectorNativeHaarBasis.analysis (n := n))
    (VectorNativeHaarBasis.equivalence (VectorWhiteCoordinates.basis k)) =
      MatrixPredictableHaarRotation.basis k
  simp only [VectorNativeHaarBasis.analysis,LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply]
  rw [← VectorWhiteCoordinates.synthesis_single]
  rw [LinearIsometryEquiv.apply_symm_apply]
  rw [← HilbertBasis.repr_symm_single
    (MatrixPredictableHaarRotation.basis (d := Fin n)) k]
  change lp.single 2 k 1 =
    (LinearIsometryEquiv.refl ℝ (Input (d := Fin n))).symm (lp.single 2 k 1)
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H (Fin n×FiniteHaar.HaarNode))

/-- The native-row cylindrical Ito integral and the original matrix
Haar-coordinate Ito integral are the same isometry. -/
theorem terminal :
    restrictNoise
      (FiniteCylindricalIto.terminalIto P.toCoordinates (VectorNativeHaarBasis.basis (n := n)))
      (VectorNativeHaarBasis.analysis (n := n)).symm.toLinearIsometry =
      FiniteCylindricalIto.terminalIto P.toCoordinates
        (MatrixPredictableHaarRotation.basis (d := Fin n)) := by
  rw [←basis (n := n)]
  exact NativeNoiseEquivalence.integral_eq P
    (VectorNativeHaarBasis.analysis (n := n)).symm (VectorNativeHaarBasis.basis (n := n))

end SHEStochastic.MatrixUnboundedNativeItoTransport
