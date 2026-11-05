module

public import SHEStochastic.MatrixSqrtReference
public import SHE.SynthesisEquivalence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixHaarNoiseRotation
open MatrixInfiniteHaar

variable {d : Type*} [Fintype d] [DecidableEq d]

def sqrtEquivalence (P : Profile d) : Physical (d := d) ≃L[ℝ] Physical (d := d) :=
  ContinuousLinearEquiv.ofBijective (MatrixSqrtReference.operator P)
    (LinearMap.ker_eq_bot.mpr (MatrixSqrtReference.bijective P).1)
    (LinearMap.range_eq_top.mpr (MatrixSqrtReference.bijective P).2)

/-- The reference factor uses the fixed complete ordinary vector white
basis and the literal pointwise positive square root of the covariance. -/
def reference (P : Profile d) : Input (d := d) ≃L[ℝ] Physical (d := d) :=
  (VectorWhiteCoordinates.analysis (d := d)).symm.toContinuousLinearEquiv.trans (sqrtEquivalence P)

theorem reference_apply (P : Profile d) (z : Input (d := d)) :
    reference P z=MatrixSqrtReference.factor P z := rfl

theorem same_covariance (P : Profile d) :
    (MatrixInfiniteHaar.equivalence P).toContinuousLinearMap.comp
        (MatrixInfiniteHaar.equivalence P).toContinuousLinearMap.adjoint=
      (reference P).toContinuousLinearMap.comp (reference P).toContinuousLinearMap.adjoint := by
  change (MatrixInfiniteHaar.factor P).comp (MatrixInfiniteHaar.factor P).adjoint=
    (MatrixSqrtReference.factor P).comp (MatrixSqrtReference.factor P).adjoint
  rw [MatrixInfiniteHaar.covariance, MatrixSqrtReference.covariance]

/-- The countable Haar coordinate change is a genuine unitary map.
Both its covariance identity and invertibility have been proved for
the actual infinite spatial operators. -/
def rotation (P : Profile d) : Input (d := d) ≃ₗᵢ[ℝ] Input (d := d) :=
  SHE.SynthesisEquivalence.comparison (MatrixInfiniteHaar.equivalence P) (reference P) (same_covariance P)

theorem reconstruct (P : Profile d) (z : Input (d := d)) :
    MatrixInfiniteHaar.factor P (rotation P z)=MatrixSqrtReference.factor P z := by
  change MatrixInfiniteHaar.equivalence P
    ((MatrixInfiniteHaar.equivalence P).symm (reference P z))=reference P z
  exact (MatrixInfiniteHaar.equivalence P).apply_symm_apply _

theorem preserves_inner (P : Profile d) (x y : Input (d := d)) :
    inner ℝ (rotation P x) (rotation P y)=inner ℝ x y := (rotation P).inner_map_map x y

end SHEStochastic.MatrixHaarNoiseRotation
