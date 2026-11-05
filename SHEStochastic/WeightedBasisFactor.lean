module

public import SHEStochastic.WeightedRieszSynthesis

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.WeightedBasisFactor

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A complete weighted Gram identity supplies the right inverse on
the physical Hilbert space, not merely a left inverse on coefficients. -/
theorem right_identity (S : E →L[ℝ] F) (M : F →L[ℝ] F)
    (hWeighted : S.adjoint.comp (M.comp S)=ContinuousLinearMap.id ℝ E)
    (hSurj : Function.Surjective S) :
    S.comp (S.adjoint.comp M)=ContinuousLinearMap.id ℝ F := by
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hSurj y
  have hh := congrArg (fun K : E →L[ℝ] E => S (K x)) hWeighted
  exact hh

theorem physical_inverse (S : E →L[ℝ] F) (M : F →L[ℝ] F)
    (hWeighted : S.adjoint.comp (M.comp S)=ContinuousLinearMap.id ℝ E)
    (hSurj : Function.Surjective S) (hM : M.adjoint=M) :
    (M.comp S).comp S.adjoint=ContinuousLinearMap.id ℝ F := by
  have hh := congrArg (fun K : F →L[ℝ] F => K.adjoint) (right_identity S M hWeighted hSurj)
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint_id, hM, ContinuousLinearMap.comp_assoc] using hh

/-- Multiplying a complete weighted Haar synthesis by its covariance
multiplier gives a genuinely invertible physical factor. Its inverse
is the weighted Haar analysis operator. -/
def equivalence (S : E →L[ℝ] F) (M : F →L[ℝ] F)
    (hWeighted : S.adjoint.comp (M.comp S)=ContinuousLinearMap.id ℝ E)
    (hSurj : Function.Surjective S) (hM : M.adjoint=M) : E ≃L[ℝ] F :=
  ContinuousLinearEquiv.equivOfInverse' (M.comp S) S.adjoint
    (physical_inverse S M hWeighted hSurj hM) hWeighted

/-- The full infinite covariance identity follows from completeness
and weighted orthogonality, preserving the order of matrix products. -/
theorem covariance (S : E →L[ℝ] F) (M : F →L[ℝ] F)
    (hWeighted : S.adjoint.comp (M.comp S)=ContinuousLinearMap.id ℝ E)
    (hSurj : Function.Surjective S) (hM : M.adjoint=M) :
    (M.comp S).comp (M.comp S).adjoint=M := by
  rw [ContinuousLinearMap.adjoint_comp, hM]
  calc
    _ = ((M.comp S).comp S.adjoint).comp M := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = M := by rw [physical_inverse S M hWeighted hSurj hM, ContinuousLinearMap.id_comp]

end SHEStochastic.WeightedBasisFactor
