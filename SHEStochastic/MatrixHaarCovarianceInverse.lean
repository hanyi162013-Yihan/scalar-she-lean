module

public import SHEStochastic.MatrixInfiniteHaar

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixHaarCovarianceInverse
open MatrixInfiniteHaar

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The inverse covariance multiplier is built from the completed
weighted Haar synthesis. This uses no extra pointwise inverse bounds. -/
def inverse (P : Profile d) : Physical (d := d) →L[ℝ] Physical (d := d) :=
  (synthesis P).comp (synthesis P).adjoint

theorem inverse_left (P : Profile d) :
    (inverse P).comp (multiplier P)=ContinuousLinearMap.id ℝ (Physical (d := d)) := by
  have hh := WeightedBasisFactor.right_identity (synthesis P) (multiplier P)
    (weighted_identity P) (synthesis_bijective P).2
  simpa only [inverse, ContinuousLinearMap.comp_assoc] using hh

theorem inverse_right (P : Profile d) :
    (multiplier P).comp (inverse P)=ContinuousLinearMap.id ℝ (Physical (d := d)) := by
  have hh := WeightedBasisFactor.physical_inverse (synthesis P) (multiplier P)
    (weighted_identity P) (synthesis_bijective P).2 (multiplier_selfadjoint P)
  simpa only [inverse, ContinuousLinearMap.comp_assoc] using hh

def equivalence (P : Profile d) : Physical (d := d) ≃L[ℝ] Physical (d := d) :=
  ContinuousLinearEquiv.equivOfInverse' (multiplier P) (inverse P)
    (inverse_right P) (inverse_left P)

theorem bijective (P : Profile d) : Function.Bijective (multiplier P) :=
  (equivalence P).bijective

end SHEStochastic.MatrixHaarCovarianceInverse
