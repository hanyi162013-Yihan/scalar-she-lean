module

public import SHEStochastic.MatrixProfileEntries
public import SHEStochastic.MatrixHaarNegativeFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.VectorScalarTransform
open SHE SHE.FiniteHaar SHE.DyadicApproximation MatrixProfileEntries MatrixInfiniteHaar
open scoped ENNReal
variable {d E : Type*} [Fintype d] [DecidableEq d] [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Output (d E : Type*) [Fintype d] [NormedAddCommGroup E] := PiLp 2 (fun _ : d => E)

def map (T : RealL2 →L[ℝ] E) : Physical (d := d) →L[ℝ] Output d E :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun r : d => T.comp (component r)))

theorem apply (T : RealL2 →L[ℝ] E) (u : Physical (d := d)) (r : d) : map T u r = T (component r u) := rfl

theorem norm_sq (T : RealL2 →L[ℝ] E) (u : Physical (d := d)) :
    ‖map T u‖^2 = ∑ r : d, ‖T (component r u)‖^2 := PiLp.norm_sq_eq_of_L2 _ _

end SHEStochastic.VectorScalarTransform
