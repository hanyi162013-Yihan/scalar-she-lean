module

public import SHEStochastic.L2EuclideanCoordinates
public import SHEStochastic.FiniteL2Flatten
public import SHE.AdditivePhysicalFactor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.VectorWhiteCoordinates
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation
open scoped ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

abbrev Physical := Lp (EuclideanSpace ℝ d) 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))
abbrev Input := lp (fun _ : d × HaarNode => ℝ) 2

/-- A single fixed scalar Haar identification, reused in every state
component. There is no new basis-existence assumption. -/
def scalar : RealL2 ≃ₗᵢ[ℝ] RealHaarInput :=
  (AdditivePhysicalFactor.whiteCoordinates 1 zero_lt_one).symm

/-- Actual countable vector white-noise coordinates: spatial `L²`, its
finite scalar components, scalar Haar coordinates, then a single index. -/
def analysis : Physical (d := d) ≃ₗᵢ[ℝ] Input (d := d) :=
  (L2EuclideanCoordinates.equivalence (AddCircle.haarAddCircle (T := (1 : ℝ)))).trans
    ((LinearIsometryEquiv.piLpCongrRight 2 (fun _ : d => scalar)).trans
      FiniteL2Flatten.equivalence)

def basis : HilbertBasis (d × HaarNode) ℝ (Physical (d := d)) :=
  HilbertBasis.ofRepr analysis

theorem coordinate (u : Physical (d := d)) (i : d) (q : HaarNode) :
    analysis u (i,q) = scalar (L2EuclideanCoordinates.coordinates (AddCircle.haarAddCircle (T := (1 : ℝ))) u i) q := rfl

theorem basis_coordinate (u : Physical (d := d)) (p : d × HaarNode) :
    analysis u p = inner ℝ (basis p) u := HilbertBasis.repr_apply_apply basis u p

/-- Parseval holds for the actual infinite vector basis, not just for
the finite dyadic Gram matrices. -/
theorem parseval (u : Physical (d := d)) :
    (∑' p : d × HaarNode, ‖inner ℝ (basis p) u‖ ^ 2) = ‖u‖ ^ 2 := by
  have hn := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (analysis u)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] at hn
  rw [hn]
  exact tsum_congr (fun p => congrArg (fun z : ℝ => ‖z‖ ^ 2) (basis_coordinate u p).symm)

theorem synthesis_single (p : d × HaarNode) : analysis.symm (lp.single 2 p 1) = basis p :=
  HilbertBasis.repr_symm_single basis p

end SHEStochastic.VectorWhiteCoordinates
