module

public import SHEStochastic.VectorNativeHeatEndpoint
public import SHEStochastic.VectorWhiteCoordinates

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.VectorNativeHaarBasis
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}

private theorem scale_inverse (x : AddCircle (2*Real.pi)) :
    CircleNormalization.scale 1 (2*Real.pi)
      (CircleNormalization.scale (2*Real.pi) 1 x)=x := by
  induction x using Quotient.inductionOn with
  | _ r =>
    simp only [CircleNormalization.scale,AddCircle.equivAddCircle_apply_mk]
    congr 1
    field_simp

def back : Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi)) →ₗᵢ[ℝ]
    Physical (d := Fin n) :=
  Lp.compMeasurePreservingₗᵢ ℝ (CircleNormalization.scale 1 (2*Real.pi))
    (CircleNormalization.scale_measurePreserving 1 (2*Real.pi))

theorem push_back (u : Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi))) :
    VectorNativeHeatEndpoint.push (back u)=u := by
  change Lp.compMeasurePreserving (CircleNormalization.scale (2*Real.pi) 1)
    (CircleNormalization.scale_measurePreserving (2*Real.pi) 1)
    (Lp.compMeasurePreserving (CircleNormalization.scale 1 (2*Real.pi))
      (CircleNormalization.scale_measurePreserving 1 (2*Real.pi)) u)=u
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : (CircleNormalization.scale 1 (2*Real.pi)) ∘
      (CircleNormalization.scale (2*Real.pi) 1) = id := funext scale_inverse
  simpa only [he] using (Lp.compMeasurePreserving_id_apply u)

def equivalence : Physical (d := Fin n) ≃ₗᵢ[ℝ]
    Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi)) :=
  LinearIsometryEquiv.ofSurjective VectorNativeHeatEndpoint.push
    (fun u => ⟨back u,push_back u⟩)

def analysis : Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi)) ≃ₗᵢ[ℝ]
    Input (d := Fin n) :=
  equivalence.symm.trans VectorWhiteCoordinates.analysis

def basis : HilbertBasis (Fin n × HaarNode) ℝ
    (Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi))) :=
  HilbertBasis.ofRepr analysis

theorem basis_eq (k : Fin n × HaarNode) :
    basis (n := n) k = equivalence (VectorWhiteCoordinates.basis k) := by
  rw [←(basis (n := n)).repr_symm_single k]
  change (analysis (n := n)).symm (lp.single 2 k 1) = _
  change equivalence (VectorWhiteCoordinates.analysis.symm (lp.single 2 k 1)) =
    equivalence (VectorWhiteCoordinates.basis k)
  exact congrArg equivalence (VectorWhiteCoordinates.synthesis_single k)

end SHEStochastic.VectorNativeHaarBasis
