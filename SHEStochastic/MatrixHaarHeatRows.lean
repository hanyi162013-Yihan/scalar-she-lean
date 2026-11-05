module

public import SHEStochastic.MatrixHaarKernel
public import SHEStochastic.MatrixHaarFrameEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixHaarHeatRows
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology

def row (t : ℝ) (P : Profile d) (u : Physical (d := d)) : Input (d := d) :=
  (factor P).adjoint ((VectorHeat.heat t).adjoint u)

theorem coordinate {t : ℝ} (ht : 0 < t) (P : Profile d) (u : Physical (d := d)) (k : d × HaarNode) :
    row t P u k = inner ℝ (MatrixHaarKernel.kernel t P k) u := by
  rw [row, MatrixHaarFrameEnergy.analysis_coordinate]
  rw [MatrixHaarKernel.column, if_pos ht]
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

/-- Full covariance on vector heat observations, in the actual
infinite input space rather than on finite truncations. -/
theorem pairing (t : ℝ) (P : Profile d) (u v : Physical (d := d)) :
    inner ℝ (row t P u) (row t P v) =
      inner ℝ u (VectorHeat.heat t (multiplier P ((VectorHeat.heat t).adjoint v))) := by
  unfold row
  rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, covariance,
    ContinuousLinearMap.adjoint_inner_left]

theorem norm_sq (t : ℝ) (P : Profile d) (u : Physical (d := d)) :
    ‖row t P u‖ ^ 2 =
      inner ℝ u (VectorHeat.heat t (multiplier P ((VectorHeat.heat t).adjoint u))) := by
  rw [← real_inner_self_eq_norm_sq]
  exact pairing t P u u

/-- The genuine predictable Haar innovation rotates each heat row
to the square-root covariance reference row. -/
theorem rotation (t : ℝ) (P : Profile d) (u : Physical (d := d)) :
    (MatrixHaarNoiseRotation.rotation P).symm (row t P u) =
      (MatrixSqrtReference.factor P).adjoint ((VectorHeat.heat t).adjoint u) :=
  MatrixHaarRotationInverse.reconstruct_adjoint P _

theorem measurable {Z : Type*} [MeasurableSpace Z] (Q : Z → Profile d)
    (hQ : Measurable (fun z : Z × AddCircle (1 : ℝ) => (Q z.1).value z.2))
    (u : Z → Physical (d := d)) (hu : @Measurable Z (Physical (d := d)) _ (borel _) u) :
    @Measurable Z (Input (d := d)) _ (borel _) (fun z => (factor (Q z)).adjoint (u z)) := by
  letI : MeasurableSpace (Physical (d := d)) := borel _
  letI : BorelSpace (Physical (d := d)) := ⟨rfl⟩
  letI : MeasurableSpace (Input (d := d)) := borel _
  letI : BorelSpace (Input (d := d)) := ⟨rfl⟩
  apply MeasurableHilbertSynthesis.adjoint_action (fun z => factor (Q z)) _ u hu
  intro k
  exact MatrixHaarKernel.factor_measurable Q hQ (fun _ => lp.single 2 k 1) measurable_const

end SHEStochastic.MatrixHaarHeatRows
