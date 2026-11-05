module
public import SHE.ScalarHaarRotation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 250000
namespace SHE.ScalarHaarRotation
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle
open NoiseSplitting OrthogonalItoChannels AdditivePhysicalFactor
open scoped ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance (ell M : ℝ) : MeasurableSpace (EllipticField ell M) := Subtype.instMeasurableSpace
local instance (ell M : ℝ) : BorelSpace (EllipticField ell M) := by infer_instance
variable (D : SmoothApproximation.ScalarData)

def action (u : RealL2) (z : Both RealHaarInput) : Both RealL2 :=
  (rotation D u).toFun z

theorem action_eq (u : RealL2) (z : Both RealHaarInput) : action D u z = rotation D u z := rfl

/-- The actual state-dependent scalar splitting and Haar innovation is
jointly measurable. It can therefore be substituted into any original
predictable solution without postulating a noise rotation. -/
theorem action_measurable : Measurable (fun p : RealL2 × Both RealHaarInput => action D p.1 p.2) := by
  let P := RealL2 × Both RealHaarInput
  let A : P × UnitAddCircle → ℝ := fun p => scalar D p.1.1 p.2
  have hmap : Measurable (fun p : P × UnitAddCircle => (p.1.1,p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hA0 := (scalar_joint D).comp hmap
  have hA : Measurable A := hA0
  have hp : Measurable (fun p : P => (p.2).ofLp) :=
    (WithLp.measurable_ofLp 2 (RealHaarInput × RealHaarInput)).comp measurable_snd
  have hl : Measurable (fun p : P => whiteCoordinates ((amplitude D)^2)
      (sq_pos_of_pos (amplitude_pos D)) p.2.fst) :=
    (whiteCoordinates ((amplitude D)^2) (sq_pos_of_pos (amplitude_pos D))).continuous.measurable.comp
      (measurable_fst.comp hp)
  have hmres : Measurable (fun p : P => residual D p.1) := (residual_measurable D).comp measurable_fst
  have hmsecond : Measurable (fun p : P => p.2.snd) := measurable_snd.comp hp
  have hpair := hmres.prodMk hmsecond
  have hinv := measurable_fieldRealInnovationInverse_joint D.ell D.cap D.ell_pos
  have hr0 := hinv.comp hpair
  have hr : Measurable (fun p : P => (fieldRealInnovation D.ell D.cap D.ell_pos (residual D p.1)).symm p.2.snd) := hr0
  let V : P → Both RealL2 := fun p => WithLp.toLp 2
    (whiteCoordinates ((amplitude D)^2) (sq_pos_of_pos (amplitude_pos D)) p.2.fst,
      (fieldRealInnovation D.ell D.cap D.ell_pos (residual D p.1)).symm p.2.snd)
  have hV : Measurable V := (WithLp.measurable_toLp 2 (RealL2 × RealL2)).comp (hl.prodMk hr)
  exact NoiseSplitting.physicalRotation_measurable_process haarAddCircle A hA
    (amplitude D) (amplitude_pos D) (fun p => scalar_gap D p.1) V hV

end SHE.ScalarHaarRotation
