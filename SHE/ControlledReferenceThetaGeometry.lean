module

public import SHE.ControlledReferenceLevel
public import SHE.UncutSmoothWords
public import SHE.ControlledReferenceFamilyLevel
public import SHE.UncutHistoryMass
public import SHE.PhysicalParentGeometry
public import SHE.FullPhysicalWord
public import SHE.CarrierGeometryCongruence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ControlledReferenceThetaGeometry
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledReferenceThetaGeometry_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceThetaGeometry_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceThetaGeometry_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n => F q.1 q.2))

/-- The actual controlled family jointly parameterized by interpolation
and both original past states. -/
abbrev level (p : ℝ×Inputs) : Level
    (ControlledReferenceLevel.referenceData P A hA Λ p.1 v b hvb p.2) X n :=
  ControlledReferenceFamilyLevel.level P A hA Λ p.1 v b hvb Z htarget hstop F hF hFm p.2
local notation "Base" => level P A hA Λ v b hvb Z htarget hstop F hF hFm

theorem carrier_terminal_eq (p p' : ℝ×Inputs) (k : ℕ) (h : History X k) :
    (CutoffCarriers.carrier (Base p) k).terminal h=(CutoffCarriers.carrier (Base p') k).terminal h :=
  CarrierGeometryCongruence.terminal (Base p) (Base p') rfl (fun _=>rfl) k h

theorem carrier_nodeTime_eq (p p' : ℝ×Inputs) (k : ℕ) (h : History X k×(ℝ×HeatCircle)) :
    (CutoffCarriers.carrier (Base p) k).nodeTime h=(CutoffCarriers.carrier (Base p') k).nodeTime h :=
  CarrierGeometryCongruence.nodeTime (Base p) (Base p') rfl (fun _=>rfl) k h

theorem carrier_observations_eq (p p' : ℝ×Inputs) (k : ℕ) (h : History X k) :
    (CutoffCarriers.carrier (Base p) k).observations.observations h=(CutoffCarriers.carrier (Base p') k).observations.observations h :=
  CarrierGeometryCongruence.observations (Base p) (Base p') rfl (fun _=>rfl) (fun _=>rfl) k h

/-- The genuine uncut history row depends on original stops, targets
and spatial centers, and is independent of the random reference input. -/
theorem row_eq (p p' : ℝ×Inputs) (k : ℕ) (h : History X k×(ℝ×HeatCircle)) :
    CutoffCarriers.row (Base p) k h=CutoffCarriers.row (Base p') k h :=
  CarrierGeometryCongruence.row (Base p) (Base p') rfl (fun _=>rfl) (fun _=>rfl) k h

theorem weight_eq (p p' : ℝ×Inputs) (k : ℕ) (h : History X k) :
    UncutSmoothWords.weight (Base p) k h=UncutSmoothWords.weight (Base p') k h :=
  CarrierGeometryCongruence.weight (Base p) (Base p') rfl (fun _=>rfl) (fun _=>rfl) k h


end SHE.ControlledReferenceThetaGeometry
