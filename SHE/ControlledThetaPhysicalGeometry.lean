module

public import SHE.ControlledReferenceLevel
public import SHE.UncutSmoothWords
public import SHE.ControlledReferenceFamilyLevel
public import SHE.UncutHistoryMass
public import SHE.PhysicalParentGeometry
public import SHE.FullPhysicalWord
public import SHE.CarrierGeometryCongruence
public import SHE.CarrierPhysicalCongruence
public import SHE.ControlledReferenceThetaGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ControlledThetaPhysicalGeometry
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledThetaPhysicalGeometry_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaPhysicalGeometry_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaPhysicalGeometry_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n => F q.1 q.2))


open PhysicalChainArrays PhysicalScoreChain PhysicalParentGeometry
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

theorem lower_eq (p p' : ℝ×Inputs) (k : ℕ) (h : History X k) :
    PhysicalChainArrays.lower (Base p) k h=PhysicalChainArrays.lower (Base p') k h :=
  CarrierPhysicalCongruence.lower (Base p) (Base p') rfl (fun _=>rfl) k h

theorem upper_eq (p p' : ℝ×Inputs) (k : ℕ) (h : History X k) :
    PhysicalChainArrays.upper (Base p) k h=PhysicalChainArrays.upper (Base p') k h :=
  CarrierPhysicalCongruence.upper (Base p) (Base p') rfl (fun _=>rfl) k h

theorem directions_eq (p p' : ℝ×Inputs) {N : ℕ} (Q : Fin N→Observation) (k : ℕ) (h : History X k) :
    PhysicalChainArrays.directions (Base p) Q k h=PhysicalChainArrays.directions (Base p') Q k h :=
  CarrierPhysicalCongruence.directions (Base p) (Base p') rfl (fun _=>rfl) Q k h

theorem covariances_eq (p p' : ℝ×Inputs) {N : ℕ} (Q : Fin N→Observation) (c : StoppedGaussianFeatures.Domain→ℝ) (k : ℕ) (h : History X k) :
    PhysicalChainArrays.covariances (Base p) Q c k h=PhysicalChainArrays.covariances (Base p') Q c k h :=
  CarrierPhysicalCongruence.covariances (Base p) (Base p') rfl (fun _=>rfl) Q c k h

theorem scoreProduct_eq (p p' : ℝ×Inputs) {N : ℕ} (Q : Fin N→Observation) (c : StoppedGaussianFeatures.Domain→ℝ) (k : ℕ) (h : History X k) :
    PhysicalScoreChain.scoreProduct (Base p) Q c k h=PhysicalScoreChain.scoreProduct (Base p') Q c k h :=
  CarrierPhysicalCongruence.scoreProduct (Base p) (Base p') rfl (fun _=>rfl) Q c k h

theorem strict_iff (p p' : ℝ×Inputs) (k : ℕ) (h : History X k) :
    StrictHistory (Base p) k h↔StrictHistory (Base p') k h :=
  CarrierPhysicalCongruence.strict_iff (Base p) (Base p') rfl (fun _=>rfl) k h

theorem small_iff (p p' : ℝ×Inputs) (Hs : ℕ→ℝ) (k : ℕ) (h : History X k) :
    SmallHistory (Base p) Hs k h↔SmallHistory (Base p') Hs k h :=
  CarrierPhysicalCongruence.small_iff (Base p) (Base p') rfl (fun _=>rfl) (fun _=>rfl) Hs k h

theorem timeWeight_eq (p p' : ℝ×Inputs) (ell : ℝ) (Cs : ℕ→ℝ) (k : ℕ) (h : History X k) :
    PhysicalScoreChain.timeWeight (Base p) ell Cs k h=PhysicalScoreChain.timeWeight (Base p') ell Cs k h :=
  CarrierPhysicalCongruence.timeWeight (Base p) (Base p') rfl (fun _=>rfl) ell Cs k h

end SHE.ControlledThetaPhysicalGeometry
