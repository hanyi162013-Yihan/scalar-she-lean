module

public import SHE.ControlledReferenceLevel
public import SHE.UncutSmoothWords
public import SHE.ControlledReferenceFamilyLevel
public import SHE.ControlledReferenceFamilyBounds
public import SHE.ControlledReferenceCovariance
public import SHE.GaussianParameterContinuity
public import SHE.UncutHistoryMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ControlledReferenceFamilyContinuity
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open scoped NNReal
local instance controlledReferenceFamilyContinuity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceFamilyContinuity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceFamilyContinuity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n => F q.1 q.2))

local notation "Base" => ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hsmall in
theorem nodeCovariance_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History X k×(ℝ×HeatCircle)) :
    Continuous (fun p : Inputs => (CutoffCarriers.carrier (Base p) k).nodeCovariance h) := by
  apply Continuous.subtype_mk
  have hc := ControlledReferenceCovariance.covariance_inputs_continuous P hΛ θ v hsmall
    ((CutoffCarriers.carrier (Base (0,0)) k).observations.observations h.1)
    ((CutoffCarriers.carrier (Base (0,0)) k).terminal h.1)
    ((CutoffCarriers.carrier (Base (0,0)) k).nodeTime_mem h).2
    ((CutoffCarriers.carrier (Base (0,0)) k).targets_after h.1)
  convert hc using 1
  funext p
  change WordRecursion.covariance (ControlledReferenceWindows.coefficient P Λ θ v p)
    ((CutoffCarriers.carrier (Base p) k).observations.observations h.1)
    ((CutoffCarriers.carrier (Base p) k).nodeTime h) ((CutoffCarriers.carrier (Base p) k).terminal h.1)=_
  rw [ControlledReferenceFamilyBounds.carrier_observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h.1,
    ControlledReferenceFamilyBounds.carrier_nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h,
    ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h.1]
include hsmall in
/-- True normalized uncut words are jointly continuous in the two
past-state reference inputs and their finite-dimensional state. -/
theorem normalized_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History X k) :
    Continuous (fun q : Inputs×WordRecursion.State (n+k) => UncutSmoothWords.normalized (Base q.1) k h q.2) := by
  induction k with
  | zero => exact (hF.smooth h).continuous.comp continuous_snd
  | succ k ih =>
    let G := fun p : Inputs => UncutSmoothWords.normalized (Base p) k h.1
    have hG := ih h.1
    have hGs := uniform_reindex
      (ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k)
      (fun p : Inputs => (p,h.1))
    have hC := nodeCovariance_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k h
    have hH := GaussianParameterContinuity.continuous_average_hessian G hG hGs
      (fun p : Inputs => (CutoffCarriers.carrier (Base p) k).nodeCovariance h) hC
    have hp : Continuous (fun q : Inputs×WordRecursion.State (n+(k+1)) =>
        (q.1,SmoothWords.tailProjection (n+k) q.2)) :=
      continuous_fst.prodMk ((SmoothWords.tailProjection (n+k)).continuous.comp continuous_snd)
    have hH' := hH.comp hp
    have hr : Continuous (fun q : Inputs×WordRecursion.State (n+(k+1)) =>
        NormalizedInsertion.unitRow (CutoffCarriers.row (Base q.1) k h)) := by
      have he : (fun q : Inputs×WordRecursion.State (n+(k+1)) =>
          NormalizedInsertion.unitRow (CutoffCarriers.row (Base q.1) k h))=
          fun _ => NormalizedInsertion.unitRow (CutoffCarriers.row (Base (0,0)) k h) := by
        funext q
        rw [ControlledReferenceFamilyBounds.row_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm q.1 (0,0) k h]
      rw [he]
      exact continuous_const
    have hd := (hH'.clm_apply hr).clm_apply hr
    have ha := hA.smooth.continuous.comp ((SmoothWords.headProjection (n+k)).continuous.comp
      (continuous_snd : Continuous (fun q : Inputs×WordRecursion.State (n+(k+1)) => q.2)))
    have href : Continuous (fun q : Inputs×WordRecursion.State (n+(k+1)) =>
        ControlledReferenceWindows.coefficient P Λ θ v q.1 ((CutoffCarriers.carrier (Base q.1) k).nodeTime h,h.2.2)) := by
      have he : (fun q : Inputs×WordRecursion.State (n+(k+1)) =>
          ControlledReferenceWindows.coefficient P Λ θ v q.1 ((CutoffCarriers.carrier (Base q.1) k).nodeTime h,h.2.2))=
          fun q => ControlledReferenceWindows.coefficient P Λ θ v q.1 ((CutoffCarriers.carrier (Base (0,0)) k).nodeTime h,h.2.2) := by
        funext q
        rw [ControlledReferenceFamilyBounds.carrier_nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm q.1 (0,0) k h]
      rw [he]
      exact (ControlledReferenceWindows.coefficient_inputs_continuous P Λ θ v hΛ hsmall _).comp continuous_fst
    exact (continuous_const.mul (ha.sub href)).mul hd

include hsmall in
/-- The full uncut tests inherit actual parameter continuity. Their
possibly singular heat-history weight is independent of the reference
inputs and is kept explicit in the separate integrability theorem. -/
theorem test_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History X k) :
    Continuous (fun q : Inputs×WordRecursion.State (n+k) => UncutSmoothWords.test (Base q.1) k h q.2) := by
  have hh := (normalized_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k h).const_smul
    (UncutSmoothWords.weight (Base (0,0)) k h)
  convert hh using 1
  funext q
  rw [UncutSmoothWords.test_eq_weight_normalized,Pi.smul_apply,
    ControlledReferenceFamilyBounds.weight_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm q.1 (0,0) k h]
  rfl

end SHE.ControlledReferenceFamilyContinuity
