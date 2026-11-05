module

public import SHE.ControlledReferenceLevel
public import SHE.UncutSmoothWords
public import SHE.ControlledReferenceFamilyLevel
public import SHE.ControlledReferenceFamilyBounds
public import SHE.ControlledReferenceFamilyContinuity
public import SHE.UncutWordEvaluation
public import SHE.JointWordHessian
public import SHE.ControlledReferenceCovariance
public import SHE.GaussianParameterContinuity
public import SHE.UncutHistoryMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ControlledReferenceFamilyBackward
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open scoped NNReal
local instance controlledReferenceFamilyBackward_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceFamilyBackward_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceFamilyBackward_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

local notation "NL" => (fun p k => UncutWordEvaluation.normalizedLevel (Base p) k)

include hsmall in
theorem window_path_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History X k) (t : ℝ) :
    Continuous (fun p : Inputs => ((NL p k).window h).path t) := by
  apply Continuous.subtype_mk
  let T := (NL (0,0) k).terminal h
  let Z₀ := (NL (0,0) k).observations.observations h
  have hc := ControlledReferenceCovariance.covariance_inputs_continuous P hΛ θ v hsmall Z₀ T
    (ClippedCovariance.clip_mem ((NL (0,0) k).terminal_base h) t).2
    ((NL (0,0) k).targets_after h)
  convert hc using 1
  funext p
  change WordRecursion.covariance (ControlledReferenceWindows.coefficient P Λ θ v p)
    ((CutoffCarriers.carrier (Base p) k).observations.observations h)
    (ClippedCovariance.clip (v:ℝ) ((CutoffCarriers.carrier (Base p) k).terminal h) t)
    ((CutoffCarriers.carrier (Base p) k).terminal h)=_
  rw [ControlledReferenceFamilyBounds.carrier_observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h,
    ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h]
  rfl

include hsmall in
/-- Full-reserve state Hessians of normalized uncut words depend
continuously on both past inputs, including scalar zero-root-gap
observations and singular collision covariances. -/
theorem hessian_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History X k) (t : ℝ) :
    Continuous (fun q : Inputs×WordRecursion.State (n+k) => GaussianTaylor.hessian
      (GaussianItoTest.backward ((NL q.1 k).window h) ((NL q.1 k).test h) t) q.2) := by
  have hFs := uniform_reindex
    (ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k)
    (fun p : Inputs => (p,h))
  exact GaussianParameterContinuity.continuous_average_hessian
    (fun p : Inputs => (NL p k).test h)
    (ControlledReferenceFamilyContinuity.normalized_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k h)
    hFs (fun p : Inputs => ((NL p k).window h).path t)
    (window_path_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k h t)

variable {Ω : Type} [MeasurableSpace Ω]
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

include hsmall in
theorem hessian_field_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History X k) (ω : Ω) (t : ℝ) :
    Continuous (fun p : Inputs => JointWordHessian.field (NL p k) Λ U V XU XV ((h,ω),t)) := by
  let y := JointWordAnalytic.state (NL (0,0) k) Λ U V XU XV h ω t
  have hh := (hessian_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k h t).comp
    (continuous_id.prodMk (continuous_const (y := y)))
  convert hh using 1
  funext p
  unfold JointWordHessian.field
  have hs : JointWordAnalytic.state (NL p k) Λ U V XU XV h ω t=y := by
    unfold JointWordAnalytic.state
    change JointWordObserve.evaluate Λ _ _ _ _ ((CutoffCarriers.carrier (Base p) k).observations.observations h) t=_
    rw [ControlledReferenceFamilyBounds.carrier_observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h]
    rfl
  rw [hs]
  rfl

end SHE.ControlledReferenceFamilyBackward

