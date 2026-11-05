module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.ControlledReferenceRecursiveBackward
public import SHE.JointWordHessian
public import SHE.GaussianParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceRecursiveFields
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
local instance controlledReferenceRecursiveFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceRecursiveFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceRecursiveFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)

local notation "R" => referenceData P A hA Λ θ v b hvb
local notation "L" => ControlledReferenceRecursiveBounds.level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

variable {Ω : Type*} [MeasurableSpace Ω]
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

theorem state_eq (p p' : Inputs) (ε : ℝ≥0) (k : ℕ) (h : History Unit k) (ω : Ω) (t : ℝ) :
    JointWordAnalytic.state (L p ε k) Λ U V XU XV h ω t=
      JointWordAnalytic.state (L p' ε k) Λ U V XU XV h ω t := by
  unfold JointWordAnalytic.state
  rw [ControlledReferenceRecursiveBounds.observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p p' ε k h]

include hsmall in
theorem continuous_leaf (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ) (h : History Unit k) (ω : Ω) :
    Continuous (fun p : Inputs => JointWordAnalytic.leaf (L p ε k) Λ U V XU XV h ω) := by
  let y := JointWordAnalytic.state (L (0,0) ε k) Λ U V XU XV h ω ((L (0,0) ε k).terminal h)
  have hh := (ControlledReferenceRecursiveContinuity.continuous_test P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k h).comp
    (continuous_id.prodMk (continuous_const (y := y)))
  convert hh using 1
  funext p
  unfold JointWordAnalytic.leaf
  rw [ControlledReferenceRecursiveBounds.terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε ε k h,
    state_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ U V XU XV p (0,0) ε k h ω]
  rfl

include hsmall in
theorem continuous_reference (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ) (h : History Unit k) (ω : Ω) :
    Continuous (fun p : Inputs => JointWordAnalytic.reference (L p ε k) Λ U V XU XV h ω) := by
  let y := JointWordAnalytic.state (L (0,0) ε k) Λ U V XU XV h ω v
  have hh := (ControlledReferenceRecursiveBackward.continuous_backward P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k h v).comp
    (continuous_id.prodMk (continuous_const (y := y)))
  convert hh using 1
  funext p
  unfold JointWordAnalytic.reference
  change GaussianItoTest.backward ((L p ε k).window h) ((L p ε k).test h) v
    (JointWordAnalytic.state (L p ε k) Λ U V XU XV h ω v)=_
  rw [state_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ U V XU XV p (0,0) ε k h ω]
  rfl

include hsmall in
theorem continuous_hessian (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ) (h : History Unit k) (ω : Ω) (t : ℝ) :
    Continuous (fun p : Inputs => JointWordHessian.field (L p ε k) Λ U V XU XV ((h,ω),t)) := by
  let y := JointWordAnalytic.state (L (0,0) ε k) Λ U V XU XV h ω t
  have hh := (ControlledReferenceRecursiveBackward.continuous_hessian P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k h t).comp
    (continuous_id.prodMk (continuous_const (y := y)))
  convert hh using 1
  funext p
  unfold JointWordHessian.field
  rw [state_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ U V XU XV p (0,0) ε k h ω]
  rfl

include hsmall in
theorem continuous_insertion (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ) (h : History Unit k) (ω : Ω) (t : ℝ) (x : HeatCircle) :
    Continuous (fun p : Inputs => JointWordAnalytic.insertion (L p ε k) Λ U V XU XV h ω t x) := by
  have hh := continuous_hessian P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV hΛ ε k h ω t
  let r := WordRecursion.heatRow ((L (0,0) ε k).observations.observations h) t x
  have hd := (hh.clm_apply (continuous_const (y := r))).clm_apply (continuous_const (y := r))
  have hc := (continuous_const (y := A (XV (ω,(t,x))))).sub
    (ControlledReferenceWindows.coefficient_inputs_continuous P Λ θ v hΛ hsmall (t,x))
  have he := (hc.const_mul (1/2:ℝ)).mul hd
  convert he using 1
  funext p
  rw [JointWordAnalytic.insertion,JointPhysicalInsertion.insertion_appendState]
  unfold JointWordHessian.field
  rw [ControlledReferenceRecursiveBounds.observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε k h]
  rfl

end SHE.ControlledReferenceRecursiveFields
