module

public import SHE.ControlledReferenceLevel
public import SHE.ControlledReferenceFamilyContinuity
public import SHE.RecursiveHeatBounds
public import SHE.UncutSmoothWords
public import SHE.UncutHistoryMass
public import SHE.ControlledReferenceUncutBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.GaussianParameterContinuity
public import SHE.ControlledReferenceUncutContinuity
public import SHE.ControlledReferenceRecursiveFields
public import SHE.JointUncutWordEvaluation
public import SHE.PastParameterDiagonal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceFamilyEvaluation
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
local instance controlledReferenceFamilyEvaluation_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceFamilyEvaluation_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceFamilyEvaluation_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

local instance controlledReferenceFamilyEvaluation_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {Ω : Type} [MeasurableSpace Ω]
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)
variable (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)

def leaf (p : Inputs) (k : ℕ) (h : History X k) (ω : Ω) : ℝ :=
  JointUncutWordEvaluation.leaf (Base p) Λ U V XU XV k h ω

def reference (p : Inputs) (k : ℕ) (h : History X k) (ω : Ω) : ℝ :=
  JointUncutWordEvaluation.reference (Base p) Λ U V XU XV k h ω

include hsmall in
theorem leaf_parameter_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History X k) (ω : Ω) :
    Continuous (fun p : Inputs => leaf P A hA Λ θ v b hvb Z htarget hstop F hF hFm U V XU XV p k h ω) := by
  let Y := JointWordAnalytic.state (CutoffCarriers.carrier (Base (0,0)) k) Λ U V XU XV h ω
    ((CutoffCarriers.carrier (Base (0,0)) k).terminal h)
  have hh := (ControlledReferenceFamilyContinuity.test_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k h).comp
    (continuous_id.prodMk (continuous_const (y := Y)))
  convert hh using 1
  funext p
  unfold leaf JointUncutWordEvaluation.leaf
  rw [ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h]
  have hs : JointWordAnalytic.state (CutoffCarriers.carrier (Base p) k) Λ U V XU XV h ω ((CutoffCarriers.carrier (Base (0,0)) k).terminal h)=
      JointWordAnalytic.state (CutoffCarriers.carrier (Base (0,0)) k) Λ U V XU XV h ω ((CutoffCarriers.carrier (Base (0,0)) k).terminal h) := by
    unfold JointWordAnalytic.state
    rw [ControlledReferenceFamilyBounds.carrier_observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h]
  rw [hs]
  rfl

include hsmall in
theorem reference_parameter_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History X k) (ω : Ω) :
    Continuous (fun p : Inputs => reference P A hA Λ θ v b hvb Z htarget hstop F hF hFm U V XU XV p k h ω) := by
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceFamilyBounds.test_norm_bound P A hA Λ θ v b hvb Z htarget hstop F hF hFm k
  let Y := JointWordAnalytic.state (CutoffCarriers.carrier (Base (0,0)) k) Λ U V XU XV h ω v
  have hCcont := ControlledReferenceFamilyContinuity.nodeCovariance_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k (h,((v:ℝ),0))
  have hh := (GaussianParameterContinuity.continuous_average
    (fun p : Inputs => UncutSmoothWords.test (Base p) k h)
    (ControlledReferenceFamilyContinuity.test_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k h)
    (fun p z => hC p h z)
    (fun p : Inputs => (CutoffCarriers.carrier (Base p) k).nodeCovariance (h,((v:ℝ),0))) hCcont).comp
    (continuous_id.prodMk (continuous_const (y := Y)))
  convert hh using 1
  funext p
  unfold reference JointUncutWordEvaluation.reference
  change GaussianSmooth.average _ _ (JointWordAnalytic.state (CutoffCarriers.carrier (Base p) k) Λ U V XU XV h ω v)=_
  have hs : JointWordAnalytic.state (CutoffCarriers.carrier (Base p) k) Λ U V XU XV h ω v=
      JointWordAnalytic.state (CutoffCarriers.carrier (Base (0,0)) k) Λ U V XU XV h ω v := by
    unfold JointWordAnalytic.state
    rw [ControlledReferenceFamilyBounds.carrier_observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h]
  rw [hs]
  rfl

include hsmall hU hV hXU hXV in
theorem diagonal_measurable (hΛ : 0≤Λ) (u : Ω→Inputs) (hu : StronglyMeasurable u) (k : ℕ) :
    Measurable (fun q : History X k×Ω => leaf P A hA Λ θ v b hvb Z htarget hstop F hF hFm U V XU XV (u q.2) k q.1 q.2) ∧
    Measurable (fun q : History X k×Ω => reference P A hA Λ θ v b hvb Z htarget hstop F hF hFm U V XU XV (u q.2) k q.1 q.2) := by
  let Q := History X k×Ω
  have huQ : StronglyMeasurable (fun q : Q => u q.2) := hu.comp_measurable measurable_snd
  have hL (p : Inputs) : Measurable (fun q : Q => leaf P A hA Λ θ v b hvb Z htarget hstop F hF hFm U V XU XV p k q.1 q.2) :=
    JointUncutWordEvaluation.leaf_measurable (Base p) Λ hU hV hXU hXV k
  have hR (p : Inputs) : Measurable (fun q : Q => reference P A hA Λ θ v b hvb Z htarget hstop F hF hFm U V XU XV p k q.1 q.2) :=
    JointUncutWordEvaluation.reference_measurable (Base p) Λ hU hV hXU hXV k
  have hl := PastParameterDiagonal.stronglyMeasurable_diagonal (inferInstance : MeasurableSpace Q) le_rfl
    (fun p q => leaf P A hA Λ θ v b hvb Z htarget hstop F hF hFm U V XU XV p k q.1 q.2) hL huQ
    (fun q => leaf_parameter_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall U V XU XV hΛ k q.1 q.2)
  have hr := PastParameterDiagonal.stronglyMeasurable_diagonal (inferInstance : MeasurableSpace Q) le_rfl
    (fun p q => reference P A hA Λ θ v b hvb Z htarget hstop F hF hFm U V XU XV p k q.1 q.2) hR huQ
    (fun q => reference_parameter_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall U V XU XV hΛ k q.1 q.2)
  exact ⟨hl.measurable,hr.measurable⟩

/-- The same true uncut history weight controls the literal actual
leaf and full joint-current Gaussian reference, uniformly in both
random past-state inputs. -/
theorem evaluation_bound (k : ℕ) : ∃ C : ℝ,0≤C ∧ ∀ (p : Inputs) (h : History X k) ω,
    ‖leaf P A hA Λ θ v b hvb Z htarget hstop F hF hFm U V XU XV p k h ω‖≤C*UncutSmoothWords.weight (Base (0,0)) k h ∧
    ‖reference P A hA Λ θ v b hvb Z htarget hstop F hF hFm U V XU XV p k h ω‖≤C*UncutSmoothWords.weight (Base (0,0)) k h := by
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceFamilyBounds.test_norm_bound P A hA Λ θ v b hvb Z htarget hstop F hF hFm k
  exact ⟨C,hCn,fun p h ω => ⟨hC p h _,GaussianSmooth.average_norm_bound _ (hC p h) _⟩⟩

end SHE.ControlledReferenceFamilyEvaluation
