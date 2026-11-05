module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.ControlledReferenceRecursiveBackward
public import SHE.ControlledReferenceRecursiveFields
public import SHE.JointLiteralChildLimit
public import SHE.FiniteParameterL1Limit
public import SHE.PastParameterDiagonal
public import SHE.GaussianParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceLiteralChildren
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open Filter Topology
open scoped NNReal
local instance controlledReferenceLiteralChildren_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceLiteralChildren_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceLiteralChildren_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

local instance controlledReferenceLiteralChildren_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)
variable (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)
local notation "Base" => ControlledReferenceLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF

theorem childObservations_eq (p p' : Inputs) (ε : ℝ≥0) (k : ℕ) (h : History Unit k×(ℝ×HeatCircle)) :
    (L p ε k).childObservations.observations h=(L p' ε k).childObservations.observations h := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrArg (fun t : ℝ => (⟨t,t,h.2.2⟩ : Observation))
      (ControlledReferenceRecursiveBounds.nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p p' ε ε k h)
  · exact congrFun (ControlledReferenceRecursiveBounds.observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p p' ε k h.1) j

include hsmall in
theorem childLeaf_parameter_continuous (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ)
    (h : History Unit k×(ℝ×HeatCircle)) (ω : Ω) :
    Continuous (fun p : Inputs => JointCutoffStep.childLeaf (L p ε k) Λ δ U V XU XV h ω) := by
  let Y := JointWordObserve.evaluate Λ (fun t => U (ω,t)) (fun t => V (ω,t))
    (fun tx => XU (ω,tx)) (fun tx => XV (ω,tx))
    ((L (0,0) ε k).childObservations.observations h) ((L (0,0) ε k).nodeTime h)
  have hh := (ControlledReferenceRecursiveContinuity.continuous_test P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε (k+1) h).comp
    (continuous_id.prodMk (continuous_const (y := Y)))
  convert hh using 1
  funext p
  unfold JointCutoffStep.childLeaf
  rw [childObservations_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε k h,
    ControlledReferenceRecursiveBounds.nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε ε k h]
  rfl

include hsmall hU hV hXU hXV in
theorem childLeaf_diagonal_measurable (hΛ : 0≤Λ) (u : Ω→Inputs) (hu : StronglyMeasurable u) (ε : ℝ≥0) (k : ℕ) :
    Measurable (fun q : History Unit (k+1)×Ω => JointCutoffStep.childLeaf (L (u q.2) ε k) Λ δ U V XU XV q.1 q.2) := by
  let Q := History Unit (k+1)×Ω
  let K := fun (p : Inputs) (q : Q) => JointCutoffStep.childLeaf (L p ε k) Λ δ U V XU XV q.1 q.2
  have hK (p : Inputs) : Measurable (K p) := JointCutoffStep.childLeaf_measurable (L p ε k) Λ δ hU hV hXU hXV hδ
  have huQ : StronglyMeasurable (fun q : Q => u q.2) := hu.comp_measurable measurable_snd
  have hh := PastParameterDiagonal.stronglyMeasurable_diagonal (inferInstance : MeasurableSpace Q) le_rfl K hK huQ
    (fun q => childLeaf_parameter_continuous P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV hΛ ε k q.1 q.2)
  exact hh.measurable

include hsmall hU hV hXU hXV in
/-- Genuine full history/sample convergence of the moving literal
children for any actual measurable random reference input. The old
heat targets and full recursive word remain ε-dependent. -/
theorem literalChild_converges (hΛ : 0≤Λ) (u : Ω→Inputs) (hu : StronglyMeasurable u) (k : ℕ)
    (ν : Measure (History Unit (k+1))) [IsFiniteMeasure ν] (μ : Measure Ω) [IsFiniteMeasure μ] :
    Filter.Tendsto (fun ε : ℝ => ∫ q : History Unit (k+1)×Ω,
      |JointCutoffStep.childLeaf (L (u q.2) ε.toNNReal k) Λ δ U V XU XV q.1 q.2-
        JointCutoffStep.childLeaf (L (u q.2) 0 k) Λ δ U V XU XV q.1 q.2| ∂ν.prod μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,hCn,hC⟩ := (ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ (k+1)).norm_bound
  let g := fun (ε : ℝ≥0) (q : History Unit (k+1)×Ω) => JointCutoffStep.childLeaf (L (u q.2) ε k) Λ δ U V XU XV q.1 q.2
  have hm (ε : ℝ≥0) : AEStronglyMeasurable (g ε) (ν.prod μ) :=
    (childLeaf_diagonal_measurable P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV hU hV hXU hXV hΛ u hu ε k).aestronglyMeasurable
  have hb (ε : ℝ≥0) (q : History Unit (k+1)×Ω) : ‖g ε q‖≤C := hC (u q.2,(ε,q.1)) _
  have hc (q : History Unit (k+1)×Ω) : Continuous (fun ε => g ε q) := by
    have hh := JointLiteralChildLimit.continuous_literalChild (Base (u q.2)) δ hδ Λ U V XU XV k q.1 q.2
    exact hh
  exact FiniteParameterL1Limit.bounded_continuous_L1 (ν.prod μ) g hm hb hc

end SHE.ControlledReferenceLiteralChildren
