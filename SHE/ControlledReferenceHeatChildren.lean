module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.ControlledReferenceRecursiveBackward
public import SHE.ControlledReferenceRecursiveFields
public import SHE.JointLiteralChildLimit
public import SHE.ControlledReferenceLiteralChildren
public import SHE.FiniteParameterL1Limit
public import SHE.PastParameterDiagonal
public import SHE.GaussianParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceHeatChildren
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open Filter Topology
open scoped NNReal
local instance controlledReferenceHeatChildren_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceHeatChildren_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceHeatChildren_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

local instance controlledReferenceHeatChildren_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)
variable (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)
local notation "Base" => ControlledReferenceLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF

include hsmall in
theorem heatChild_parameter_continuous (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ)
    (h : History Unit k×(ℝ×HeatCircle)) (ω : Ω) :
    Continuous (fun p : Inputs => JointCutoffStep.heatChildLeaf (L p ε k) Λ δ U V XU XV ε h ω) := by
  have hh := ControlledReferenceRecursiveFields.continuous_leaf P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall
    U V XU XV hΛ ε (k+1) h ω
  exact hh

include hsmall hU hV hXU hXV in
theorem heatChild_diagonal_measurable (hΛ : 0≤Λ) (u : Ω→Inputs) (hu : StronglyMeasurable u) (ε : ℝ≥0) (k : ℕ) :
    Measurable (fun q : History Unit (k+1)×Ω => JointCutoffStep.heatChildLeaf (L (u q.2) ε k) Λ δ U V XU XV ε q.1 q.2) := by
  let Q := History Unit (k+1)×Ω
  let K := fun (p : Inputs) (q : Q) => JointCutoffStep.heatChildLeaf (L p ε k) Λ δ U V XU XV ε q.1 q.2
  have hK (p : Inputs) : Measurable (K p) := JointCutoffStep.heatChildLeaf_measurable (L p ε k) Λ δ hU hV hXU hXV hδ ε.2
  have huQ : StronglyMeasurable (fun q : Q => u q.2) := hu.comp_measurable measurable_snd
  have hh := PastParameterDiagonal.stronglyMeasurable_diagonal (inferInstance : MeasurableSpace Q) le_rfl K hK huQ
    (fun q => heatChild_parameter_continuous P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV hΛ ε k q.1 q.2)
  exact hh.measurable

/-- Bounds for BOTH actual heated and literal newest children, uniform
over the random-reference inputs, all heat ages and finite histories. -/
theorem children_bound (k : ℕ) : ∃ C : ℝ,0≤C ∧ ∀ (p : Inputs) (ε : ℝ≥0) h ω,
    ‖JointCutoffStep.heatChildLeaf (L p ε k) Λ δ U V XU XV ε h ω‖≤C ∧
      ‖JointCutoffStep.childLeaf (L p ε k) Λ δ U V XU XV h ω‖≤C := by
  obtain ⟨C,hCn,hC⟩ := (ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ (k+1)).norm_bound
  exact ⟨C,hCn,fun p ε h ω => ⟨hC (p,(ε,h)) _,hC (p,(ε,h)) _⟩⟩

end SHE.ControlledReferenceHeatChildren
