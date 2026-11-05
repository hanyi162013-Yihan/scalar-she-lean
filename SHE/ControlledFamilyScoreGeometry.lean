module

public import SHE.HistoryGeometry
public import SHE.UniformPhysicalProfileForest
public import SHE.ControlledReferenceFamilyBounds
public import SHE.ControlledReferenceLevel
public import SHE.UncutSmoothWords
public import SHE.ControlledReferenceFamilyLevel
public import SHE.UncutHistoryMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 150000
noncomputable section

namespace SHE.ControlledFamilyScoreGeometry
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledFamilyScoreGeometry_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyScoreGeometry_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyScoreGeometry_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n => F q.1 q.2))


open CutoffCarriers PhysicalChainArrays PhysicalScoreChain PhysicalParentGeometry


theorem lower_eq (p p' : Inputs) (k : ℕ) (h : History X k) :
    lower ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) k h=lower ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p') k h := by
  exact HistoryGeometry.lower_eq (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p) (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p') (ControlledReferenceFamilyBounds.carrier_nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') k h

theorem upper_eq (p p' : Inputs) (k : ℕ) (h : History X k) :
    upper ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) k h=upper ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p') k h := by
  exact HistoryGeometry.upper_eq (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p) (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p') (ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') k h

theorem interior_iff (p p' : Inputs) (k : ℕ) (h : History X k×(ℝ×HeatCircle)) :
    Interior ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) k h↔Interior ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p') k h := by
  change ((v:ℝ)<h.2.1 ∧ h.2.1<(carrier ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) k).terminal h.1)↔
    ((v:ℝ)<h.2.1 ∧ h.2.1<(carrier ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p') k).terminal h.1)
  rw [(ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p p' k h.1]

theorem direction_eq {N : ℕ} (p p' : Inputs) (Q : Fin N→Observation)
    (k : ℕ) (h : History X k×(ℝ×HeatCircle)) :
    PhysicalScoreChain.direction ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) Q k h=PhysicalScoreChain.direction ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p') Q k h := by
  exact HistoryGeometry.direction_eq (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p) (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p') (interior_iff P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') (ControlledReferenceFamilyBounds.carrier_nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') Q k h

theorem directions_eq {N : ℕ} (p p' : Inputs) (Q : Fin N→Observation) (k : ℕ) (h : History X k) :
    directions ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) Q k h=directions ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p') Q k h := by
  exact HistoryGeometry.directions_eq (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p) (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p') (interior_iff P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') (ControlledReferenceFamilyBounds.carrier_nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') Q k h

theorem covariances_eq {N : ℕ} (p p' : Inputs) (Q : Fin N→Observation) (c : Domain→ℝ)
    (k : ℕ) (h : History X k) :
    covariances ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) Q c k h=covariances ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p') Q c k h := by
  exact HistoryGeometry.covariances_eq (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p) (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p') (lower_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') (upper_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') Q c k h

theorem scoreProduct_eq {N : ℕ} (p p' : Inputs) (Q : Fin N→Observation) (c : Domain→ℝ)
    (k : ℕ) (h : History X k) :
    scoreProduct ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) Q c k h=scoreProduct ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p') Q c k h := by
  exact HistoryGeometry.scoreProduct_eq (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p) (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p') (lower_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') (upper_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') Q (directions_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p' Q) c k h

theorem strict_iff (p p' : Inputs) (k : ℕ) (h : History X k) :
    StrictHistory ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) k h↔StrictHistory ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p') k h := by
  exact HistoryGeometry.strict_iff (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p) (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p') (interior_iff P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') k h

theorem small_iff (p p' : Inputs) (H : ℕ→ℝ) (k : ℕ) (h : History X k) :
    SmallHistory ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) H k h↔SmallHistory ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p') H k h := by
  exact HistoryGeometry.small_iff (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p) (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p') (ControlledReferenceFamilyBounds.carrier_nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') (ControlledReferenceFamilyBounds.carrier_observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') H k h

theorem timeWeight_eq (p p' : Inputs) (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (h : History X k) :
    timeWeight ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p) ell C k h=timeWeight ((ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm) p') ell C k h := by
  exact HistoryGeometry.timeWeight_eq (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p) (ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm p') (ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') (ControlledReferenceFamilyBounds.carrier_nodeTime_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p p') ell C k h

theorem historyMeasure_eq (p p' : Inputs) (μ : Measure X) (k : ℕ) :
    historyMeasure (ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb p) μ k=
      historyMeasure (ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb p') μ k := by
  exact HistoryGeometry.historyMeasure_eq (X:=X) (R:=ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb p) (R':=ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb p') rfl rfl μ k

end SHE.ControlledFamilyScoreGeometry
