module

public import SHE.ControlledThetaStoppedCovariance
public import SHE.ControlledThetaAssigned
public import SHE.VaryingFullResidualMoments
public import SHE.ControlledThetaSupported
public import SHE.FullResidualStoppedCovariance
public import SHE.ControlledProfileTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledThetaRelativeWord
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance controlledThetaRelativeWord_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaRelativeWord_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaRelativeWord_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm


/-- The actual fixed old matrices of the entire theta/past-input family
are exactly the physical relative-age matrices. This is pointwise in
all parameters, not an a.e. substitution theorem. -/
theorem old_covariance_relative (p : ℝ×Inputs) (k : ℕ) (h : History X k)
    {q : ℝ} (hvq : (v:ℝ) ≤ q) (hqt : q ≤ (carrier (Base p) k).terminal h) :
    covariances (Base p) ((carrier (Base p) k).observations.observations h)
      (oldProfile P Λ v p.2) k h=
    OldIntervalCovariance.familyCovariance
      (fun i=>stops (Base p) k h i-(v:ℝ)) (fun i=>targets (Base p) k h i-(v:ℝ))
      (centers (Base p) k h) (referenceProfile P Λ p.2.1 p.2.2)
      (fun j=>lower (Base p) k h j-(v:ℝ)) (fun j=>upper (Base p) k h j-(v:ℝ)) := by
  have hq : 0 ≤ q:=v.2.trans hvq
  funext j
  have he:=ControlledProfileTimeShift.oldCovariance_translation P Λ (v:ℝ) p.2.1 p.2.2 v.2
    (fun i=>stops (Base p) k h i-(v:ℝ)) (fun i=>targets (Base p) k h i-(v:ℝ))
    (centers (Base p) k h) (fun j=>lower (Base p) k h j-(v:ℝ))
    (fun j=>upper (Base p) k h j-(v:ℝ))
    (fun j=>sub_nonneg.mpr (hvq.trans (hqt.trans (terminal_le_lower (Base p) k h j)))) j
  have hc : ControlledProfileTimeShift.oldProfile P Λ v p.2.1 p.2.2=oldProfile P Λ v p.2:=rfl
  simp only [hc,sub_add_cancel] at he
  rw [CoveredControlledLaw.old_family_eq (Base p) (oldProfile P Λ v p.2) k h hq hqt] at he
  exact he

/-- Every original centered baseline keeps its relative native age,
including after arbitrary original-past-input substitution. -/
theorem baseline_relative (p : ℝ×Inputs) (k : ℕ) (h : History X k) (j : Fin k) :
    baseline (Base p) k h j=ControlledProfile.profile P Λ p.2.1 p.2.2
      (p.1,(targets (Base p) k h (leafIndex k (fun i=>i) j)-(v:ℝ),
        centers (Base p) k h (leafIndex k (fun i=>i) j))) := by
  unfold targets centers
  rw [leaf_observation (Base p) k h j]
  rfl

/-- Exact identification of the literal physical assigned integral with
the variable-law Gaussian average used by the conditional native moment
theorem, on ONE history event for ALL theta and past inputs. -/
theorem assigned_integral_relative_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop ≤ (Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,(v:ℝ) ≤ q → q ≤ (carrier (Base p) k).terminal h →
      ∀ direction mean : WordRecursion.State (n+k),∀ choices,
      (∫ x,fullAssignedWord (Base p) (oldProfile P Λ v p.2) k h q direction mean choices x
        ∂fullAssignedMeasure (Base p) (oldProfile P Λ v p.2) k h q)=
      FullResidualAssignedMoments.fibreAverage P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
        (fun i=>stops (Base p) k h i-(v:ℝ)) (fun i=>targets (Base p) k h i-(v:ℝ))
        (centers (Base p) k h) (fun j=>lower (Base p) k h j-(v:ℝ))
        (fun j=>upper (Base p) k h j-(v:ℝ)) mean false
        (directions (Base p) ((carrier (Base p) k).observations.observations h) k h) direction
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) choices (F (rootParameter k h)) := by
  filter_upwards [ControlledThetaStoppedCovariance.relative_all_parameters_ae
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p q hvq hqt direction mean choices
  have hq : 0 ≤ q:=v.2.trans hvq
  have hcov:=old_covariance_relative P hA Λ v b hvb Z htarget hstop F hF hFm p k h hvq hqt
  have hres:=hh p q hq hqt
  have hbase : baseline (Base p) k h=(fun j=>ControlledProfile.profile P Λ p.2.1 p.2.2
      (p.1,(targets (Base p) k h (leafIndex k (fun i=>i) j)-(v:ℝ),
        centers (Base p) k h (leafIndex k (fun i=>i) j)))) :=
    funext (baseline_relative P hA Λ v b hvb Z htarget hstop F hF hFm p k h)
  unfold fullAssignedWord fullAssignedMeasure FullResidualAssignedMoments.fibreAverage
  rw [hcov,hres,hbase]
  rfl

end SHE.ControlledThetaRelativeWord
