module

public import SHE.ControlledThetaRelativeWord
public import SHE.ControlledThetaCovarianceAssignments
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

namespace SHE.ControlledThetaRelativeCovariance
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance controlledThetaRelativeCovariance_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaRelativeCovariance_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaRelativeCovariance_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm


/-- Exact relative-law identification for the actual fresh SECOND score,
shared by every interpolation and original past-input parameter. -/
theorem assigned_covariance_integral_relative_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop ≤ (Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,(v:ℝ) ≤ q → q ≤ (carrier (Base p) k).terminal h →
      ∀ direction mean : WordRecursion.State (n+k),∀ choices,
      (∫ x,fullCovarianceAssignedWord (Base p) (oldProfile P Λ v p.2) k h q direction mean choices x
        ∂fullAssignedMeasure (Base p) (oldProfile P Λ v p.2) k h q)=
      FullResidualAssignedMoments.fibreAverage P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
        (fun i=>stops (Base p) k h i-(v:ℝ)) (fun i=>targets (Base p) k h i-(v:ℝ))
        (centers (Base p) k h) (fun j=>lower (Base p) k h j-(v:ℝ))
        (fun j=>upper (Base p) k h j-(v:ℝ)) mean true
        (directions (Base p) ((carrier (Base p) k).observations.observations h) k h) direction
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) choices (F (rootParameter k h)) := by
  filter_upwards [ControlledThetaStoppedCovariance.relative_all_parameters_ae
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p q hvq hqt direction mean choices
  have hq : 0 ≤ q:=v.2.trans hvq
  have hcov:=ControlledThetaRelativeWord.old_covariance_relative P hA Λ v b hvb Z htarget hstop F hF hFm p k h hvq hqt
  have hres:=hh p q hq hqt
  have hbase : baseline (Base p) k h=(fun j=>ControlledProfile.profile P Λ p.2.1 p.2.2
      (p.1,(targets (Base p) k h (leafIndex k (fun i=>i) j)-(v:ℝ),
        centers (Base p) k h (leafIndex k (fun i=>i) j)))) :=
    funext (ControlledThetaRelativeWord.baseline_relative P hA Λ v b hvb Z htarget hstop F hF hFm p k h)
  unfold fullCovarianceAssignedWord fullAssignedMeasure FullResidualAssignedMoments.fibreAverage
  rw [hcov,hres,hbase]
  rfl


end SHE.ControlledThetaRelativeCovariance
