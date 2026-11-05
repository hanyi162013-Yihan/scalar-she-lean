module

public import SHE.ControlledThetaRelativeWord
public import SHE.ControlledThetaOmittedAssignments
public import SHE.OmittedWordPhysicalBridge
public import SHE.OmittedVaryingMoments
public import SHE.ControlledThetaRelativeDerivative
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

namespace SHE.ControlledThetaRelativeOmitted
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance controlledThetaRelativeOmitted_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaRelativeOmitted_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaRelativeOmitted_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm


/-- Exact relative-law identification for an erased baseline leaf.
Assignments differentiating the erased constant factor vanish identically. -/
theorem assigned_omitted_integral_relative_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop ≤ (Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,(v:ℝ) ≤ q → q ≤ (carrier (Base p) k).terminal h →
      ∀ mean : WordRecursion.State (n+k),∀ choices,∀ j0 : Fin k,
      (∫ x,omittedAssignedWord (Base p) (oldProfile P Λ v p.2) k h mean choices j0 x
        ∂fullAssignedMeasure (Base p) (oldProfile P Λ v p.2) k h q)=
      if GaussianAssignmentBlocks.block choices j0.succ=[] then
        OmittedAssignedMoments.fibreAverage P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
          (fun i=>stops (Base p) k h i-(v:ℝ)) (fun i=>targets (Base p) k h i-(v:ℝ))
          (centers (Base p) k h) (fun j=>lower (Base p) k h j-(v:ℝ))
          (fun j=>upper (Base p) k h j-(v:ℝ)) mean
          (directions (Base p) ((carrier (Base p) k).observations.observations h) k h)
          (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) choices j0
          (F (rootParameter k h)) else 0 := by
  filter_upwards [ControlledThetaStoppedCovariance.relative_all_parameters_ae
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p q hvq hqt mean choices j0
  have hq : 0 ≤ q:=v.2.trans hvq
  have hcov:=ControlledThetaRelativeWord.old_covariance_relative P hA Λ v b hvb Z htarget hstop F hF hFm p k h hvq hqt
  have hres:=hh p q hq hqt
  have hbase : baseline (Base p) k h=(fun j=>ControlledProfile.profile P Λ p.2.1 p.2.2
      (p.1,(targets (Base p) k h (leafIndex k (fun i=>i) j)-(v:ℝ),
        centers (Base p) k h (leafIndex k (fun i=>i) j)))) :=
    funext (ControlledThetaRelativeWord.baseline_relative P hA Λ v b hvb Z htarget hstop F hF hFm p k h)
  simp_rw [omitted_assigned_eq_word]
  by_cases hb : GaussianAssignmentBlocks.block choices j0.succ=[]
  · simp only [ite_eq_left hb]
    unfold fullAssignedMeasure OmittedAssignedMoments.fibreAverage
    rw [hcov,hres,hbase]
    rfl
  · simp only [ite_eq_right hb,integral_zero]

local notation "Zero" => Base (0,(0,0))

/-- The literal full omitted-baseline average is a finite sum of the
relative assigned Gaussian words on one common history event. Original
full profile baselines and the zero erased-leaf blocks are retained. -/
theorem omitted_average_relative_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop ≤ (Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,(v:ℝ) ≤ q → q ≤ (carrier (Base p) k).terminal h →
      ∀ mean : WordRecursion.State (n+k),∀ j0 : Fin k,
      omittedAverage (Base p) (oldProfile P Λ v p.2) k h q j0 mean=
      (1/2:ℝ)^k*((GaussianAssignmentBlocks.assignments (m:=k+1) (List.finRange k)).map
        (fun choices=>if GaussianAssignmentBlocks.block choices j0.succ=[] then
          OmittedAssignedMoments.fibreAverage P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
            (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
            (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean
            (directions Zero ((carrier Zero k).observations.observations h) k h)
            (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) choices j0
            (F (rootParameter k h)) else 0)).sum := by
  filter_upwards [ControlledThetaOmittedAssignments.omitted_average_all_parameters_ae
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    assigned_omitted_integral_relative_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hrep hword
  intro p q hvq hqt mean j0
  rw [(hrep p q mean j0).2]
  have he (choices) := hword p q hvq hqt mean choices j0
  have hdir : directions (Base p) ((carrier (Base p) k).observations.observations h) k h=
      directions Zero ((carrier Zero k).observations.observations h) k h := by
    rw [ControlledReferenceThetaGeometry.carrier_observations_eq
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h]
    exact ControlledThetaPhysicalGeometry.directions_eq
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) _ k h
  simp only [ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
    ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
    ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
    ControlledThetaPhysicalGeometry.lower_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
    ControlledThetaPhysicalGeometry.upper_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,hdir] at he
  simp_rw [he]

end SHE.ControlledThetaRelativeOmitted
