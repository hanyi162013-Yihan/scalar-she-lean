module

public import SHE.ControlledThetaRelativeCovariance
public import SHE.ControlledThetaRelativeDerivative
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

namespace SHE.ControlledThetaRelativeSecondScore
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance controlledThetaRelativeSecondScore_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaRelativeSecondScore_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaRelativeSecondScore_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm



local notation "Zero" => Base (0,(0,0))

/-- The full recursive covariance-row mark has its exact complete
relative Gaussian assignment representation on ONE history event for
all theta, past inputs, current means and range directions. The common
geometry on the right is independent of those reference parameters. -/
theorem score_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,(v:ℝ)≤q→q<(carrier (Base p) k).terminal h→
      ∀ direction mean : WordRecursion.State (n+k),
      direction∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q)).range→
      (∫ y,oldAverage (Base p) (oldProfile P Λ v p.2) k h (mean+y)*
        MeasurableGaussianScores.secondScore
          (fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q) direction y
        ∂multivariateGaussian 0 (fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q))=
      (1/2:ℝ)^k*((GaussianAssignmentBlocks.assignments (m:=k+1) (List.finRange k)).map
        (fun choices=>FullResidualAssignedMoments.fibreAverage P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
          (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
          (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean true
          (directions Zero ((carrier Zero k).observations.observations h) k h) direction
          (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) choices (F (rootParameter k h)))).sum := by
  filter_upwards [ControlledThetaCovarianceAssignments.full_residual_covariance_integral_all_parameters_ae
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaRelativeCovariance.assigned_covariance_integral_relative_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hrep hword
  intro p q hvq hqt direction mean hd
  rw [(hrep p q (v.2.trans hvq) hqt direction mean hd).2]
  have he (choices) := hword p q hvq hqt.le direction mean choices
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

end SHE.ControlledThetaRelativeSecondScore

