module

public import SHE.ControlledThetaRelativeWord
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

namespace SHE.ControlledThetaRelativeDerivative
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance controlledThetaRelativeDerivative_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaRelativeDerivative_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaRelativeDerivative_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm



local notation "Zero" => Base (0,(0,0))

theorem stops_eq (p p' : ℝ×Inputs) (k : ℕ) (h : History X k) :
    stops (Base p) k h=stops (Base p') k h := by
  unfold stops initialTerminal
  rw [ControlledReferenceThetaGeometry.carrier_observations_eq
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p p' k h]
  rfl

theorem targets_eq (p p' : ℝ×Inputs) (k : ℕ) (h : History X k) :
    targets (Base p) k h=targets (Base p') k h := by
  unfold targets
  rw [ControlledReferenceThetaGeometry.carrier_observations_eq
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p p' k h]

theorem centers_eq (p p' : ℝ×Inputs) (k : ℕ) (h : History X k) :
    centers (Base p) k h=centers (Base p') k h := by
  unfold centers
  rw [ControlledReferenceThetaGeometry.carrier_observations_eq
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p p' k h]

/-- The exact actual recursive derivative is the complete relative-age
assigned Gaussian sum on one history event, uniformly in every theta,
past input and current mean. All time/center/direction arrays on the
right are named using one fixed zero-input reference only because the
physical geometry is exactly independent of both varying parameters. -/
theorem derivative_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop ≤ (Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,(v:ℝ) ≤ q → q<(carrier (Base p) k).terminal h →
      ∀ direction mean : WordRecursion.State (n+k),
      direction∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q)).range →
      fderiv ℝ (GaussianConvolution.gaussianAverage (WordRecursion.covariance
        (referenceData P P.coefficient hA Λ p.1 v b hvb p.2).reference
        ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
        (UncutSmoothWords.test (Base p) k h)) mean direction=
      (1/2:ℝ)^k*((GaussianAssignmentBlocks.assignments (m:=k+1) (List.finRange k)).map
        (fun choices=>FullResidualAssignedMoments.fibreAverage P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
          (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
          (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean false
          (directions Zero ((carrier Zero k).observations.observations h) k h) direction
          (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) choices (F (rootParameter k h)))).sum := by
  filter_upwards [ControlledThetaAssigned.full_residual_integral_all_parameters_ae
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaRelativeWord.assigned_integral_relative_all_parameters_ae
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
  simp only [stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
    targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
    centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
    ControlledThetaPhysicalGeometry.lower_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
    ControlledThetaPhysicalGeometry.upper_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,hdir] at he
  simp_rw [he]

end SHE.ControlledThetaRelativeDerivative
