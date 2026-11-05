module

public import SHE.BoundedThetaRelativeWord
public import SHE.BoundedThetaCovarianceAssignments
public import SHE.BoundedCompleteGaussianWord
public import SHE.RelativeHistoryGeometry
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

namespace SHE.BoundedThetaRelativeSecondScore
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
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State 1=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm



local notation "Zero" => Base (0,(0,0))

def covariance (p : ℝ×Inputs) (k : ℕ) (h : History X k) (q : ℝ)
    (c : StoppedGaussianFeatures.Domain→ℝ) :=
  StoppedGaussianFeatures.stoppedCovariance
    (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
    (BoundedWindowDecomposition.residual P Λ p.2.1 p.2.2
      (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) c) (q-(v:ℝ))

local notation "Cov"=>covariance P hA Λ v b hvb Z htarget hstop F hF hFm

/-- One original event identifies the COMPLETE covariance second-score
word under ANY bounded elliptic intermediate future law with its exact
relative-array Gaussian assignment sum. Own endpoint baselines are fixed
at p.1; q=terminal and random past substitution are both allowed. -/
theorem score_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,(v:ℝ)≤q→q≤(carrier Zero k).terminal h→
      ∀ (c : StoppedGaussianFeatures.Domain→ℝ),Measurable c → (∀ z,P.lower≤c z ∧ c z≤P.upper) →
      ∀ direction mean : WordRecursion.State (1+k),
      direction∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (Cov p k h q c)).range →
      (∫ y,oldAverage (Base p) (oldProfile P Λ v p.2) k h (mean+y)*
        MeasurableGaussianScores.secondScore (Cov p k h q c) direction y
        ∂multivariateGaussian 0 (Cov p k h q c))=
      BoundedCompleteGaussianWord.value P Λ p.2.1 p.2.2 c p.1 (q-(v:ℝ))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean true
        (directions Zero ((carrier Zero k).observations.observations h) k h) direction
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h)) := by
  filter_upwards [BoundedThetaCovarianceAssignments.integral_all_parameters_ae
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hrep
  intro p q hvq hqt c hc hcb direction mean hd
  let B:=Cov p k h q c
  have hgeom (i) : stops Zero k h i-(v:ℝ)≤targets Zero k h i-(v:ℝ):=
    sub_le_sub_right ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _
  have hdisjoint (j l) (hne : j≠l) : upper Zero k h j-(v:ℝ)≤lower Zero k h l-(v:ℝ) ∨
      upper Zero k h l-(v:ℝ)≤lower Zero k h j-(v:ℝ):=
    RelativeHistoryGeometry.relative_disjoint Zero k h j l hne
  have hB : B.PosSemidef:=StoppedCovarianceSplit.covariance_posSemidef _ _ _ hgeom (q-(v:ℝ))
    (BoundedWindowDecomposition.residual_measurable P Λ p.2.1 p.2.2 _ _ c hc)
    (fun z=>⟨(half_pos P.lower_pos).le.trans
      (BoundedWindowDecomposition.residual_bounds P Λ p.2.1 p.2.2 _ _ hdisjoint c hcb z).1,
      (BoundedWindowDecomposition.residual_bounds P Λ p.2.1 p.2.2 _ _ hdisjoint c hcb z).2⟩)
  rw [(hrep p B hB direction mean hd).2]
  have hqt' : q≤(carrier (Base p) k).terminal h:=by
    rwa [ControlledReferenceThetaGeometry.carrier_terminal_eq
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h]
  have he (choices):=BoundedThetaRelativeWord.assigned_relative P hA Λ v b hvb Z htarget hstop F hF hFm
    p k h hvq hqt' c direction mean choices
  dsimp only at he
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
  unfold BoundedCompleteGaussianWord.value
  apply congrArg (fun a : ℝ=>(1/2:ℝ)^k*a)
  apply congrArg List.sum
  apply List.map_congr_left
  intro choices _
  convert! he choices using 1

end SHE.BoundedThetaRelativeSecondScore
