module

public import SHE.ControlledThetaRelativeWord
public import SHE.BoundedCompleteGaussianWord
public import SHE.ArbitraryResidualCovariance
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

namespace SHE.BoundedThetaRelativeWord
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
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State 1=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm


/-- The actual old assigned word under ANY intermediate residual law
has exactly its relative-age own-baseline Gaussian form. This identity
holds pointwise before random past substitution and at q=terminal. -/
theorem assigned_relative (p : ℝ×Inputs) (k : ℕ) (h : History X k)
    {q : ℝ} (hvq : (v:ℝ)≤q) (hqt : q≤(carrier (Base p) k).terminal h)
    (c : StoppedGaussianFeatures.Domain→ℝ) (direction mean : WordRecursion.State (1+k))
    (choices : List (Fin k×Fin (k+1))) :
    let σ:=fun i=>stops (Base p) k h i-(v:ℝ)
    let target:=fun i=>targets (Base p) k h i-(v:ℝ)
    let center:=centers (Base p) k h
    let lo:=fun j=>lower (Base p) k h j-(v:ℝ)
    let hi:=fun j=>upper (Base p) k h j-(v:ℝ)
    let B:=StoppedGaussianFeatures.stoppedCovariance σ target center
      (BoundedWindowDecomposition.residual P Λ p.2.1 p.2.2 lo hi c) (q-(v:ℝ))
    let old:=oldProfile P Λ v p.2
    (∫ x,ArbitraryResidualCovariance.assignedWord (Base p) old k h B direction mean choices x
      ∂(Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (1+k))
        (covariances (Base p) ((carrier (Base p) k).observations.observations h) old k h j))).prod
          (multivariateGaussian 0 B))=
    BoundedResidualAssignedMoments.fibreAverage P Λ p.2.1 p.2.2 c p.1 (q-(v:ℝ)) σ target center lo hi
      mean true (directions (Base p) ((carrier (Base p) k).observations.observations h) k h) direction
      (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) choices (F (rootParameter k h)) := by
  intro σ target center lo hi B old
  have hcov:=ControlledThetaRelativeWord.old_covariance_relative P hA Λ v b hvb Z htarget hstop F hF hFm p k h hvq hqt
  have hbase : baseline (Base p) k h=(fun j=>ControlledProfile.profile P Λ p.2.1 p.2.2
      (p.1,(targets (Base p) k h (leafIndex k (fun i=>i) j)-(v:ℝ),
        centers (Base p) k h (leafIndex k (fun i=>i) j)))) :=
    funext (ControlledThetaRelativeWord.baseline_relative P hA Λ v b hvb Z htarget hstop F hF hFm p k h)
  unfold ArbitraryResidualCovariance.assignedWord BoundedResidualAssignedMoments.fibreAverage
  dsimp only [old]
  rw [hcov,hbase]
  rfl

end SHE.BoundedThetaRelativeWord
