module
public import SHE.ControlledThetaRelativeSecondScore
public import SHE.PhysicalHessianChain
public import SHE.PointwiseCompleteGaussianWord

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ControlledHessianRelative
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution
open scoped NNReal
local instance controlledHessianRelative_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledHessianRelative_circleSigma : MeasurableSpace CircleL2:=borel _
local instance controlledHessianRelative_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
attribute [local irreducible] WordRecursion.directionalSecond GaussianConvolution.gaussianAverage UncutSmoothWords.test
variable (P:CanonicalCovariance.ProfileParameters)(ha:BoundedSmooth P.coefficient)
variable (Λ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable {X:Type}[MeasurableSpace X](Z:VariableObservations.Family X 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient ha Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))

/-- Literal recursive Hessian equals the complete relative-coordinate
second-score word, on one event before all past inputs and current means.
The newest physical coefficient error may therefore remain outside it. -/
theorem all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X)[IsFiniteMeasure ρ](k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient ha Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q<(carrier (Base p) k).terminal h→
      ∀d z:WordRecursion.State (1+k),d∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q)).range→
      WordRecursion.directionalSecond
        (gaussianAverage (WordRecursion.covariance
          (referenceData P P.coefficient ha Λ p.1 v b hvb p.2).reference
          ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
            (UncutSmoothWords.test (Base p) k h)) z d=
      PointwiseCompleteGaussianWord.value P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) z true
        (directions Zero ((carrier Zero k).observations.observations h) k h) d
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h)) := by
  filter_upwards [ControlledThetaSupported.physical_chain_all_parameters_ae
      P P.coefficient ha Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaRelativeSecondScore.score_all_parameters_ae
      P ha Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hs hrep
  intro p q hvq hqt d z hd
  obtain ⟨chain,hchain,_,hphysical⟩:=hs p
  have hc:Measurable (oldProfile P Λ v p.2):=
    (coefficient_section_measurable P Λ 0 v p.2).const_mul (fraction P)
  have hR(r:StoppedGaussianFeatures.Domain):P.lower≤
      (referenceData P P.coefficient ha Λ p.1 v b hvb p.2).reference r:=
    (coefficient_bounds P Λ p.1 v p.2 r).1
  rw [hessian_second_score_of_chain (Base p) (oldProfile P Λ v p.2) hc P.lower_pos hR
    hages k h chain hchain hphysical q (v.2.trans hvq) hqt d z hd]
  exact hrep p q hvq hqt d z hd

end SHE.ControlledHessianRelative
