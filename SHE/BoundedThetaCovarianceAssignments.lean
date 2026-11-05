module

public import SHE.ArbitraryCovarianceChain
public import SHE.ControlledReferenceThetaGeometry
public import SHE.ControlledThetaPhysicalGeometry
public import SHE.ControlledFamilySupported
public import SHE.FullResidualChainAverage
public import SHE.ChainCovarianceAssignments
public import SHE.ControlledThetaSupported

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.BoundedThetaCovarianceAssignments
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffInsertionCore SmoothCylinders UniformSmooth
  CutoffCarriers PhysicalChainArrays PhysicalScoreChain PhysicalParentGeometry
  ControlledOldIntervals ControlledReferenceWindows FixedOldScoreSupport ControlledFamilyProfileForest
  ProjectedUncutWord GaussianConvolution
open scoped NNReal
local instance controlledThetaCovarianceAssignments_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaCovarianceAssignments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaCovarianceAssignments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State 1=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "NME" => ControlledReferenceThetaGeometry.carrier_nodeTime_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "OME" => ControlledReferenceThetaGeometry.carrier_observations_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "RME" => ControlledReferenceThetaGeometry.row_eq P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- ONE original history event carries the exact second-score old
assignment identity simultaneously for every original past-input pair,
endpoint baseline, current mean and arbitrary positive residual law.
This includes convex intermediate laws and the true newest endpoint. -/
theorem integral_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,
      ∀ (B : Matrix (Fin (1+k)) (Fin (1+k)) ℝ),B.PosSemidef →
      ∀ d z : WordRecursion.State (1+k),d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) B).range →
      let old:=oldProfile P Λ v p.2
      let νG:=(Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (1+k))
        (covariances (Base p) ((carrier (Base p) k).observations.observations h) old k h j))).prod
          (multivariateGaussian 0 B)
      (∀ choices,MemLp (ArbitraryResidualCovariance.assignedWord (Base p) old k h B d z choices) 2 νG) ∧
      (∫ y,oldAverage (Base p) old k h (z+y)*MeasurableGaussianScores.secondScore B d y
        ∂multivariateGaussian 0 B)=
      (1/2:ℝ)^k*((GaussianAssignmentBlocks.assignments (m:=k+1) (List.finRange k)).map
        (fun choices=>∫ x,ArbitraryResidualCovariance.assignedWord (Base p) old k h B d z choices x ∂νG)).sum := by
  filter_upwards [ControlledThetaSupported.physical_chain_all_parameters_ae
    P A hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p B hB d z hd
  obtain ⟨chain,_,_,hp⟩:=hh p
  exact ArbitraryResidualCovariance.integral_of_chain (Base p) (oldProfile P Λ v p.2) chain hp B hB d z hd

end SHE.BoundedThetaCovarianceAssignments
