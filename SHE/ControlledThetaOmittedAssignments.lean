module

public import SHE.ControlledReferenceThetaGeometry
public import SHE.ControlledThetaPhysicalGeometry
public import SHE.ControlledFamilySupported
public import SHE.FullResidualChainAverage
public import SHE.ChainOmittedAssignments
public import SHE.ControlledThetaSupported

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ControlledThetaOmittedAssignments
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffInsertionCore SmoothCylinders UniformSmooth
  CutoffCarriers PhysicalChainArrays PhysicalScoreChain PhysicalParentGeometry
  ControlledOldIntervals ControlledReferenceWindows FixedOldScoreSupport ControlledFamilyProfileForest
  ProjectedUncutWord GaussianConvolution
open scoped NNReal
local instance controlledThetaOmittedAssignments_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaOmittedAssignments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaOmittedAssignments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "NME" => ControlledReferenceThetaGeometry.carrier_nodeTime_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "OME" => ControlledReferenceThetaGeometry.carrier_observations_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "RME" => ControlledReferenceThetaGeometry.row_eq P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- ONE original history event carries every actual omitted-leaf
assignment identity for every theta, past reference input, current mean
and erased leaf. No parameterwise a.e. substitution is made. -/
theorem omitted_average_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,∀ mean : WordRecursion.State (n+k),∀ j0 : Fin k,
      (∀ choices,Integrable (omittedAssignedWord (Base p) (oldProfile P Λ v p.2) k h mean choices j0)
        (fullAssignedMeasure (Base p) (oldProfile P Λ v p.2) k h q)) ∧
      omittedAverage (Base p) (oldProfile P Λ v p.2) k h q j0 mean=(1/2:ℝ)^k*
        ((GaussianAssignmentBlocks.assignments (m:=k+1) (List.finRange k)).map (fun choices=>∫ x,
          omittedAssignedWord (Base p) (oldProfile P Λ v p.2) k h mean choices j0 x
            ∂fullAssignedMeasure (Base p) (oldProfile P Λ v p.2) k h q)).sum := by
  filter_upwards [ControlledThetaSupported.physical_chain_all_parameters_ae
    P A hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p
  obtain ⟨chain,_,_,hp⟩:=hh p
  exact omitted_average_assignment_of_chain (Base p) (oldProfile P Λ v p.2) chain hp

end SHE.ControlledThetaOmittedAssignments
