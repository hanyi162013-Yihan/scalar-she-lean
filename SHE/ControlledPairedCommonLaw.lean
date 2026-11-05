module

public import SHE.ControlledTerminalPairedFields
public import SHE.PairedOldGaussianDifference
public import SHE.ControlledThetaSupported
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledRelativeScoreForest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.ControlledPairedCommonLaw
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalScoreChain
  ControlledFamilyProfileForest SmoothCylinders UniformSmooth CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance controlledTerminalPairedRelative_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledTerminalPairedRelative_circleSigma : MeasurableSpace CircleL2:=borel _
local instance controlledTerminalPairedRelative_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters) (hA:BoundedSmooth P.coefficient)
variable (Λ:ℝ) (v b:ℝ≥0) (hvb:v≤b)
variable {X:Type} [MeasurableSpace X] (Z:VariableObservations.Family X 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (Function.uncurry F))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "OME" => ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "SE" => ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TE" => ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "CE" => ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LE" => ControlledThetaPhysicalGeometry.lower_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "UE" => ControlledThetaPhysicalGeometry.upper_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

open GaussianIncrement GaussianConvolution GaussianAssignmentBlocks GaussianCoordinates
  GaussianVectorFractions
open scoped BigOperators

/-- The common old Gaussian kernel, keeping the actual own baseline. -/
def rawOld (p:Inputs) (k:ℕ) (h:History X k) (α:ℝ):WordRecursion.State (1+k)→ℝ:=
  let L:=Base (0,p)
  let A:=covariances L ((carrier L k).observations.observations h) (oldProfile P Λ v p) k h
  let D:=directions L ((carrier L k).observations.observations h) k h
  WeightedBorelAverage.average (Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (1+k)) (A j)))
    (fun x=>∏j,MeasurableGaussianScores.secondScore (A j) (D j) (x j)) (fun x=>∑j,x j)
    (VectorAssignmentIdentity.raw P.coefficient (F (rootParameter k h))
      (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (baseline (Base (α,p)) k h))

local notation "Raw"=>rawOld P hA Λ v b hvb Z htarget hstop F hF hFm

/-- Changing the own baseline does not change the original fixed old
Gaussian fractions or directions. The factor2^(-k) is retained exactly. -/
theorem old_average_common (p:Inputs) (k:ℕ) (h:History X k) (α:ℝ)
    (mean:WordRecursion.State (1+k)):
    oldAverage (Base (α,p)) (oldProfile P Λ v p) k h mean=(1/2:ℝ)^k*Raw p k h α mean:=by
  unfold oldAverage rawOld
  rw [word_eq_raw,OME (α,p) (0,p) k h,
    ControlledThetaPhysicalGeometry.covariances_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
      (α,p) (0,p) _ (oldProfile P Λ v p) k h,
    ControlledThetaPhysicalGeometry.directions_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
      (α,p) (0,p) _ k h]
  exact WeightedBorelAverage.const_mul _ _ _ _ _ _

/-- The original common-future-law endpoint difference is the sum of
ALL normalized paired slots. Every Gaussian applicability hypothesis is
derived on one original-history event, before choosing any past input. -/
theorem difference_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:Inputs,∀newMean oldMean:WordRecursion.State (1+k),
      ∀A0 ν χ:ℝ,0≤A0 → 0≤ν → 0≤χ → χ≤P.exponent →
      (∀j,j≤k+1→∀z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j) →
      let L:=Base (0,p)
      let B:=fullResidualCovariance L (oldProfile P Λ v p) k h ((carrier L k).terminal h)
      gaussianAverage B (oldAverage (Base (1,p)) (oldProfile P Λ v p) k h) newMean-
        gaussianAverage B (oldAverage L (oldProfile P Λ v p) k h) oldMean=
      (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices=>
        ∑i,PairedAssignedTelescope.sources P choices (rootSelector k (fun j=>j)) (leafIndex k (fun j=>j))
          newMean oldMean (baseline (Base (1,p)) k h) (baseline L k h) ν χ i*
          ControlledTerminalPairedFields.average P hA Λ v b hvb Z htarget hstop F hF hFm
            k p h newMean oldMean choices ν χ i)).sum:=by
  filter_upwards [ControlledThetaSupported.physical_chain_all_parameters_ae
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p newMean oldMean A0 ν χ hA0 hν hχ hχβ hb L B
  obtain ⟨chain,_,_,hp⟩:=hh (0,p)
  let A:=covariances L ((carrier L k).observations.observations h) (oldProfile P Λ v p) k h
  let D:=directions L ((carrier L k).observations.observations h) k h
  have hPSD(j:Fin k):(A j).PosSemidef:=by
    rw [show A=chain.old from (Physical.old_eq L _ (oldProfile P Λ v p) chain hp).symm]
    exact chain.old_posSemidef j
  have hD(j:Fin k):D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range:=by
    rw [show A=chain.old from (Physical.old_eq L _ (oldProfile P Λ v p) chain hp).symm,
      show D=chain.direction from (Physical.direction_eq L _ (oldProfile P Λ v p) chain hp).symm]
    exact chain.assigned_direction_mem_range j
  have havg (α:ℝ) (mean:WordRecursion.State (1+k)):
      gaussianAverage B (oldAverage (Base (α,p)) (oldProfile P Λ v p) k h) mean=
        (1/2:ℝ)^k*gaussianAverage B (Raw p k h α) mean:=by
    unfold gaussianAverage
    simp_rw [old_average_common P hA Λ v b hvb Z htarget hstop F hF hFm]
    exact integral_const_mul _ _
  rw [havg 1 newMean,havg 0 oldMean,←mul_sub]
  have hp:=PairedOldGaussianDifference.difference P A hPSD D hD B (F (rootParameter k h))
    (hF.smooth _) (rootSelector k (fun j=>j)) (leafIndex k (fun j=>j))
    newMean oldMean (baseline (Base (1,p)) k h) (baseline L k h) hA0 hν hχ hχβ hb
  exact congrArg (fun z:ℝ=>(1/2:ℝ)^k*z) hp

end SHE.ControlledPairedCommonLaw
