module

public import SHE.ControlledTerminalPairedFields
public import SHE.ControlledPairedCommonLaw
public import SHE.ControlledThetaGaussianDifference
public import SHE.ControlledFiniteCovarianceFields
public import SHE.PairedOldGaussianDifference
public import SHE.ControlledThetaSupported
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledRelativeScoreForest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.ControlledFiniteEndpointComparison
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
open scoped BigOperators

/-- All paired root and rough sources with their actual normalized
common-future-law Gaussian slots. -/
def paired (p:Inputs) (k:ℕ) (h:History X k) (newMean oldMean:WordRecursion.State (1+k))
    (ν χ:ℝ):ℝ:=
  (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices=>
    ∑i,PairedAssignedTelescope.sources P choices (rootSelector k (fun j=>j)) (leafIndex k (fun j=>j))
      newMean oldMean (baseline (Base (1,p)) k h) (baseline (Base (0,p)) k h) ν χ i*
      ControlledTerminalPairedFields.average P hA Λ v b hvb Z htarget hstop F hF hFm
        k p h newMean oldMean choices ν χ i)).sum

local notation "Paired"=>paired P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Point"=>ControlledFiniteCovarianceFields.point P hA Λ v b hvb Z htarget hstop F hF hFm

/-- COMPLETE finite endpoint decomposition of the actual original
old-score word: finite covariance interpolation plus every paired
root/rough source. A single original-history event supports all past
inputs and both dependent current states; singular terminal covariance
and zero newest future age are retained. This is an exact identity,
separate from the subsequent quantitative spatial/time estimate. -/
theorem comparison_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:Inputs,∀newMean oldMean:WordRecursion.State (1+k),
      ∀A0 ν χ:ℝ,0≤A0 → 0≤ν → 0≤χ → χ≤P.exponent →
      (∀j,j≤k+1→∀z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j) →
      let q:=(carrier Zero k).terminal h
      let endpoint:=fun own law mean=>gaussianAverage
        (fullResidualCovariance (Base (law,p)) (oldProfile P Λ v p) k h q)
        (oldAverage (Base (own,p)) (oldProfile P Λ v p) k h) mean
      let mark:ℝ→ℝ:=fun ζ=>Point (1,p) k h q 0 1 ζ newMean
      IntervalIntegrable mark volume 0 1 ∧
        endpoint 1 1 newMean-endpoint 0 0 oldMean=
          (∫ζ in (0:ℝ)..1,mark ζ)+Paired p k h newMean oldMean ν χ:=by
  filter_upwards [ControlledThetaGaussianDifference.covariance_ftc_all_parameters_ae
    P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledPairedCommonLaw.difference_ae
    P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hc hp
  intro p newMean oldMean A0 ν χ hA0 hν hχ hχβ hb q endpoint mark
  have hv:(v:ℝ)≤q:=(carrier Zero k).terminal_base h
  have hcov:=hc (1,p) q hv le_rfl 0 1 newMean
  have hpair:=hp p newMean oldMean A0 ν χ hA0 hν hχ hχβ hb
  dsimp only at hcov hpair
  have he:mark=(fun ζ=>FiniteWordScores.covarianceMark (StoppedGaussianFeatures.historyMeasure q)
      ((1-ζ) • fullResidualCovariance (Base (0,p)) (oldProfile P Λ v p) k h q+
        ζ • fullResidualCovariance (Base (1,p)) (oldProfile P Λ v p) k h q)
      (ObservationTimeShift.profile (v:ℝ) (fun z=>ControlledProfile.profile P Λ p.1 p.2 (1,z)-
        ControlledProfile.profile P Λ p.1 p.2 (0,z)))
      (StoppedGaussianFeatures.stoppedRow (stops (Base (1,p)) k h) (targets (Base (1,p)) k h)
        (centers (Base (1,p)) k h)) (oldAverage (Base (1,p)) (oldProfile P Λ v p) k h) newMean):=by
    funext ζ
    exact ControlledFiniteCovarianceFields.point_of_window P hA Λ v b hvb Z htarget hstop F hF hFm
      (1,p) k h q le_rfl 0 1 ζ newMean
  rw [←he] at hcov
  simp only [TME (0,p) (0,(0,0)) k h] at hpair
  refine ⟨hcov.1,?_⟩
  change endpoint 1 1 newMean-endpoint 0 0 oldMean=_
  have hc':(∫ζ in (0:ℝ)..1,mark ζ)=endpoint 1 1 newMean-endpoint 1 0 newMean:=hcov.2
  have hp':endpoint 1 0 newMean-endpoint 0 0 oldMean=Paired p k h newMean oldMean ν χ:=hpair
  linarith only [hc',hp']

end SHE.ControlledFiniteEndpointComparison
