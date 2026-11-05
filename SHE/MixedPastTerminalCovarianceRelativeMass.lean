module

public import SHE.MixedPastTerminalCovarianceSpatialFields
public import SHE.ControlledFiniteCovarianceMassRelative
public import SHE.MixedPastTerminalCovarianceEnvelope
public import SHE.HistoryRelativeOldFirst
public import SHE.MixedPastFiniteTerminalMass

public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastScoreEnergy
public import SHE.RandomFutureCenters
public import SHE.PastMeanSections
public import SHE.QuarterSpatialEvent
public import SHE.PastCovarianceMassSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastTerminalCovarianceRelativeMass
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceSpatialFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceSpatialFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceSpatialFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceSpatialFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastCovarianceSpatialFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceSpatialFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open ScalarRootRelativeGeometry ControlledResidualScoreInput MeasurableGaussianScores
  ProfileStability QuarterSpatialEvent OrderedHeatForests
local notation "Actual" => MixedPastLiteralCovariance.actualPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "G"=>MixedPastTerminalCovarianceFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "MActual"=>MixedPastTerminalCovarianceFields.mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "HM"=>MixedPastTerminalCovarianceSpatialFields.historyMass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "SM"=>MixedPastFiniteTerminalMass.scoreMass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- ONE original history event identifies the actual random covariance
mass with the sharp endpoint mass before any sample or output section. -/
theorem mass_relative_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x) (k:ℕ):
    ∀ᵐ t:Fin (k+1)→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      ∀ᵐ w:Fin (k+1)→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),
      ∀ᵐ x:HeatCircle ∂haarAddCircle,∀ζ:ℝ,∀ω:Ω,
      HM k ζ t ((ω,x),w)=SM k ζ t ((ω,x),w):=by
  have hevent:∀ᵐ h ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0))
      haarAddCircle (k+1),∀ζ:ℝ,∀ω:Ω,
      MActual (k+1) ζ h ω=
      futureInput (fun i=>stops Zero (k+1) h i-(v:ℝ))
        (fun i=>targets Zero (k+1) h i-(v:ℝ)) (centers Zero (k+1) h)
        (BoundedWindowDecomposition.residual P Λ (U ω) (Dir ω)
          (fun j=>lower Zero (k+1) h j-(v:ℝ)) (fun j=>upper Zero (k+1) h j-(v:ℝ))
          (BoundedWindowDecomposition.convexProfile P Λ (U ω) (Dir ω) 1 0 (1-ζ)))
        (fun p=>ControlledProfile.profile P Λ (U ω) (Dir ω) (1,p)-
          ControlledProfile.profile P Λ (U ω) (Dir ω) (0,p))
        ((carrier Zero (k+1)).terminal h-(v:ℝ)) 0:=by
    filter_upwards [ControlledFiniteCovarianceMassRelative.mass_relative_ae
      P haP Λ v b hvb Z htarget hstop F hF hFm hages haarAddCircle (k+1)] with h hh
    intro ζ ω
    have hvq:(v:ℝ)≤(carrier Zero (k+1)).terminal h:=((carrier Zero k).nodeTime_mem h).1
    have he:=hh (1,(U ω,Dir ω)) ((carrier Zero (k+1)).terminal h) hvq le_rfl 0 1 ζ
    simpa only [MixedPastTerminalCovarianceFields.mass,
      BoundedThetaRelativeSecondScore.covariance,futureInput,add_zero,
      MixedPastTerminalCovarianceEnvelope.profile_reversal] using he
  have hs:=HistoryProductMeasure.ae_relative_old_first
    (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) (k+1) hevent
  filter_upwards [hs] with t ht
  filter_upwards [ht] with w hw
  filter_upwards [hw] with x hx
  intro ζ ω
  have he:=hx ζ ω
  have hterm:(carrier Zero (k+1)).terminal
      (separated (k+1) (x,t,fun i=>w i+x))=
      (carrier Zero (k+1)).terminal (anchor (k+1) t):=by
    dsimp only [anchor]
    rw [terminal_separated Zero (b:ℝ) (fun _=>rfl),
      terminal_separated Zero (b:ℝ) (fun _=>rfl)]
  rw [ScalarRootRelativeGeometry.covered_stops_sections Zero (b:ℝ) (fun _=>rfl)
      (b:ℝ) hrootstop (k+1) t x 0 _ (fun _=>0),
    FixedHistoryTimeFactors.targets_sections Zero (b:ℝ) (fun _=>rfl) (fun _=>(b:ℝ))
      hrootage (k+1) t x 0 _ (fun _=>0),
    FixedHistoryTimeFactors.lower_sections Zero (b:ℝ) (fun _=>rfl) (k+1) t x 0 _ (fun _=>0),
    FixedHistoryTimeFactors.upper_sections Zero (b:ℝ) (fun _=>rfl) (k+1) t x 0 _ (fun _=>0),
    ScalarRootRelativeGeometry.centers_relative Zero hcenter,hterm] at he
  simpa only [MixedPastTerminalCovarianceSpatialFields.historyMass,
    MixedPastFiniteTerminalMass.scoreMass,futureInput,anchor,add_zero] using he

end SHE.MixedPastTerminalCovarianceRelativeMass
