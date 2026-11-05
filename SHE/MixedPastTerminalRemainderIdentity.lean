module

public import SHE.MixedPastTerminalCovarianceHistoryEnergy
public import SHE.MixedPastTerminalEndpointWord
public import SHE.RootHistoryFubini
public import SHE.HistoryAverageEnergy
public import SHE.MixedPastTerminalCovarianceThetaFields
public import SHE.MixedPastTerminalCovarianceAverages
public import SHE.HilbertFiniteAverage
public import SHE.ControlledTerminalCovarianceSections
public import SHE.MixedPastTerminalCovarianceRelativeMass
public import SHE.RandomScoreSpatialAverage
public import SHE.RandomScoreSpatialAbsolute
public import SHE.ParentScoreInput
public import SHE.MixedPastFiniteTerminalMass

public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastScoreEnergy
public import SHE.RandomFutureCenters
public import SHE.PastMeanSections
public import SHE.QuarterSpatialEvent
public import SHE.PastCovarianceMassSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastTerminalRemainderIdentity
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

local notation "Point"=>MixedPastTerminalCovarianceSpatialFields.relativePoint
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mass"=>MixedPastFiniteTerminalMass.scoreMass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "TA"=>ControlledTerminalCovarianceSections.timeAmplitude
  P haP Λ v b hvb Z htarget hstop F hF hFm

local notation "Avg"=>MixedPastTerminalCovarianceAverages.oldSpaceAverage
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "AA"=>TerminalCovarianceTimeIntegral.activeAmplitude
  P haP Λ v b hvb Z htarget hstop F hF hFm

local notation "TimeAvg"=>MixedPastTerminalCovarianceThetaFields.timeAverage
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "ThetaAvg"=>MixedPastTerminalCovarianceThetaFields.thetaAverage
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "Field"=>MixedPastTerminalCovarianceJointMass.integrand
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "FTC"=>MixedPastTerminalCovarianceHistoryEnergy.ftc
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

def word (k:ℕ) (z:Ω×History HeatCircle (k+1)):ℝ:=
  MixedPastTerminalEndpointWord.wordDifference
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    (k+1) z.2 z.1

def paired (k:ℕ) (ν χ:ℝ) (z:Ω×History HeatCircle (k+1)):ℝ:=
  MixedPastTerminalPairedWord.point
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    (k+1) ν χ z.2 z.1

local notation "Word"=>word 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Pair"=>paired 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

/-- The ACTUAL recursive finite remainder is covariance FTC plus all
paired sources on the ORIGINAL sample/history product measure. -/
theorem original_identity_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target) (k:ℕ)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχβ:χ≤P.exponent)
    (hjet:∀x j,j≤k+2→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j):
    let R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
    Word k=ᵐ[μ.prod (historyMeasure R haarAddCircle (k+1))]
      (fun z=>FTC k z+Pair k ν χ z):=by
  intro R
  have hh:=MixedPastTerminalEndpointWord.word_decomposition_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages haarAddCircle (k+1) hA0 hν hχ hχβ hjet
  have hp:∀ᵐz:Ω×History HeatCircle (k+1) ∂μ.prod (historyMeasure R haarAddCircle (k+1)),
      ∀ω:Ω,IntervalIntegrable (fun ζ=>G (k+1) ζ z.2 ω) volume 0 1 ∧
      MixedPastTerminalEndpointWord.wordDifference
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
        (k+1) z.2 ω=(∫ζ in (0:ℝ)..1,G (k+1) ζ z.2 ω)+
        MixedPastTerminalPairedWord.point
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
          (k+1) ν χ z.2 ω:=Measure.quasiMeasurePreserving_snd.ae hh
  filter_upwards [hp] with z hz
  have he:=(hz z.1).2
  rw [←MixedPastTerminalCovarianceHistoryEnergy.ftc_eq_interval
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k z] at he
  exact he

/-- Honest original-history averaging of the exact actual remainder.
The two absolute branch masses are explicit applicability premises;
the covariance one is discharged by actual_history_energy. -/
theorem average_decomposition_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target) (k:ℕ)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχβ:χ≤P.exponent)
    (hjet:∀x j,j≤k+2→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (hFTC:Integrable (FTC k) (μ.prod (historyMeasure
      (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) haarAddCircle (k+1))))
    (hPair:Integrable (Pair k ν χ) (μ.prod (historyMeasure
      (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) haarAddCircle (k+1)))):
    let R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
    Integrable (Word k) (μ.prod (historyMeasure R haarAddCircle (k+1))) ∧
      ∀ᵐω ∂μ,Integrable (fun h=>Word k (ω,h)) (historyMeasure R haarAddCircle (k+1)) ∧
      (∫h,Word k (ω,h) ∂historyMeasure R haarAddCircle (k+1))=
        (∫h,FTC k (ω,h) ∂historyMeasure R haarAddCircle (k+1))+
        (∫h,Pair k ν χ (ω,h) ∂historyMeasure R haarAddCircle (k+1)):=by
  intro R
  have he:=original_identity_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages k hA0 hν hχ hχβ hjet
  have hw:Integrable (Word k) (μ.prod (historyMeasure R haarAddCircle (k+1))):=
    (hFTC.add hPair).congr he.symm
  refine ⟨hw,?_⟩
  filter_upwards [hw.prod_right_ae,hFTC.prod_right_ae,hPair.prod_right_ae,Measure.ae_ae_of_ae_prod he]
    with ω hω hc hp heq
  refine ⟨hω,?_⟩
  rw [integral_congr_ae heq]
  exact integral_add hc hp

end SHE.MixedPastTerminalRemainderIdentity
