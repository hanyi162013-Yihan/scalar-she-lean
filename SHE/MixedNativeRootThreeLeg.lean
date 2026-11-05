module

public import SHE.MixedNativeRootTransfer
public import SHE.MixedNativeRootLegMass
public import SHE.MixedPastMeanAbsolute
public import SHE.MixedPastBaselineHistoryMass
public import SHE.MixedNativeCovarianceFTCIdentity
public import SHE.ControlledFamilyRootAverageFTC
public import SHE.ControlledFamilyLegFubini
public import SHE.PastCovarianceRMS
public import SHE.MixedPastCovarianceSpatialAbsoluteUniform
public import SHE.HistoryRelativeSample
public import SHE.RandomScoreSpatialAverage
public import SHE.HistoryRelativeOldFirst
public import SHE.ScalarRootSharpSections
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

namespace SHE.MixedNativeRootThreeLeg
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeRootThreeLeg_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeRootThreeLeg_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeRootThreeLeg_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeRootThreeLeg_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeRootThreeLeg_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeRootThreeLeg_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
local instance mixedNativeRootThreeLeg_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeRootThreeLeg_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeRootThreeLeg_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

local notation "Point" => MixedPastCovarianceSpatialFields.relativePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mass" => MixedPastCovarianceSpatialFields.scoreMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "Rzero"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)

def covarianceAverage (k : ℕ) (q : ℝ≥0) (z : Ω×HeatCircle) : ℝ:=
  ∫ θ in Ioc (0:ℝ) 1,HistoryProductMeasure.rootAverage Rzero k
    (fun a=>MixedNativeRootLegMass.covarianceField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k q (θ,a)) z

def meanAverage (k : ℕ) (q : ℝ≥0) (z : Ω×HeatCircle) : ℝ:=
  ∫ θ in Ioc (0:ℝ) 1,HistoryProductMeasure.rootAverage Rzero k
    (fun a=>MixedNativeRootLegMass.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k q (θ,a)) z

def baselineAverage (k : ℕ) (q : ℝ≥0) (z : Ω×HeatCircle) : ℝ:=
  ∫ θ in Ioc (0:ℝ) 1,HistoryProductMeasure.rootAverage Rzero k
    (fun a=>MixedNativeRootLegMass.baselineField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k q (θ,a)) z

include hIJ₀ hIJ₁ in
/-- Literal root-retained finite reference comparison, with every old
time/space and theta average placed before the final spatial square.
All component absolute masses are derived from the actual mixed pair. -/
theorem actual_three_leg_transfer (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH : v≤H) (hv1 : (v:ℝ)≤1)
    (Bpast : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (k+2) J B0)
    (q : ℝ≥0) (hvq : v≤q) (hqb : q<b) (hqH : q≤H) (hq1 : (q:ℝ)≤1) :
    ∀ᵐ z : Ω×HeatCircle ∂μ.prod haarAddCircle,
      MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k 1 q z-
      MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k 0 q z=
      covarianceAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k q z+
      meanAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k q z+
      baselineAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k q z := by
  have he:=MixedNativeRootTransfer.actual_root_transfer
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hsmallPoint hsmallL2 hvH hv1 Bpast hBDGpast hages hrootStop hrootTarget hcenter
    hspan k hfresh hold A0 ν hA0 hν hjet B0 hBDG q hvq hqb hqH hq1
  have hi:=MixedNativeRootLegMass.legs_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hsmallPoint hsmallL2 hvH hv1 Bpast hBDGpast hages hrootStop hrootTarget hcenter
    hspan k hfresh hold A0 ν hA0 hν hjet B0 hBDG q hvq hqb hqH hq1
  let C:=MixedNativeRootLegMass.covarianceField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q
  let Mv:=MixedNativeRootLegMass.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q
  let B:=MixedNativeRootLegMass.baselineField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q
  have hs:=HistoryProductMeasure.root_theta_sum_three Rzero k (volume.restrict (Ioc (0:ℝ) 1)) μ
    C Mv B hi.1 hi.2.1 hi.2.2
  have hmark (θ : ℝ) (z : Ω×HeatCircle) :
      MixedNativeRootTransfer.averagedMark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q z=
      HistoryProductMeasure.rootAverage Rzero k (fun a=>C (θ,a)+Mv (θ,a)+B (θ,a)) z := by
    unfold MixedNativeRootTransfer.averagedMark
    congr 1
    funext a
    exact ControlledFamilyLegFubini.active_mark_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (U a.1,Dir a.1) k a.2 q (embed (S.first q a.1)) (embed (S.second q a.1-S.first q a.1)) θ
  filter_upwards [he,hs] with z he hs
  rw [←he.2]
  simp_rw [hmark]
  exact hs

end SHE.MixedNativeRootThreeLeg
