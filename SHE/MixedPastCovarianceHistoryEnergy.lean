module

public import SHE.MixedPastCovarianceTimeFields
public import SHE.PastCovarianceRMS
public import SHE.MixedPastCovarianceSpatialAbsoluteUniform
public import SHE.HistoryRelativeSample
public import SHE.HistoryAverageEnergy
public import SHE.MixedPastCovarianceAverageUniform
public import SHE.MixedPastCovarianceAbsoluteUniform
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

namespace SHE.MixedPastCovarianceHistoryEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceHistoryEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceHistoryEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceHistoryEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceHistoryEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceHistoryEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceHistoryEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
local instance mixedPastCovarianceHistoryEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceHistoryEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceHistoryEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

include hIJ₀ hIJ₁ in
/-- Genuine sample times ORIGINAL-history absolute covariance mass,
before any signed cancellation, with an envelope independent of theta.
All actual-profile and correlated native-word applicability is derived. -/
theorem actual_history_energy (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
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
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (k+2) J B0) :
    ∀ᵐ θ ∂volume,∀ q : ℝ≥0,v≤q→q<b→q≤H→|θ|≤1→
      let CG:=MixedPastWordMoments.momentConstant P k k 1
        ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
      let E:=∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ
      let R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
      Integrable (fun ω=>|∫ h,Actual k θ q (ω,h) ∂historyMeasure R haarAddCircle k|^2) μ ∧
      (∫ ω,|∫ h,Actual k θ q (ω,h) ∂historyMeasure R haarAddCircle k|^2 ∂μ)≤
        (PastCovarianceRMS.coefficient P k CG*Real.sqrt E*
          QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
            k ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) (MarkedProfileTimeFactors.freshDegree P) A0 ν)^2 := by
  have ha:=MixedPastCovarianceAbsoluteUniform.actual_absolute_history
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallPoint hsmallL2 hvH hv1
      Bpast hBDGpast hages hrootStop hrootTarget hcenter hspan k hold A0 ν hA0 hν hjet B0 hBDG
  have he:=MixedPastCovarianceAverageUniform.actual_averaged_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallPoint hsmallL2 hvH hv1
      Bpast hBDGpast hages hrootStop hrootTarget hcenter hspan k hold A0 ν hA0 hν hjet B0 hBDG
  filter_upwards [ha,he] with θ hθa hθe
  intro q hvq hqb hqH hθ CG E R
  have hAbs:=hθa q hvq hqb hqH hθ
  have hRMS:=hθe q hvq hqb hqH hθ
  have hm:=MixedPastLiteralCovariance.actualPoint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint k θ q
  have hbase : R.base=(v:ℝ):=rfl
  have hhor : R.horizon=(b:ℝ):=rfl
  have hi : Integrable (fun z : Ω×HeatCircle=>
      |∫ t:Fin k→ℝ,∫ w:Fin k→HeatCircle,Actual k θ q (z.1,separated k (z.2,t,fun i=>w i+z.2))
        ∂Measure.pi (fun _=>haarAddCircle)
        ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon))|^2) (μ.prod haarAddCircle):=by
    simpa only [hbase,hhor,MixedPastCovarianceSpatialFields.relativePoint] using hRMS.2.1
  have hh:=history_average_energy μ R k (Actual k θ q) hm hAbs.1 hi
  refine ⟨hh.1,hh.2.trans ?_⟩
  simpa only [hbase,hhor,MixedPastCovarianceSpatialFields.relativePoint] using hRMS.2.2

end SHE.MixedPastCovarianceHistoryEnergy
