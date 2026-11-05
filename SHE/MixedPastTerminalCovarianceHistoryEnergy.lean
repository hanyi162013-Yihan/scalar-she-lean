module

public import SHE.MixedPastTerminalCovarianceJointMass
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

namespace SHE.MixedPastTerminalCovarianceHistoryEnergy
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

/-- Literal original-history covariance FTC term. -/
def ftc (k:ℕ) (z:Ω×History HeatCircle (k+1)):ℝ:=
  ∫ζ,Field k (ζ,z) ∂MeanThetaAverage.thetaMeasure
local notation "FTC"=>ftc 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

theorem ftc_measurable (k:ℕ):Measurable (FTC k):=
  (MixedPastTerminalCovarianceJointMass.integrand_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k).stronglyMeasurable.integral_prod_left'.measurable

theorem ftc_eq_interval (k:ℕ) (z:Ω×History HeatCircle (k+1)):
    FTC k z=∫ζ in (0:ℝ)..1,G (k+1) ζ z.2 z.1:=by
  rw [intervalIntegral.integral_of_le (zero_le_one:(0:ℝ)≤1)]
  rfl

include hIJ₀ hIJ₁ in
/-- Covariance interpolation commutes with the ORIGINAL root-retained
history average by GENUINE joint absolute mass, not a conditional formal
Fubini premise. -/
theorem actual_root_swap
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ)
    (hsmallL2:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hv1:(v:ℝ)≤1) (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (hvb':v<b) (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (hbH:b≤H) (k:ℕ)
    (hsmall:∀j,j<k+1→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    {A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν)
    (hjet:∀x j,j≤k+1→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0:ℝ≥0) (hBDG:StandardTerminalBDGPower (k+3) J B0):
    let R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
    ∀ᵐy:Ω×HeatCircle ∂μ.prod haarAddCircle,
      Integrable (fun ζ=>TimeAvg k (ζ,y)) MeanThetaAverage.thetaMeasure ∧
      ThetaAvg k y=HistoryProductMeasure.rootAverage R (k+1) (FTC k) y:=by
  intro R
  have hj:=MixedPastTerminalCovarianceJointMass.actual_joint_mass
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallL2 hv1 Bpast hBDGpast
    hages hrootstop hrootage hcenter hvb' hspan hbH k hsmall hA0 hν hjet B0 hBDG
  have hh:=HistoryProductMeasure.root_average_swap R (k+1) MeanThetaAverage.thetaMeasure μ (Field k)
    (MixedPastTerminalCovarianceJointMass.integrand_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k) hj
  simpa only [R,ControlledReferenceLevel.referenceData,HistoryProductMeasure.rootAverage,ftc,MixedPastTerminalCovarianceThetaFields.thetaAverage,
    MixedPastTerminalCovarianceThetaFields.timeAverage,MixedPastTerminalCovarianceAverages.oldSpaceAverage,
    MixedPastTerminalCovarianceSpatialFields.relativePoint,MixedPastTerminalCovarianceJointMass.integrand] using hh

include hIJ₀ hIJ₁ in
/-- ORIGINAL history-averaged actual covariance FTC has the sharp finite
remainder energy. All interpolation/old-space/old-time/root/sample
Fubini and native stochastic applicability inputs are discharged. -/
theorem actual_history_energy
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ)
    (hsmallL2:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hv1:(v:ℝ)≤1) (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (hvb':v<b) (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (hbH:b≤H) (k:ℕ)
    (hsmall:∀j,j<k+1→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    {A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν)
    (hjet:∀x j,j≤k+1→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0:ℝ≥0) (hBDG:StandardTerminalBDGPower (k+3) J B0):
    let CC:=MixedPastWordMoments.momentConstant P (k+1) (k+1) 1
      (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) B0 κ M)^P.exponent)
    let Cm:=2*P.holder*(3*(((1+k:ℕ):ℝ)/(P.lower/2)))
    let EE:=(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)^P.exponent
    let B:=QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
      (k+1) ((b:ℝ)-(v:ℝ)) 0 1 A0 ν
    let D:=(CC*Cm^2*EE*(Fintype.card (Choices 1 (k+1)):ℝ)^2)*(B/2)^2
    let R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
    Integrable (FTC k) (μ.prod (historyMeasure R haarAddCircle (k+1))) ∧
      Integrable (fun ω=>|∫h,FTC k (ω,h) ∂historyMeasure R haarAddCircle (k+1)|^2) μ ∧
      (∫ω,|∫h,FTC k (ω,h) ∂historyMeasure R haarAddCircle (k+1)|^2 ∂μ)≤D:=by
  intro CC Cm EE B D R
  have hj:=MixedPastTerminalCovarianceJointMass.actual_joint_mass
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallL2 hv1 Bpast hBDGpast
    hages hrootstop hrootage hcenter hvb' hspan hbH k hsmall hA0 hν hjet B0 hBDG
  have hFTC:Integrable (FTC k) (μ.prod (historyMeasure R haarAddCircle (k+1))):=hj.integral_prod_right
  have ht:=MixedPastTerminalCovarianceThetaEnergy.actual_theta_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallL2 hv1 Bpast hBDGpast
    hages hrootstop hrootage hcenter hvb' hspan hbH k hsmall hA0 hν hjet B0 hBDG
  have hr:=actual_root_swap 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallL2 hv1 Bpast hBDGpast
    hages hrootstop hrootage hcenter hvb' hspan hbH k hsmall hA0 hν hjet B0 hBDG
  have heq:(fun y:Ω×HeatCircle=>|HistoryProductMeasure.rootAverage R (k+1) (FTC k) y|^2)=ᵐ[μ.prod haarAddCircle]
      fun y=>|ThetaAvg k y|^2:=by
    filter_upwards [hr] with y hy
    rw [←hy.2]
  have hRMS:=ht.2.1.congr heq.symm
  have hh:=HistoryProductMeasure.history_average_energy μ R (k+1) (FTC k)
    (ftc_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k) hFTC hRMS
  exact ⟨hFTC,hh.1,hh.2.trans ((integral_congr_ae heq).trans_le ht.2.2)⟩

end SHE.MixedPastTerminalCovarianceHistoryEnergy
