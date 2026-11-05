module

public import SHE.MixedPastTerminalRemainderEnergy
public import SHE.MixedPastTerminalPairedHistoryEnergy
public import SHE.MixedPastTerminalRemainderIdentity
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
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedTerminalEnergySplit
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedTerminalEnergySplit_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedTerminalEnergySplit_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedTerminalEnergySplit_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedTerminalEnergySplit_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedTerminalEnergySplit_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedTerminalEnergySplit_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
local instance mixedTerminalEnergySplit_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedTerminalEnergySplit_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedTerminalEnergySplit_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

local notation "Word"=>MixedPastTerminalRemainderIdentity.word
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Pair"=>MixedPastTerminalRemainderIdentity.paired
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "RMS"=>MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) (Λ:=Λ)
  (P:=P) (haP:=haP) (v:=v) (b:=b) (hvb:=hvb) (Z:=Z)
  (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)
local notation "En"=>MixedPastTerminalTimeFields.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
theorem actual_energy_split
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ) (hH:(H:ℝ)≤1) (hvb':v<b)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (hbH:b≤H)
    (hsmallP:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ) (hsmall:∀j,j<k+1→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0<χ) (hχβ:χ<P.exponent)
    (hjet:∀x j,j≤k+2→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order:ℕ) (horder:0<order) (ho0:1≤(order:ℝ)*(1-χ))
    (ho1:1≤(order:ℝ)*(1-χ/P.exponent)) (B0 B1 Bcov:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (hBDG1:StandardTerminalBDGPower 1 J B1)
    (hBDGcov:StandardTerminalBDGPower (k+3) J Bcov) :
    let R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
    let CC:=MixedPastWordMoments.momentConstant P (k+1) (k+1) 1
      (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) Bcov κ M)^P.exponent)
    let Cm:=2*P.holder*(3*(((1+k:ℕ):ℝ)/(P.lower/2)))
    let B:=QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
      (k+1) ((b:ℝ)-(v:ℝ)) 0 1 A0 ν
    let Epast:=∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ
    Integrable (Word k) (μ.prod (historyMeasure R haarAddCircle (k+1))) ∧
      Integrable (fun ω=>|∫hist,Word k (ω,hist) ∂historyMeasure R haarAddCircle (k+1)|^2) μ ∧
      Integrable (fun ω=>|∫hist,Pair k ν χ (ω,hist) ∂historyMeasure R haarAddCircle (k+1)|^2) μ ∧
      (∫ω,|∫hist,Word k (ω,hist) ∂historyMeasure R haarAddCircle (k+1)|^2 ∂μ)≤
        2*((CC*Cm^2*(Fintype.card (Choices 1 (k+1)):ℝ)^2)*(B/2)^2*Epast^P.exponent+
          (∫ω,|∫hist,Pair k ν χ (ω,hist) ∂historyMeasure R haarAddCircle (k+1)|^2 ∂μ)):=by
  intro R CC Cm B Epast
  have hw:=MixedPastTerminalRemainderEnergy.actual_history_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hH hvb' hages hrootstop hrootage hcenter hspan hbH hsmallP k hsmall hA0 hν hχ hχβ hjet
    order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov
  have hc:=MixedPastTerminalCovarianceHistoryEnergy.actual_history_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hsmallP (show (v:ℝ)≤1 from (show (v:ℝ)≤(H:ℝ) from by exact_mod_cast hvb.trans hbH).trans hH)
    B1 hBDG1 hages hrootstop hrootage hcenter hvb' hspan hbH k hsmall hA0 hν
    (fun x j hj z=>hjet x j (by omega) z) Bcov hBDGcov
  have hp:=MixedPastTerminalPairedHistoryEnergy.actual_history_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hH hvb' hages hrootstop hrootage hcenter hspan hbH hsmallP k hsmall hA0 hν hχ hχβ hjet
    order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov
  have hd:=MixedPastTerminalRemainderIdentity.average_decomposition_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hages k hA0 hν hχ.le hχβ.le hjet hc.1 hp.1
  have hCi:Integrable (fun ω=>|∫hist,FTC k (ω,hist) ∂historyMeasure R haarAddCircle (k+1)|^2) μ:=by
    convert! hc.2.1 using 1
  have hPi:Integrable (fun ω=>|∫hist,Pair k ν χ (ω,hist) ∂historyMeasure R haarAddCircle (k+1)|^2) μ:=by
    convert! hp.2.1 using 1
  have hdom:Integrable (fun ω=>2*((|∫hist,FTC k (ω,hist) ∂historyMeasure R haarAddCircle (k+1)|^2)+
      (|∫hist,Pair k ν χ (ω,hist) ∂historyMeasure R haarAddCircle (k+1)|^2))) μ:=by
    convert! (hCi.add hPi).const_mul 2 using 1
  have hle:∀ᵐω ∂μ,|∫hist,Word k (ω,hist) ∂historyMeasure R haarAddCircle (k+1)|^2≤
      2*((|∫hist,FTC k (ω,hist) ∂historyMeasure R haarAddCircle (k+1)|^2)+
        (|∫hist,Pair k ν χ (ω,hist) ∂historyMeasure R haarAddCircle (k+1)|^2)):=by
    filter_upwards [hd.2] with ω hω
    rw [hω.2]
    simp only [sq_abs]
    nlinarith [sq_nonneg ((∫hist,FTC k (ω,hist) ∂historyMeasure R haarAddCircle (k+1))-
      (∫hist,Pair k ν χ (ω,hist) ∂historyMeasure R haarAddCircle (k+1)))]
  refine ⟨hw.1,hw.2.1,hp.2.1,(integral_mono_ae hw.2.1 hdom hle).trans ?_⟩
  rw [integral_const_mul,integral_add hCi hPi]
  have hh:=mul_le_mul_of_nonneg_left (add_le_add_right hc.2.2
    (∫ω,|∫hist,Pair k ν χ (ω,hist) ∂historyMeasure R haarAddCircle (k+1)|^2 ∂μ)) (by norm_num:(0:ℝ)≤2)
  convert! hh using 1 <;> ring

end SHE.MixedTerminalEnergySplit
