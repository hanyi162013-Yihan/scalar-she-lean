module

public import SHE.RootHistoryFields
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

namespace SHE.RetainedTerminalEnergySplit
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
theorem actual_spatial_energy
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
    let W:=HistoryProductMeasure.rootAverage R (k+1) (Word k)
    let PV:=MixedPastTerminalPairedTimeEnergy.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm (k+1) ν χ
    (W=ᵐ[μ.prod haarAddCircle] fun z=>ThetaAvg k z+PV z) ∧
      Integrable (fun z=>|W z|^2) (μ.prod haarAddCircle) ∧
      Integrable (fun z=>|PV z|^2) (μ.prod haarAddCircle) ∧
      (∫z,|W z|^2 ∂μ.prod haarAddCircle)≤
        2*((CC*Cm^2*(Fintype.card (Choices 1 (k+1)):ℝ)^2)*(B/2)^2*Epast^P.exponent+
          (∫z,|PV z|^2 ∂μ.prod haarAddCircle)):=by
  intro R CC Cm B Epast W PV
  have hv1:(v:ℝ)≤1:=(show (v:ℝ)≤(H:ℝ) from by exact_mod_cast hvb.trans hbH).trans hH
  have hc:=MixedPastTerminalCovarianceHistoryEnergy.actual_history_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hsmallP hv1 B1 hBDG1 hages hrootstop hrootage hcenter hvb' hspan hbH k hsmall hA0 hν
    (fun x j hj z=>hjet x j (by omega) z) Bcov hBDGcov
  have hp:=MixedPastTerminalPairedHistoryEnergy.actual_history_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hH hvb' hages hrootstop hrootage hcenter hspan hbH hsmallP k hsmall hA0 hν hχ hχβ hjet
    order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov
  have hw:=MixedPastTerminalWordMass.word_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    haarAddCircle (k+1)
  have hi:=MixedPastTerminalRemainderIdentity.original_identity_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hages k hA0 hν hχ.le hχβ.le hjet
  have hdiff:(Word k-Pair k ν χ)=ᵐ[μ.prod (historyMeasure R haarAddCircle (k+1))] FTC k:=by
    filter_upwards [hi] with z hz
    change Word k z-Pair k ν χ z=FTC k z
    linarith
  have hr:=HistoryProductMeasure.root_average_congr_ae R (k+1) μ _ _ hdiff
  have hs:=HistoryProductMeasure.root_average_sub_ae R (k+1) μ (Word k) (Pair k ν χ) hw hp.1
  have hswap:=MixedPastTerminalCovarianceHistoryEnergy.actual_root_swap
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hsmallP hv1 B1 hBDG1 hages hrootstop hrootage hcenter hvb' hspan hbH k hsmall hA0 hν
    (fun x j hj z=>hjet x j (by omega) z) Bcov hBDGcov
  have hpair:HistoryProductMeasure.rootAverage R (k+1) (Pair k ν χ)=PV:=by rfl
  have he:W=ᵐ[μ.prod haarAddCircle] fun z=>ThetaAvg k z+PV z:=by
    filter_upwards [hr,hs,hswap] with z hz hsz hcz
    rw [hsz,←hcz.2,hpair] at hz
    change W z-PV z=ThetaAvg k z at hz
    linarith
  have htheta:=MixedPastTerminalCovarianceThetaEnergy.actual_theta_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hsmallP hv1 B1 hBDG1 hages hrootstop hrootage hcenter hvb' hspan hbH k hsmall hA0 hν
    (fun x j hj z=>hjet x j (by omega) z) Bcov hBDGcov
  have hpairEnergy:=MixedPastTerminalPairedLinearEnergy.actual_linear_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hH hvb' hages (fun x i=>(hrootstop x i).le) hrootage hcenter hspan hbH hsmallP
    k hsmall hA0 hν hχ hχβ hjet order horder ho0 ho1 B0 B1 hBDG hBDG1
  have hmW:Measurable W:=HistoryProductMeasure.rootAverage_measurable R (k+1) (Word k)
    (MixedPastTerminalWordMass.word_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm (k+1))
  have hh:=HistoryProductMeasure.retained_sum_energy (μ.prod haarAddCircle) W (ThetaAvg k) PV
    hmW.aestronglyMeasurable he htheta.2.1 hpairEnergy.2.1
  refine ⟨he,hh.1,hpairEnergy.2.1,hh.2.trans ?_⟩
  have hbound:=mul_le_mul_of_nonneg_left
    (add_le_add_right htheta.2.2 (∫z,|PV z|^2 ∂μ.prod haarAddCircle)) (by norm_num:(0:ℝ)≤2)
  convert! hbound using 1 <;> ring

end SHE.RetainedTerminalEnergySplit
