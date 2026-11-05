module

public import SHE.MixedPastTerminalCovarianceSpatialEnergy
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

namespace SHE.MixedPastTerminalCovarianceTimeEnergy
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

include hIJ₀ hIJ₁ in
/-- LITERAL finite terminal covariance branch, averaged in original
old space and then original old time BEFORE squaring. All stochastic,
conditional-Gaussian, source, spatial and time inputs are discharged. -/
theorem actual_time_energy
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
    {ζ:ℝ} (hζ:0≤ζ) (hζ1:ζ≤1) {A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν)
    (hjet:∀x j,j≤k+1→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0:ℝ≥0) (hBDG:StandardTerminalBDGPower (k+3) J B0):
    let old:=Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
    let CC:=MixedPastWordMoments.momentConstant P (k+1) (k+1) 1
      (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) B0 κ M)^P.exponent)
    let Cm:=2*P.holder*(3*(((1+k:ℕ):ℝ)/(P.lower/2)))
    let EE:=(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)^P.exponent
    let B:=QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
      (k+1) ((b:ℝ)-(v:ℝ)) 0 1 A0 ν
    Integrable (Avg k ζ) (old.prod (μ.prod haarAddCircle)) ∧
      Integrable (fun y=>|∫t,Avg k ζ (t,y) ∂old|^2) (μ.prod haarAddCircle) ∧
      (∫y,|∫t,Avg k ζ (t,y) ∂old|^2 ∂μ.prod haarAddCircle)≤
        (CC*Cm^2*EE*(Fintype.card (Choices 1 (k+1)):ℝ)^2)*(B/2)^2:=by
  intro old CC Cm EE B
  let C:=CC*Cm^2*EE*(Fintype.card (Choices 1 (k+1)):ℝ)^2
  have hCC:0≤CC:=MixedPastWordMoments.momentConstant_nonneg P (k+1) (k+1) 1 _
  have hEE:0≤EE:=Real.rpow_nonneg (integral_nonneg (fun _=>sq_nonneg _)) _
  have hC:0≤C:=mul_nonneg (mul_nonneg (mul_nonneg hCC (sq_nonneg _)) hEE) (sq_nonneg _)
  have hm:=MixedPastTerminalCovarianceSpatialEnergy.actual_spatial_energy_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallL2 hv1 Bpast hBDGpast
    hages hrootstop hrootage hcenter hspan hbH k hsmall hζ hζ1 hA0 hν hjet B0 hBDG
  have hbudget:=TerminalCovarianceTimeIntegral.old_time_integral P haP Λ v b hvb Z htarget hstop
    F hF hFm hvb' (k+1) hA0 hν
  let A:=fun t:Fin (k+1)→ℝ=>Real.sqrt C*AA (k+1) A0 ν t
  have hAm:Measurable A:=measurable_const.mul (TerminalCovarianceTimeIntegral.activeAmplitude_measurable
    P haP Λ v b hvb Z htarget hstop F hF hFm (k+1) A0 ν)
  have hAi:Integrable A old:=hbudget.1.const_mul _
  have hA0'(t):0≤A t:=mul_nonneg (Real.sqrt_nonneg _)
    (TerminalCovarianceTimeIntegral.activeAmplitude_nonneg P haP Λ v b hvb Z htarget hstop F hF hFm
      (k+1) A0 ν t)
  have hsec:∀ᵐt ∂old,Integrable (fun y=>‖Avg k ζ (t,y)‖^2) (μ.prod haarAddCircle) ∧
      (∫y,‖Avg k ζ (t,y)‖^2 ∂μ.prod haarAddCircle)≤(A t)^2:=by
    filter_upwards [hm] with t ht
    by_cases ha:StrictHistory Zero (k+1) (anchor (k+1) t) ∧
        (v:ℝ)<(carrier Zero (k+1)).terminal (anchor (k+1) t)
    · have hh:=ht ha.1
      have he:AA (k+1) A0 ν t=TA (k+1) t A0 ν:=ite_eq_left ha
      have heq:CC*Cm^2*EE*(TA (k+1) t A0 ν*(Fintype.card (Choices 1 (k+1)):ℝ))^2=(A t)^2:=by
        dsimp only [A]
        rw [he]
        conv_rhs => rw [mul_pow,Real.sq_sqrt hC]
        dsimp only [C]
        ring
      refine ⟨by simpa only [Real.norm_eq_abs,MixedPastTerminalCovarianceAverages.oldSpaceAverage] using hh.2.1,?_⟩
      simpa only [Real.norm_eq_abs,MixedPastTerminalCovarianceAverages.oldSpaceAverage] using hh.2.2.1.trans_eq heq
    · have hz:=MixedPastTerminalCovarianceAverages.oldSpaceAverage_zero
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k ζ t ha
      simp only [hz,norm_zero,zero_pow (by decide : (2:ℕ)≠0),integral_zero]
      exact ⟨integrable_zero _ _ _,sq_nonneg _⟩
  have hh:=HilbertParameterAverage.finite_energy (μ.prod haarAddCircle) old (Avg k ζ)
    (MixedPastTerminalCovarianceAverages.oldSpaceAverage_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k ζ)
    A hAm hAi hA0' (hsec.mono (fun _ h=>h.1)) (hsec.mono (fun _ h=>h.2))
  refine ⟨hh.1,by simpa only [Real.norm_eq_abs] using hh.2.1,?_⟩
  have hbound:(∫t,A t ∂old)≤Real.sqrt C*(B/2):=by
    rw [show A=fun t=>Real.sqrt C*AA (k+1) A0 ν t from rfl,integral_const_mul]
    exact mul_le_mul_of_nonneg_left hbudget.2 (Real.sqrt_nonneg _)
  have hs:((∫t,A t ∂old))^2≤(Real.sqrt C*(B/2))^2:=
    pow_le_pow_left₀ (integral_nonneg hA0') hbound 2
  have he:(Real.sqrt C*(B/2))^2=C*(B/2)^2:=by rw [mul_pow,Real.sq_sqrt hC]
  simpa only [Real.norm_eq_abs] using hh.2.2.trans (hs.trans_eq he)

end SHE.MixedPastTerminalCovarianceTimeEnergy
