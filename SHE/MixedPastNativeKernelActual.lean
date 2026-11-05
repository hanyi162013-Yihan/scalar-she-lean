module

public import SHE.NativeUniversalConstants

public import SHE.MixedPastNativeKernelCurrent
public import SHE.MixedPastNativeKernelResidual
public import SHE.MixedPastNativeKernelClipSections
public import SHE.MixedPastNativeAAmplitudeEnergy
public import SHE.MixedPastNativeResidualLegBound
public import SHE.MixedPastNativeThetaSections
public import SHE.MixedPastNativeLeafThetaSections
public import SHE.MixedPastNativeAAmplitude
public import SHE.MixedPastNativeAAmplitudeFields
public import SHE.MixedPastNativeKernelEnergy
public import SHE.MixedPastNativeKernelTrace
public import SHE.MixedPastNativeMeanFTCClip
public import SHE.NativeCurrentCoordinates
public import SHE.NativeCurrentOutputRMS
public import SHE.NativeReserveTranslatedEnvelope
public import SHE.MixedPastNativeKernelAverage
public import SHE.HistoryRelativeOldFirst
public import SHE.NativeParentOutputEnergyAE
public import SHE.ControlledThetaNativePointFields
public import SHE.MixedPastLiteralFields
public import SHE.ControlledFamilyKernelBounds
public import SHE.NativeKernelParameterAverage
public import SHE.ControlledFamilyNativePacketFTC
public import SHE.MixedPastNativeLegIdentity
public import SHE.MixedPastNativeMeanClip
public import SHE.MixedPastNativeMeanCap
public import SHE.NativeCarrierGeometry
public import SHE.ControlledRelativeScoreForest
public import SHE.ControlledThetaNativeGradient
public import SHE.MixedPastNativeConsistentPoint
public import SHE.MixedPastTwoFreshCovarianceInput
public import SHE.NativeResidualInputApplicability
public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastProfileDerivative
public import SHE.ControlledThetaNativeCovariance
public import SHE.ActualCovarianceMarkFields
public import SHE.MixedPastCovarianceMass
public import SHE.ControlledThetaRelativeCovarianceMark
public import SHE.MixedPastLiteralPoint
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledThetaWeightedFields
public import SHE.MixedPastDecayedWord
public import SHE.RelativeHistoryGeometry
public import SHE.ParentHeatFields
public import SHE.MixedPastActualMean
public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section
universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeKernelActual
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeMeanFTCClip_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeMeanFTCClip_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeMeanFTCClip_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeMeanFTCClip_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeMeanFTCClip_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeMeanFTCClip_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastNativeMeanFTCClip_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeMeanFTCClip_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastNativeMeanFTCClip_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

local notation "Field"=>MixedPastNativeKernel.field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Frame"=>MixedPastNativeKernelTrace.frame Λ P haP v b hvb Z htarget hstop F hF hFm

local notation "Current"=>MixedPastNativeKernelEnergy.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "RowVariance"=>MixedPastNativeKernelEnergy.rowVariance Λ P haP v b hvb Z htarget hstop F hF hFm
local notation "RowResidual"=>MixedPastNativeKernelEnergy.rowResidual
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "AAmp"=>MixedPastNativeAAmplitude.amplitude
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- The exact past-energy budget of the complete additive residual. -/
def pastEnergy (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(A0 ν:ℝ)(B0:ℝ≥0):ℝ:=
  let a:=QuarterSpatialEvent.anchor k t
  let age:=fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)
  let sharp:=MixedPastWordMoments.total (d:=1) P
    (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ)) age A0 ν
  let C0:=(k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent
  let c:=Real.sqrt (TwoFreshCompleteWord.momentConstant P k k 1 C0)*(sharp/2)
  let d:=fun j=>Real.sqrt (NativeOmittedCompleteWord.momentConstant P k k j 1 C0)
  let Cmass:=(ControlledProfile.sharpUnit P*((q:ℝ)-(v:ℝ))^((P.exponent-1)/4))*
    ((((1+k:ℕ):ℝ)/(3*P.lower/8))*3)
  let Cbase:=BaselineOriginalGain.unitCoefficient P*((q:ℝ)-(v:ℝ))^(-(1/4:ℝ))*sharp
  let D:=∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ
  ((k:ℝ)+1)*(c^2*(Cmass^2*D)+∑j:Fin k,(d j)^2*(Cbase^2*D))

local notation "PastEnergy"=>pastEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

/-- The exact current-energy budget, with all other factors in their
proved higher moment and the true current displacement in degree chi. -/
def currentEnergy (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(p:ℕ)(χ Cdim:ℝ)(B0:ℝ≥0):ℝ:=
  let δ:=(carrier Zero k).terminal (QuarterSpatialEvent.anchor k t)-(q:ℝ)
  let Cpacket:=MixedPastNativePacketUniform.constant P k k p*
    (1+2*(2:ℝ)^(((2*(p*(k+2)):ℕ):ℝ)*P.exponent)*
      ((k:ℝ)*(NativeHybridMoments.momentConstant (p*(k+2)) B0 κ M)^P.exponent))
  ((Cdim/(3*P.lower/8))*(Real.sqrt δ)⁻¹*(∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ))^χ*
    Cpacket^(1/(p:ℝ))

local notation "CurrentEnergy"=>currentEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

attribute [local irreducible] MixedPastNativeKernel.field MixedPastNativeKernelEnergy.current
  MixedPastNativeKernelEnergy.rowResidual MixedPastNativeKernelEnergy.rowVariance
  MixedPastNativeAAmplitude.amplitude MixedPastWordMoments.total pastEnergy currentEnergy

include hIJ₀ hIJ₁ in
/-- Actual complete endpoint-kernel negative trace. Every Gaussian,
conditional/current moment, native row range, correlation, theta RMS,
original forest and relative-section premise is discharged internally.
The original law stays at q, the physical row is at r, and the only
realized kernel is the bounded complete endpoint difference. -/
theorem actual_energy_fixed (k:ℕ):
    let Hf:=NativeUniversalConstants.rowHorizon (1+k)
    let Cf:=NativeUniversalConstants.rowConstant (1+k)
    let Hcur:=NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega)
    let Cdim:=NativeUniversalConstants.currentConstant.{0} (1+k) (by omega)
    ∀(hΛ:0<Λ)(hlocal:StandardTerminalPastLocality J)
      (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
        ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
      (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
        ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
      (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
      (hrootStop:∀x i,(Z.observations x i).stop=(b:ℝ))
      (hcenter:∀x i,(Z.observations x i).center=x)
      (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)
      (hspanF:(b:ℝ)-(v:ℝ)≤Hf)(hspanC:(b:ℝ)-(v:ℝ)≤4*Real.pi^2*Hcur)
      (hHistory:∀j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
      (q:ℝ≥0)(hvq:v<q)(hqH:q≤H)(hq1:(q:ℝ)≤1)
      (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)
      (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
      (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
      (p:ℕ)(hp:0<p)(Bcur:ℝ≥0)(hBDGcur:StandardTerminalBDGPower (p*(k+2)) J Bcur)
      (Bword:ℝ≥0)(hBDGword:StandardTerminalBDGPower (k+2) J Bword)
      (χ:ℝ)(hχ:0≤χ)(hχ1:χ<1)(horder:1≤(p:ℝ)*(1-χ))
      (mass ρ:ℝ)(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2),
    ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      ∀ht:QuarterSpatialEvent.active Zero (b:ℝ) k q t,
      ∀ r : ℝ, (q:ℝ) ≤ r → r < (carrier Zero k).terminal (QuarterSpatialEvent.anchor k t) →
      ∀ᵐw:Fin k→HeatCircle∂Measure.pi (fun _=>haarAddCircle),
      let a:=QuarterSpatialEvent.anchor k t
      let age:=fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)
      let sharp:=MixedPastWordMoments.total (d:=1) P
        (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ)) age A0 ν
      let K:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k a)
          (carrier_orderedTimes Zero (fun x i=>by
            change (Z.observations x i).stop≤(Z.observations x i).target
            rw [hrootStop,hrootTarget]) k a ht.1)
          (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w)
      let c:=Real.sqrt (Cf/((P.lower/8)*((carrier Zero k).terminal a-r)))*NativeHeatSpan.sqrtKernelConstant
      Integrable (fun ω=>‖NativeRandomKernel.negativeKernel mass ρ hmass hρ.le (Field k q r t w) ω‖^2) μ ∧
        (∫ω,‖NativeRandomKernel.negativeKernel mass ρ hmass hρ.le (Field k q r t w) ω‖^2 ∂μ)≤
          ((1+k:ℕ):ℝ)^2*(4*Real.pi^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
            (NativeHeatSpan.clock ((b:ℝ)-r))^ρ*((c*K)^2*
              (8*sharp^2*CurrentEnergy k q t p χ Cdim Bcur+2*PastEnergy k q t A0 ν Bword)):=by
  intro Hf Cf Hcur Cdim
  have hHf:=NativeUniversalConstants.rowHorizon_pos (1+k)
  have hCf:=NativeUniversalConstants.rowConstant_pos (1+k)
  have hHcur:=NativeUniversalConstants.currentHorizon_pos.{0} (1+k) (by omega)
  have hHcur1:=NativeUniversalConstants.currentHorizon_le_one.{0} (1+k) (by omega)
  have hCdim:=NativeUniversalConstants.currentConstant_pos.{0} (1+k) (by omega)
  have hrow:=MixedPastNativeKernelTrace.row_event_fixed Λ P haP v b hvb Z htarget hstop F hF hFm k
  have hcurrent:=MixedPastNativeKernelCurrent.actual_current_fixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm k
  intro hΛ hlocal hsmallPoint hsmallL2 hrootTarget hrootStop hcenter hspan hspanF hspanC hHistory
    q hvq hqH hq1 B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
    mass ρ hmass hρ hρhalf
  have hnative:∀x i,(Z.observations x i).stop=(Z.observations x i).target:=by
    intro x i
    rw [hrootStop,hrootTarget]
  have hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target:=fun x i=>(hnative x i).le
  have hrootLe:∀x i,(Z.observations x i).stop≤(b:ℝ):=fun x i=>(hrootStop x i).le
  have hvH:v≤H:=hvq.le.trans hqH
  have hv1:(v:ℝ)≤1:=by exact le_trans (by exact_mod_cast hvq.le) hq1
  have hT0:∀x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have hclips:=MixedPastNativeKernelClipSections.actual_clip_sections
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hΛ.le hsmallPoint hnative hrootLe hrootTarget hcenter hspan k
  have hres:=MixedPastNativeKernelResidual.actual_residual
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ.le hsmallPoint hsmallL2 hvH hv1 B1 hBDG1
    hrootTarget hrootStop hcenter hspan k hHistory q hvq hqH
  have hAmpEnergy:=MixedPastNativeAAmplitudeEnergy.actual_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hΛ.le hsmallPoint hsmallL2 hvH hv1 B1 hBDG1 hages hspan k
  filter_upwards [hclips,hres,hAmpEnergy] with t hct hrtA hAt
  intro ht r hqr hrt
  let a:=QuarterSpatialEvent.anchor k t
  have hqta:(q:ℝ)<(carrier Zero k).terminal a:=by
    change (q:ℝ)<(carrier Zero k).terminal (separated k ((0:HeatCircle),t,fun _=>0))
    rw [ActualMeanKernel.terminal_separated Zero b hT0]
    exact ht.2
  have hmaxTarget(i:Fin (1+k)):targets Zero k a i≤(b:ℝ):=
    carrier_targets_le Zero b (fun x=>(hT0 x).le) (fun x i=>(hrootTarget x i).le) k a i
  have hcurrentSmall(i:Fin (1+k)):targets Zero k a i-(q:ℝ)≤4*Real.pi^2*Hcur:=by
    have hvqR:(v:ℝ)≤(q:ℝ):=by exact_mod_cast hvq.le
    linarith [hmaxTarget i,hspanC]
  have hrowSmall(i:Fin (1+k)):targets Zero k a i-r≤Hf:=by
    have hvqR:(v:ℝ)≤(q:ℝ):=by exact_mod_cast hvq.le
    linarith [hmaxTarget i,hspanF,hqr]
  filter_upwards [hct,hrtA ht] with w hcw hrw
  intro a age sharp K c
  obtain ⟨aCur,hCm,hC0,hCi,hCsec,hCE⟩:=hcurrent hΛ hlocal q hvq.le hqH hq1 B1 hBDG1
    t w hqta hcurrentSmall p hp Bcur hBDGcur χ hχ hχ1 horder
  let aA:=AAmp k q t w A0 ν Bword
  have hAm:Measurable aA:=MixedPastNativeAAmplitudeFields.measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hΛ.le hsmallPoint k q t w A0 ν Bword
  have hA0out:∀x,0≤aA x:=MixedPastNativeAAmplitudeEnergy.nonneg
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q t w A0 ν Bword
  have hAE:=hAt ht.1 q hvq hqta w A0 ν Bword
  have hAint:Integrable (fun x=>aA x^2) haarAddCircle:=hAE.1
  have hAEbound:(∫x,aA x^2 ∂haarAddCircle)≤PastEnergy k q t A0 ν Bword:=by
    simpa only [pastEnergy] using hAE.2
  have hCEbound:(∫x,aCur x^2 ∂haarAddCircle)≤CurrentEnergy k q t p χ Cdim Bcur:=by
    simpa only [currentEnergy] using hCE
  have hK:0≤K:=mul_nonneg
    (timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1)
      (fun j=>(uniformConstant_pos 1 j).le) k a ht.1)
    (OrderedHeatForests.parentDensity_nonneg 2 (by norm_num) k _ _ _)
  have hsharp0:0≤sharp:=MixedPastWordMoments.total_nonneg P _ _ _ A0 ν
  have hc0:0≤c:=mul_nonneg (Real.sqrt_nonneg _) NativeHeatSpan.sqrtKernelConstant_pos.le
  have hrowEvent:=hrow hrootTarget hcenter q r (by exact_mod_cast hvq.le) hqr t w hrt hrowSmall
  have hclipJoint:∀ᵐyx:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,∀ω:Ω,
      |(Field k q r t w (ω,yx)).re|≤2*(K*Real.sqrt (RowVariance k q r t w yx)*sharp)*
        |Current k q t w p χ (ω,yx.2)|+|RowResidual k q r t w yx ω|:=by
    have ho:=(Measure.quasiMeasurePreserving_snd
      (μ:=haarAddCircle (T:=2*Real.pi)) (ν:=haarAddCircle (T:=2*Real.pi))).ae hcw
    filter_upwards [ho,hrowEvent] with yx hyx hyRow
    intro ω
    let h:=separated k (yx.2,t,fun i=>w i+yx.2)
    have hph:StrictHistory Zero k h:=
      (FixedHistoryTimeFactors.strict_sections Zero b hT0 k t yx.2 0 (fun i=>w i+yx.2) (fun _=>0)).mpr ht.1
    have hsmallh:SmallHistory Zero (uniformHorizon 1) k h:=
      RelativeHistoryGeometry.smallHistory_of_span Zero b (fun x=>(hT0 x).le)
        (fun x i=>(hrootTarget x i).le) _ k hHistory h
    have hqth:(q:ℝ)<(carrier Zero k).terminal h:=by
      change (q:ℝ)<(carrier Zero k).terminal (separated k (yx.2,t,fun i=>w i+yx.2))
      rw [ActualMeanKernel.terminal_separated Zero b hT0]
      exact ht.2
    have hrth:r<(carrier Zero k).terminal h:=by
      change r<(carrier Zero k).terminal (separated k (yx.2,t,fun i=>w i+yx.2))
      rw [ActualMeanKernel.terminal_separated Zero b hT0]
      have hrta:r<(carrier Zero k).terminal (separated k ((0:HeatCircle),t,fun _=>0)):=hrt
      rwa [ActualMeanKernel.terminal_separated Zero b hT0] at hrta
    exact hyx q hvq.le hqth r hqr hrth hph ht.1 hsmallh A0 ν hA0 hν
      (hjet (rootParameter k h)) p hp χ hχ hχ1.le yx.1 hyRow.1 ω
  have hResJoint:∀ᵐyx:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
      MemLp (RowResidual k q r t w yx) 2 μ ∧
      ProfileL2.normTwo μ (RowResidual k q r t w yx)≤K*Real.sqrt (RowVariance k q r t w yx)*aA yx.2:=by
    have ho:=(Measure.quasiMeasurePreserving_snd
      (μ:=haarAddCircle (T:=2*Real.pi)) (ν:=haarAddCircle (T:=2*Real.pi))).ae hrw
    filter_upwards [ho,hrowEvent] with yx hyx hyRow
    exact hyx ht.1 A0 ν hA0 hν (hjet (rootParameter k (separated k (yx.2,t,fun i=>w i+yx.2))))
      Bword hBDGword r yx.1 hyRow.1
  have hage(i:Fin (1+k)):0<(Frame k t w i).target-(r-(v:ℝ)):=by
    have htgt:(carrier Zero k).terminal a≤targets Zero k a i:=(carrier Zero k).targets_after a i
    change 0<(targets Zero k a i-(v:ℝ))-(r-(v:ℝ))
    linarith
  have hw:0<(b:ℝ)-r:=by
    have hterm:(carrier Zero k).terminal a≤(b:ℝ):=(terminal_le_initial Zero k a).trans_eq (hT0 _)
    linarith
  have hw1:(b:ℝ)-r≤1:=by
    have hvqR:(v:ℝ)≤(q:ℝ):=by exact_mod_cast hvq.le
    linarith [hspan.trans P.horizon_le_one,hqr]
  have hmax(i:Fin (1+k)):(Frame k t w i).target-(r-(v:ℝ))≤(b:ℝ)-r:=by
    change (targets Zero k a i-(v:ℝ))-(r-(v:ℝ))≤(b:ℝ)-r
    linarith [hmaxTarget i]
  have hrowBound:∀ᵐyx:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
      Real.sqrt (RowVariance k q r t w yx)≤c*∑i,
        ((Frame k t w i).target-(r-(v:ℝ)))^(1/4:ℝ)*
          ‖NativeHeatSpan.kernel (8*((Frame k t w i).target-(r-(v:ℝ))))
            (by have := hage i;positivity) yx.1 (yx.2+(Frame k t w i).center)‖:=by
    filter_upwards [hrowEvent] with yx hx
    simpa only [MixedPastNativeKernelEnergy.rowVariance] using hx.2
  exact MixedPastNativeKernelEnergy.energy_of_actual_rms
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    k q r t w p χ K sharp c hK hsharp0 hc0 aCur aA hCm hAm hC0 hA0out hCi hAint
    (CurrentEnergy k q t p χ Cdim Bcur) (PastEnergy k q t A0 ν Bword) hCEbound hAEbound
    (hCsec.mono (fun x hx=>⟨hx.1,hx.2.le⟩)) hResJoint hclipJoint hage hw hw1 hmax
    hrowBound hmass hρ hρhalf

include hIJ₀ hIJ₁ in
theorem actual_energy (k:ℕ):
    ∃Hf Cf Hcur Cdim:ℝ,0<Hf ∧ 0<Cf ∧ 0<Hcur ∧ Hcur≤1 ∧ 0<Cdim ∧
    ∀(hΛ:0<Λ)(hlocal:StandardTerminalPastLocality J)
      (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
        ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
      (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
        ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
      (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
      (hrootStop:∀x i,(Z.observations x i).stop=(b:ℝ))
      (hcenter:∀x i,(Z.observations x i).center=x)
      (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)
      (hspanF:(b:ℝ)-(v:ℝ)≤Hf)(hspanC:(b:ℝ)-(v:ℝ)≤4*Real.pi^2*Hcur)
      (hHistory:∀j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
      (q:ℝ≥0)(hvq:v<q)(hqH:q≤H)(hq1:(q:ℝ)≤1)
      (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)
      (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
      (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
      (p:ℕ)(hp:0<p)(Bcur:ℝ≥0)(hBDGcur:StandardTerminalBDGPower (p*(k+2)) J Bcur)
      (Bword:ℝ≥0)(hBDGword:StandardTerminalBDGPower (k+2) J Bword)
      (χ:ℝ)(hχ:0≤χ)(hχ1:χ<1)(horder:1≤(p:ℝ)*(1-χ))
      (mass ρ:ℝ)(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2),
    ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      ∀ht:QuarterSpatialEvent.active Zero (b:ℝ) k q t,
      ∀ r : ℝ, (q:ℝ) ≤ r → r < (carrier Zero k).terminal (QuarterSpatialEvent.anchor k t) →
      ∀ᵐw:Fin k→HeatCircle∂Measure.pi (fun _=>haarAddCircle),
      let a:=QuarterSpatialEvent.anchor k t
      let age:=fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)
      let sharp:=MixedPastWordMoments.total (d:=1) P
        (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ)) age A0 ν
      let K:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k a)
          (carrier_orderedTimes Zero (fun x i=>by
            change (Z.observations x i).stop≤(Z.observations x i).target
            rw [hrootStop,hrootTarget]) k a ht.1)
          (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w)
      let c:=Real.sqrt (Cf/((P.lower/8)*((carrier Zero k).terminal a-r)))*NativeHeatSpan.sqrtKernelConstant
      Integrable (fun ω=>‖NativeRandomKernel.negativeKernel mass ρ hmass hρ.le (Field k q r t w) ω‖^2) μ ∧
        (∫ω,‖NativeRandomKernel.negativeKernel mass ρ hmass hρ.le (Field k q r t w) ω‖^2 ∂μ)≤
          ((1+k:ℕ):ℝ)^2*(4*Real.pi^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
            (NativeHeatSpan.clock ((b:ℝ)-r))^ρ*((c*K)^2*
              (8*sharp^2*CurrentEnergy k q t p χ Cdim Bcur+2*PastEnergy k q t A0 ν Bword)):=by
  exact ⟨NativeUniversalConstants.rowHorizon (1+k),NativeUniversalConstants.rowConstant (1+k),NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega),NativeUniversalConstants.currentConstant.{0} (1+k) (by omega),NativeUniversalConstants.rowHorizon_pos (1+k),NativeUniversalConstants.rowConstant_pos (1+k),NativeUniversalConstants.currentHorizon_pos.{0} (1+k) (by omega),NativeUniversalConstants.currentHorizon_le_one.{0} (1+k) (by omega),NativeUniversalConstants.currentConstant_pos.{0} (1+k) (by omega),actual_energy_fixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm k⟩

end SHE.MixedPastNativeKernelActual
