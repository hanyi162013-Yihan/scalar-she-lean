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

public import SHE.MixedPastNativeKernelActual
public import SHE.NativeParentKernelAverage
@[expose] public section
noncomputable section
universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeKernelSpatialEnergy
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


local notation "Spatial"=>MixedPastNativeKernelAverage.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "PastEnergy"=>MixedPastNativeKernelActual.pastEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CurrentEnergy"=>MixedPastNativeKernelActual.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastNativeKernel.field MixedPastNativeKernelAverage.spatial
  MixedPastNativeKernelActual.pastEnergy MixedPastNativeKernelActual.currentEnergy MixedPastWordMoments.total

include hIJ₀ hIJ₁ in
/-- Actual ORIGINAL old-space averaged complete negative trace. The
parent forest mass is integrated before sample square, so only its
true finite assignment mass appears. No analytic contract is supplied. -/
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
      let a:=QuarterSpatialEvent.anchor k t
      let age:=fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)
      let sharp:=MixedPastWordMoments.total (d:=1) P
        (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ)) age A0 ν
      let K:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*
        (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)
      let c:=Real.sqrt (Cf/((P.lower/8)*((carrier Zero k).terminal a-r)))*NativeHeatSpan.sqrtKernelConstant
      Integrable (fun ω=>‖NativeRandomKernel.negativeKernel mass ρ hmass hρ.le (Spatial k q r t) ω‖^2) μ ∧
        (∫ω,‖NativeRandomKernel.negativeKernel mass ρ hmass hρ.le (Spatial k q r t) ω‖^2 ∂μ)≤
          ((1+k:ℕ):ℝ)^2*(4*Real.pi^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
            (NativeHeatSpan.clock ((b:ℝ)-r))^ρ*((c*K)^2*
              (8*sharp^2*CurrentEnergy k q t p χ Cdim Bcur+2*PastEnergy k q t A0 ν Bword)) :=by
  intro Hf Cf Hcur Cdim
  have hHf:=NativeUniversalConstants.rowHorizon_pos (1+k)
  have hCf:=NativeUniversalConstants.rowConstant_pos (1+k)
  have hHcur:=NativeUniversalConstants.currentHorizon_pos.{0} (1+k) (by omega)
  have hHcur1:=NativeUniversalConstants.currentHorizon_le_one.{0} (1+k) (by omega)
  have hCdim:=NativeUniversalConstants.currentConstant_pos.{0} (1+k) (by omega)
  have he:=MixedPastNativeKernelActual.actual_energy_fixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm k
  intro hΛ hlocal hsmallPoint hsmallL2 hrootTarget hrootStop hcenter hspan hspanF hspanC hHistory
    q hvq hqH hq1 B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
    mass ρ hmass hρ hρhalf
  filter_upwards [he hΛ hlocal hsmallPoint hsmallL2 hrootTarget hrootStop hcenter hspan hspanF hspanC
    hHistory q hvq hqH hq1 B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword
    χ hχ hχ1 horder mass ρ hmass hρ hρhalf] with t ht
  intro hactive r hqr hrt a age sharp K c
  let oldMeasure:Measure (Fin k→HeatCircle):=Measure.pi (fun _=>haarAddCircle)
  let G:((Fin k→HeatCircle)×Ω)×(HeatCircle×HeatCircle)→ℂ:=fun z=>Field k q r t z.1.1 (z.1.2,z.2)
  have hG:=MixedPastNativeKernelAverage.field_joint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q r t
  obtain ⟨B,hB,hbound⟩:=MixedPastNativeKernel.field_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q r t
  have hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target:=by
    intro x i
    rw [hrootStop,hrootTarget]
  let orderTimes:=carrier_orderedTimes Zero hages k a hactive.1
  let density:=fun w:Fin k→HeatCircle=>OrderedHeatForests.parentDensity 2 (by norm_num) k
    (targets Zero k a) orderTimes (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w)
  let old:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a
  let C:=((1+k:ℕ):ℝ)^2*(4*Real.pi^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
    (NativeHeatSpan.clock ((b:ℝ)-r))^ρ*((c*old)^2*
      (8*sharp^2*CurrentEnergy k q t p χ Cdim Bcur+2*PastEnergy k q t A0 ν Bword))
  have hDq:0≤∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ:=integral_nonneg (fun _=>sq_nonneg _)
  have hDv:0≤∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ:=integral_nonneg (fun _=>sq_nonneg _)
  have hM0:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hMoment:0≤NativeHybridMoments.momentConstant (p*(k+2)) Bcur κ M:=by
    dsimp only [NativeHybridMoments.momentConstant]
    have hu:=ProfileVariance.upperConstant_pos
    positivity
  have hPacket:=MixedPastNativePacketUniform.constant_nonneg P k k p
  have hCur:0≤CurrentEnergy k q t p χ Cdim Bcur:=by
    unfold MixedPastNativeKernelActual.currentEnergy
    have hlower:=P.lower_pos
    positivity
  have hPast:0≤PastEnergy k q t A0 ν Bword:=by
    unfold MixedPastNativeKernelActual.pastEnergy
    positivity
  have hGaussian:0≤GaussianNegativePacket.constant ρ:=by
    dsimp only [GaussianNegativePacket.constant]
    linarith [HeatTrace.fractionalGaussianIntegral_pos hρhalf,GaussianNegativePacket.traceConstant_pos]
  have hbr:0<(b:ℝ)-r:=by
    have hbnd:(carrier Zero k).terminal a≤(b:ℝ):=(terminal_le_initial Zero k a).trans_eq (by rfl)
    linarith
  have hclock:=NativeHeatSpan.clock_pos hbr
  have hC:0≤C:=by dsimp only [C];positivity
  have hi:∀ᵐw:Fin k→HeatCircle∂oldMeasure,
      Integrable (fun ω=>‖NativeRandomKernel.negativeKernel mass ρ hmass hρ.le G (w,ω)‖^2) μ:=by
    filter_upwards [ht hactive r hqr hrt] with w hw
    convert! hw.1 using 1
  have hbnd:∀ᵐw:Fin k→HeatCircle∂oldMeasure,
      (∫ω,‖NativeRandomKernel.negativeKernel mass ρ hmass hρ.le G (w,ω)‖^2 ∂μ)≤C*(density w)^2:=by
    filter_upwards [ht hactive r hqr hrt] with w hw
    convert! hw.2 using 1
    dsimp only [C,density,old,orderTimes,c]
    ring
  have ha:=NativeParentKernelAverage.energy μ (targets Zero k a) orderTimes (fun _:Fin 1=>(0:HeatCircle))
    G hG B hB (fun z y x=>hbound z.1 z.2 y x) hmass hρ.le C hC hi hbnd
  have hsp:NativeKernelParameterAverage.spatialAverage oldMeasure G=Spatial k q r t:=by
    funext z
    exact MixedPastNativeKernelAverage.average_eq_spatial
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      k q r t z.1 z.2.1 z.2.2
  change Integrable (fun ω=>‖NativeRandomKernel.negativeKernel mass ρ hmass hρ.le
    (NativeKernelParameterAverage.spatialAverage oldMeasure G) ω‖^2) μ ∧ _ at ha
  rw [hsp] at ha
  refine ⟨ha.1,ha.2.trans_eq ?_⟩
  dsimp only [C,K,old,c]
  ring

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
      let a:=QuarterSpatialEvent.anchor k t
      let age:=fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)
      let sharp:=MixedPastWordMoments.total (d:=1) P
        (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ)) age A0 ν
      let K:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*
        (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)
      let c:=Real.sqrt (Cf/((P.lower/8)*((carrier Zero k).terminal a-r)))*NativeHeatSpan.sqrtKernelConstant
      Integrable (fun ω=>‖NativeRandomKernel.negativeKernel mass ρ hmass hρ.le (Spatial k q r t) ω‖^2) μ ∧
        (∫ω,‖NativeRandomKernel.negativeKernel mass ρ hmass hρ.le (Spatial k q r t) ω‖^2 ∂μ)≤
          ((1+k:ℕ):ℝ)^2*(4*Real.pi^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
            (NativeHeatSpan.clock ((b:ℝ)-r))^ρ*((c*K)^2*
              (8*sharp^2*CurrentEnergy k q t p χ Cdim Bcur+2*PastEnergy k q t A0 ν Bword)) :=by
  exact ⟨NativeUniversalConstants.rowHorizon (1+k),NativeUniversalConstants.rowConstant (1+k),NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega),NativeUniversalConstants.currentConstant.{0} (1+k) (by omega),NativeUniversalConstants.rowHorizon_pos (1+k),NativeUniversalConstants.rowConstant_pos (1+k),NativeUniversalConstants.currentHorizon_pos.{0} (1+k) (by omega),NativeUniversalConstants.currentHorizon_le_one.{0} (1+k) (by omega),NativeUniversalConstants.currentConstant_pos.{0} (1+k) (by omega),actual_energy_fixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm k⟩

end SHE.MixedPastNativeKernelSpatialEnergy
