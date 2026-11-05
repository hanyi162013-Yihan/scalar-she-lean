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

public import SHE.MixedPastNativeKernelSpatialEnergy
public import SHE.MixedPastNativeKernelActual
public import SHE.NativeParentKernelAverage
public import SHE.NativeKernelEnergyHaar
public import SHE.MixedPastNativeKernelSemigroup
public import SHE.MixedPastNativeSpatialFields
@[expose] public section
noncomputable section
universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeHaarEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeMeanFTCClip_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeMeanFTCClip_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeMeanFTCClip_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeMeanFTCClip_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeMeanFTCClip_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeMeanFTCClip_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
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
/-- Actual additive and original-U SAME-Haar native energies of the
complete q-law endpoint difference. The later row-r trace and genuine
right heat are linked by an exact operator identity. All coefficient
measurability, dependence and infinite-column applicability are derived. -/
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
      let e0:Ω→ℝ:=fun ω=>∑'j:HaarNode,‖OneInputOperator.besselHalf mass ρ hmass hρ.le
        (NativeRandomKernel.integralOperator (Spatial k q q t) ω
          (CircleNormalization.push (globalHaarColumn j (AdditiveHaarForcing.constantField κ hκ).1)))‖^2
      let e1:Ω→ℝ:=fun ω=>∑'j:HaarNode,‖OneInputOperator.besselHalf mass ρ hmass hρ.le
        (NativeRandomKernel.integralOperator (Spatial k q q t) ω
          (CircleNormalization.push (globalHaarColumn j
            (ContinuousHeatMild.coefficientFunction haU hell hbU S.first (q,ω)).1)))‖^2
      Integrable e0 μ ∧ Integrable e1 μ ∧
        (∫ω,e0 ω ∂μ)+(∫ω,e1 ω ∂μ)≤(κ+M)*(((1+k:ℕ):ℝ)^2*(4*Real.pi^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
            (NativeHeatSpan.clock ((b:ℝ)-r))^ρ*((c*K)^2*
              (8*sharp^2*CurrentEnergy k q t p χ Cdim Bcur+2*PastEnergy k q t A0 ν Bword))) :=by
  intro Hf Cf Hcur Cdim
  have hHf:=NativeUniversalConstants.rowHorizon_pos (1+k)
  have hCf:=NativeUniversalConstants.rowConstant_pos (1+k)
  have hHcur:=NativeUniversalConstants.currentHorizon_pos.{0} (1+k) (by omega)
  have hHcur1:=NativeUniversalConstants.currentHorizon_le_one.{0} (1+k) (by omega)
  have hCdim:=NativeUniversalConstants.currentConstant_pos.{0} (1+k) (by omega)
  have he:=MixedPastNativeKernelSpatialEnergy.actual_energy_fixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm k
  intro hΛ hlocal hsmallPoint hsmallL2 hrootTarget hrootStop hcenter hspan hspanF hspanC hHistory
    q hvq hqH hq1 B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword χ hχ hχ1 horder
    mass ρ hmass hρ hρhalf
  filter_upwards [he hΛ hlocal hsmallPoint hsmallL2 hrootTarget hrootStop hcenter hspan hspanF hspanC
    hHistory q hvq hqH hq1 B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword
    χ hχ hχ1 horder mass ρ hmass hρ hρhalf] with t ht
  intro hactive r hqr hrt a age sharp K c e0 e1
  have hf:=MixedPastNativeSpatialFields.measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q r t
  obtain ⟨B,hB,hbound⟩:=MixedPastNativeSpatialFields.bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q r t
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hrf:r<ActualMeanKernel.fixedTerminal
      (R:=ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) (b:ℝ) k t:=by
    simpa only [QuarterSpatialEvent.anchor,ActualMeanKernel.terminal_separated Zero (b:ℝ) (fun _=>rfl)] using hrt
  have hs(ω:Ω):NativeRandomKernel.integralOperator (Spatial k q q t) ω=
      (NativeRandomKernel.integralOperator (Spatial k q r t) ω).comp
        (circleHeatOperator (r-(q:ℝ)) (sub_nonneg.mpr hqr)):=
    MixedPastNativeKernelSemigroup.operator_split
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      k q r t hqr hrf ω
  have hcU:Measurable (fun ω=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first (q,ω)):=
    (S.first_coefficient.mono (predictable_le_product 𝓕)).measurable.comp
      (measurable_const.prodMk measurable_id)
  have hh0:=NativeKernelEnergyHaar.heated_trace μ hf hB hbound hmass hρ.le
    (ht hactive r hqr hrt).1 (ht hactive r hqr hrt).2 hκ hκ.le (sub_nonneg.mpr hqr)
    (fun _:Ω=>AdditiveHaarForcing.constantField κ hκ) measurable_const
  have hh1:=NativeKernelEnergyHaar.heated_trace μ hf hB hbound hmass hρ.le
    (ht hactive r hqr hrt).1 (ht hactive r hqr hrt).2 hell hM (sub_nonneg.mpr hqr)
    (fun ω=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first (q,ω)) hcU
  have h0:Integrable e0 μ ∧ (∫ω,e0 ω ∂μ)≤κ*(((1+k:ℕ):ℝ)^2*(4*Real.pi^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
            (NativeHeatSpan.clock ((b:ℝ)-r))^ρ*((c*K)^2*
              (8*sharp^2*CurrentEnergy k q t p χ Cdim Bcur+2*PastEnergy k q t A0 ν Bword))):=by
    convert! hh0 using 1 <;> simp only [e0,hs,ContinuousLinearMap.comp_apply,c,K,sharp,a,age,Cf,Cdim]
  have h1:Integrable e1 μ ∧ (∫ω,e1 ω ∂μ)≤M*(((1+k:ℕ):ℝ)^2*(4*Real.pi^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
            (NativeHeatSpan.clock ((b:ℝ)-r))^ρ*((c*K)^2*
              (8*sharp^2*CurrentEnergy k q t p χ Cdim Bcur+2*PastEnergy k q t A0 ν Bword))):=by
    convert! hh1 using 1 <;> simp only [e1,hs,ContinuousLinearMap.comp_apply,c,K,sharp,a,age,Cf,Cdim]
  refine ⟨h0.1,h1.1,?_⟩
  nlinarith only [h0.2,h1.2]
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
      let e0:Ω→ℝ:=fun ω=>∑'j:HaarNode,‖OneInputOperator.besselHalf mass ρ hmass hρ.le
        (NativeRandomKernel.integralOperator (Spatial k q q t) ω
          (CircleNormalization.push (globalHaarColumn j (AdditiveHaarForcing.constantField κ hκ).1)))‖^2
      let e1:Ω→ℝ:=fun ω=>∑'j:HaarNode,‖OneInputOperator.besselHalf mass ρ hmass hρ.le
        (NativeRandomKernel.integralOperator (Spatial k q q t) ω
          (CircleNormalization.push (globalHaarColumn j
            (ContinuousHeatMild.coefficientFunction haU hell hbU S.first (q,ω)).1)))‖^2
      Integrable e0 μ ∧ Integrable e1 μ ∧
        (∫ω,e0 ω ∂μ)+(∫ω,e1 ω ∂μ)≤(κ+M)*(((1+k:ℕ):ℝ)^2*(4*Real.pi^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
            (NativeHeatSpan.clock ((b:ℝ)-r))^ρ*((c*K)^2*
              (8*sharp^2*CurrentEnergy k q t p χ Cdim Bcur+2*PastEnergy k q t A0 ν Bword))) :=by
  exact ⟨NativeUniversalConstants.rowHorizon (1+k),NativeUniversalConstants.rowConstant (1+k),NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega),NativeUniversalConstants.currentConstant.{0} (1+k) (by omega),NativeUniversalConstants.rowHorizon_pos (1+k),NativeUniversalConstants.rowConstant_pos (1+k),NativeUniversalConstants.currentHorizon_pos.{0} (1+k) (by omega),NativeUniversalConstants.currentHorizon_le_one.{0} (1+k) (by omega),NativeUniversalConstants.currentConstant_pos.{0} (1+k) (by omega),actual_energy_fixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm k⟩

end SHE.MixedPastNativeHaarEnergy
