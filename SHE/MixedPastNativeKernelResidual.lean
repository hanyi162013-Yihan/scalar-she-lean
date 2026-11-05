module

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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeKernelResidual
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

include hIJ₀ hIJ₁ in
/-- The literal covariance/baseline FTC residual on genuine original
relative-output sections. All conditional moments, changing laws,
full-age RMS theta integrability and native-direction applicability are
derived from the actual solution and one common history event. -/
theorem actual_residual
    (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH:v≤H)(hv1:(v:ℝ)≤1)(Bpast:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hrootStop:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(k:ℕ)
    (hHistory:∀j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (q:ℝ≥0)(hvq:v<q)(hqH:q≤H):
    ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      QuarterSpatialEvent.active Zero (b:ℝ) k q t→
      ∀ᵐw:Fin k→HeatCircle∂Measure.pi (fun _=>haarAddCircle),
      ∀ᵐx:HeatCircle∂haarAddCircle,
      let h:=separated k (x,t,fun i=>w i+x)
      let anchor:=QuarterSpatialEvent.anchor k t
      ∀(hp0:StrictHistory Zero k anchor)(A0 ν:ℝ),0≤A0→0≤ν→
      (∀j,j≤k→∀z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j)→
      ∀(B0:ℝ≥0),StandardTerminalBDGPower (k+2) J B0→
      ∀(r:ℝ)(y:HeatCircle),
      let E:=heatRow ((carrier Zero k).observations.observations h) r y
      let target:=fun i=>targets Zero k h i-(v:ℝ)
      let R:=NativeFirstScoreReserve.covariance P target target (centers Zero k h) ((q:ℝ)-(v:ℝ))
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range→
      let K:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k anchor*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k anchor)
          (carrier_orderedTimes Zero (fun x i=>by
            change (Z.observations x i).stop≤(Z.observations x i).target
            rw [hrootStop,hrootTarget]) k anchor hp0)
          (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w)
      MemLp (RowResidual k q r t w (y,x)) 2 μ ∧
      ProfileL2.normTwo μ (RowResidual k q r t w (y,x))≤
        K*Real.sqrt (RowVariance k q r t w (y,x))*AAmp k q t w A0 ν B0 x:=by
  have hnative:∀x i,(Z.observations x i).stop=(Z.observations x i).target:=by
    intro x i
    rw [hrootStop,hrootTarget]
  have hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target:=fun x i=>(hnative x i).le
  have hrootLe:∀x i,(Z.observations x i).stop≤(b:ℝ):=fun x i=>(hrootStop x i).le
  have hT0:∀x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have hsource:=MixedPastNativeResidualLegBound.actual_bound_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallPoint hvH hv1 Bpast hBDGpast
    hrootStop hages hspan haarAddCircle k
  have hs:=HistoryProductMeasure.ae_relative_old_first _ k hsource
  have hl:=MixedPastNativeLeafThetaSections.leaf_rms_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint hsmallL2 hvH hv1 Bpast hBDGpast k
  filter_upwards [hs,hl] with t hst hlt
  intro ht
  filter_upwards [hst] with w hw
  have hm:=MixedPastNativeThetaSections.mass_rms_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint hsmallL2 hvH hv1 Bpast hBDGpast
    hages hrootTarget hrootStop hcenter hspan k q hvq t ht w
  have hleafs:=ae_all_iff.mpr (fun j:Fin k=>hlt ht.1 w j)
  filter_upwards [hw,hm,hleafs] with x hx hxmass hxleaf
  intro h anchor hp0 A0 ν hA0 hν hjet B0 hBDG0 r y E target R hE K
  have hp:StrictHistory Zero k h:=
    (FixedHistoryTimeFactors.strict_sections Zero b hT0 k t x 0 (fun i=>w i+x) (fun _=>0)).mpr ht.1
  have hqt:(q:ℝ)<(carrier Zero k).terminal h:=by
    change (q:ℝ)<(carrier Zero k).terminal (separated k (x,t,fun i=>w i+x))
    rw [ActualMeanKernel.terminal_separated Zero b hT0]
    exact ht.2
  have hsmall:SmallHistory Zero (uniformHorizon 1) k h:=
    RelativeHistoryGeometry.smallHistory_of_span Zero b (fun x=>(hT0 x).le)
      (fun x i=>(hrootTarget x i).le) _ k hHistory h
  have hn:stops Zero k h=targets Zero k h:=NativeCarrierGeometry.stops_eq_targets Zero hnative hrootLe k h
  have hEr:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P
      (fun i=>stops Zero k h i-(v:ℝ)) target (centers Zero k h) ((q:ℝ)-(v:ℝ)))).range:=by
    rw [hn]
    exact hE
  have hb:=hx q hvq.le hqH hqt hp hsmall A0 ν hA0 hν hjet B0 hBDG0 E hEr hxmass hxleaf
  have hold:=NativeCurrentCoordinates.old_envelope_relative
    Λ P haP v b hvb Z htarget hstop F hF hFm hrootTarget hages hcenter k t w x hp hp0
  have hAmp:=MixedPastNativeAAmplitude.relative
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hrootTarget hrootStop hcenter k q t w A0 ν B0 x
  have hLeg:RowResidual k q r t w (y,x)=
      MixedPastNativeResidualLegs.legIntegral
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q h E:=rfl
  have hRR:RowVariance k q r t w (y,x)=scoreVariance
      (NativeFirstScoreReserve.covariance P (fun i=>stops Zero k h i-(v:ℝ)) target
        (centers Zero k h) ((q:ℝ)-(v:ℝ))) E:=by
    change scoreVariance (NativeFirstScoreReserve.covariance P target target (centers Zero k h) ((q:ℝ)-(v:ℝ))) E=_
    rw [hn]
  rw [hLeg,hRR]
  refine ⟨hb.1,?_⟩
  have hh:=hb.2
  rw [hold,hAmp] at hh
  exact hh

end SHE.MixedPastNativeKernelResidual
