module

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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeMeanFTCClip
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeMeanFTCClip_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeMeanFTCClip_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeMeanFTCClip_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeMeanFTCClip_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeMeanFTCClip_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeMeanFTCClip_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
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
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open scoped BigOperators
local instance mixedPastNativeMeanFTCClip_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

/-- Actual complete clipped native kernel, with its additive residual
identified as the original covariance-plus-baseline FTC integral. -/
theorem actual_clip_ae (hΛ:0≤Λ)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hrootNative:∀x i,(Z.observations x i).stop=(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k,
      ∀q:ℝ≥0,v≤q→(q:ℝ)<(carrier Zero k).terminal h→
      ∀hp:StrictHistory Zero k h,SmallHistory Zero (uniformHorizon n) k h→
      ∀A0 ν:ℝ,0≤A0→0≤ν→
      (∀j,j≤k→∀z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j)→
      ∀p:ℕ,0<p→∀χ:ℝ,0≤χ→χ≤1→
      let target:=fun i=>targets Zero k h i-(v:ℝ)
      let lo:=fun j=>lower Zero k h j-(v:ℝ)
      let hi:=fun j=>upper Zero k h j-(v:ℝ)
      let a:=fun i=>NativeHeatSpan.unitCenter (centers Zero k h i)
      let R:=NativeFirstScoreReserve.covariance P target target (centers Zero k h) ((q:ℝ)-(v:ℝ))
      ∀E:WordRecursion.State (n+k),E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range→∀ω:Ω,
      let mean:=fun θ=>MixedPastNativeConsistentPoint.meanField
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q ω h
      let Point:=fun θ=>fderiv ℝ (ActualMeanKernel.cappedAverage
        (Base (θ,(U ω,Dir ω))) k q h) (mean θ) E
      let old:=timeWeight Zero (fraction P*P.lower) (uniformConstant n) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero (fun x i=>(hrootNative x i).le) k h hp) (centers Zero k h)
      let T:=MixedPastWordMoments.total (d:=n) P lo hi
        (fun j=>target (leafIndex k (fun i=>i) j)) A0 ν
      let G:=MixedPastNativePacketUniform.packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        (r:=k) P v q target target a (leafIndex k (fun i=>i)) p (ω,0)
      let Dcur:=MixedNativeDampedScoreAmplitude.amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P v q target a lo hi (ω,0)
      let A:=fun θ=>ControlledFamilyNativeLegs.covarianceLeg P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
        (U ω,Dir ω) k h q (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) E θ+
        ControlledFamilyNativeLegs.baselineLeg P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
          (U ω,Dir ω) k h q (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) E θ
      IntervalIntegrable A volume 0 1 ∧
        |Point 1-Point 0|≤2*(old*Real.sqrt (scoreVariance R E)*T)*(Dcur^χ*G)+|∫θ in (0:ℝ)..1,A θ| :=by
  have hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target:=fun x i=>(hrootNative x i).le
  have hroot:∀x i,(Z.observations x i).stop=(b:ℝ):=fun x i=>le_antisymm (hrootStop x i) (hstop x i)
  filter_upwards [MixedPastNativeMeanClip.actual_clip_ae
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      hΛ hrootNative hrootStop hspan ρ k,
    ControlledFamilyNativePacketFTC.residual_all_parameters_ae
      P haP Λ v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint hroot hspan ρ k,
    ControlledThetaNativeGradient.gradient_all_parameters_ae
      P haP Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hclip hres hgradient
  intro q hvq hqt hp hsmall A0 ν hA0 hν hjet p hp0 χ hχ hχ1 target lo hi a R E hE ω
    mean Point old T G Dcur A
  let D:=directions Zero ((carrier Zero k).observations.observations h) k h
  let V:=PhysicalMeanRange.dampedDirection target target a ((q:ℝ)-(v:ℝ)) Λ
    (embed (S.second q ω-S.first q ω))
  let MP:=fun θ=>TwoFreshCompleteWord.value P Λ (U ω) (Dir ω) θ ((q:ℝ)-(v:ℝ))
    target target (centers Zero k h) lo hi (mean θ) false D E V
    (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h))
  have hc:=hclip q hvq hqt hp hsmall A0 ν hA0 hν hjet p hp0 χ hχ hχ1 E hE ω
  change Integrable MP MixedNativeDampedScoreAmplitude.thetaMeasure ∧
    |Point 1-Point 0|≤2*(old*Real.sqrt (scoreVariance R E)*T)*(Dcur^χ*G)+
      |Point 1-Point 0-(∫θ,MP θ ∂MixedNativeDampedScoreAmplitude.thetaMeasure)| at hc
  let inputs:Inputs:=(U ω,Dir ω)
  let Uq:=embed (S.first q ω)
  let Dq:=embed (S.second q ω-S.first q ω)
  let Sig:=ControlledFamilyThreeLeg.sigma P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm inputs k h
  let Tar:=ControlledFamilyThreeLeg.target P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm inputs k h
  let Cen:=ControlledFamilyThreeLeg.center P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm inputs k h
  have hn:stops Zero k h=targets Zero k h:=NativeCarrierGeometry.stops_eq_targets Zero hrootNative hrootStop k h
  have hqv:(v:ℝ)≤(q:ℝ):=by exact_mod_cast hvq
  have hTar:Tar=target:=by
    unfold Tar ControlledFamilyThreeLeg.target
    rw [ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (0,inputs) (0,(0,0)) k h]
    rfl
  have hCen:Cen=a:=by
    unfold Cen ControlledFamilyThreeLeg.center
    rw [ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (0,inputs) (0,(0,0)) k h]
    rfl
  have hSig:Sig=target:=by
    unfold Sig ControlledFamilyThreeLeg.sigma
    rw [ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (0,inputs) (0,(0,0)) k h]
    funext i
    have hh:=NativeCarrierGeometry.carrier_native Zero hrootNative k h i
    exact congrArg (fun t:ℝ=>t-(v:ℝ)) hh
  let JM:=fun θ=>ControlledJointWeightedWord.jointMeanVector Sig Tar Cen ((q:ℝ)-(v:ℝ)) Λ Uq Dq θ
  let VM:=PhysicalMeanRange.dampedDirection Sig Tar Cen ((q:ℝ)-(v:ℝ)) Λ Dq
  have hV:VM=V:=by
    dsimp only [VM]
    rw [hSig,hTar,hCen]
  have hMean(θ:ℝ):JM θ=mean θ:=by
    have hh:=MixedPastNativeLegIdentity.mean_eq_meanField
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      hages hrootStop k h θ q hqt ω
    exact (ControlledFamilyActualTransfer.mean_relative P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      inputs k h q Uq Dq θ).trans hh
  let WP:=fun θ=>ControlledFamilyNativeKernelPacket.packet P haP Λ v b hvb Z htarget hstop F hF hFm
    inputs k h q θ (JM θ) E
  let FP:=fun θ=>ControlledFamilyNativeMeanPacket.packet P haP Λ v b hvb Z htarget hstop F hF hFm
    inputs k h q θ (JM θ) E VM
  have hFP:FP=MP:=by
    funext θ
    simp only [FP,ControlledFamilyNativeMeanPacket.packet,hMean,hV,hn]
    rfl
  have hWP(θ:ℝ):WP θ=Point θ:=by
    let aθ:ℝ×Inputs:=(θ,inputs)
    have hR:NativeFirstScoreReserve.covariance P (stops (Base aθ) k h) (targets (Base aθ) k h)
        (centers (Base aθ) k h) q=R:=by
      rw [ControlledThetaRelativeDerivative.stops_eq P haP Λ v b hvb Z htarget hstop F hF hFm aθ (0,(0,0)) k h,
        ControlledThetaRelativeDerivative.targets_eq P haP Λ v b hvb Z htarget hstop F hF hFm aθ (0,(0,0)) k h,
        ControlledThetaRelativeDerivative.centers_eq P haP Λ v b hvb Z htarget hstop F hF hFm aθ (0,(0,0)) k h,
        ControlledThetaTwoFreshArrays.native_relative P (v:ℝ) q,hn]
    have heθ:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P
        (stops (Base aθ) k h) (targets (Base aθ) k h) (centers (Base aθ) k h) q)).range:=by rw [hR];exact hE
    have hg:=hgradient aθ q hqv hqt (mean θ) E heθ
    have hterm:(carrier (Base aθ) k).terminal h=(carrier Zero k).terminal h:=
      ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm aθ (0,(0,0)) k h
    have hqtθ:(q:ℝ)≤(carrier (Base aθ) k).terminal h:=by rw [hterm];exact hqt.le
    simpa only [WP,ControlledFamilyNativeKernelPacket.packet,hMean,Point,ActualMeanKernel.cappedAverage,
      min_eq_left hqtθ,aθ,inputs] using hg.symm
  have hReserve:ControlledFamilyNativeLegs.reserve P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      inputs k h q=R:=by
    have hh:=MixedPastNativeLegIdentity.reserve_eq_zero
      Λ P haP v b hvb Z htarget hstop F hF hFm hroot inputs 0 k h q
    simpa only [hn] using hh
  have heR:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (ControlledFamilyNativeLegs.reserve
      P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm inputs k h q)).range:=by rw [hReserve];exact hE
  have hqtP:(q:ℝ)<(carrier (Base (0,inputs)) k).terminal h:=by
    rw [ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (0,inputs) (0,(0,0)) k h]
    exact hqt
  have hFPi:IntervalIntegrable FP volume 0 1:=by
    rw [hFP]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mpr hc.1
  have hr:=hres inputs q hqv hqtP Uq Dq E heR 0 1 hFPi
  change IntervalIntegrable A volume 0 1 ∧ WP 1-WP 0-(∫θ in (0:ℝ)..1,FP θ)=∫θ in (0:ℝ)..1,A θ at hr
  have hInt:(∫θ in (0:ℝ)..1,FP θ)=∫θ,MP θ ∂MixedNativeDampedScoreAmplitude.thetaMeasure:=by
    rw [hFP,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    rfl
  rw [hWP,hWP,hInt] at hr
  exact ⟨hr.1,by rw [←hr.2];exact hc.2⟩

end SHE.MixedPastNativeMeanFTCClip
