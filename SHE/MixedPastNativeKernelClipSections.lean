module

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

namespace SHE.MixedPastNativeKernelClipSections
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

/-- The actual complete FTC cap on genuine relative old-space sections.
The source is one original history event uniform in all current times,
means and native directions; no adaptive spatial diagonal is used. -/
theorem actual_clip_sections (hΛ:0≤Λ)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hrootNative:∀x i,(Z.observations x i).stop=(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(k:ℕ):
    ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      ∀ᵐw:Fin k→HeatCircle∂Measure.pi (fun _=>haarAddCircle),
      ∀ᵐx:HeatCircle∂haarAddCircle,
      let h:=separated k (x,t,fun i=>w i+x)
      let anchor:=QuarterSpatialEvent.anchor k t
      ∀q:ℝ≥0,v≤q→(q:ℝ)<(carrier Zero k).terminal h→
      ∀ r : ℝ, (q:ℝ) ≤ r → r < (carrier Zero k).terminal h →
      ∀hp:StrictHistory Zero k h,∀hp0:StrictHistory Zero k anchor,
      SmallHistory Zero (uniformHorizon 1) k h→
      ∀A0 ν:ℝ,0≤A0→0≤ν→
      (∀j,j≤k→∀z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j)→
      ∀p:ℕ,0<p→∀χ:ℝ,0≤χ→χ≤1→∀y:HeatCircle,
      let target:=fun i=>targets Zero k h i-(v:ℝ)
      let R:=NativeFirstScoreReserve.covariance P target target (centers Zero k h) ((q:ℝ)-(v:ℝ))
      let E:=heatRow ((carrier Zero k).observations.observations h) r y
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range→
      let K:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k anchor*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k anchor)
          (carrier_orderedTimes Zero (fun x i=>(hrootNative x i).le) k anchor hp0)
          (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w)
      let T:=MixedPastWordMoments.total (d:=1) P
        (fun j=>lower Zero k anchor j-(v:ℝ)) (fun j=>upper Zero k anchor j-(v:ℝ))
        (fun j=>targets Zero k anchor (leafIndex k (fun i=>i) j)-(v:ℝ)) A0 ν
      ∀ω:Ω,|(Field k q r t w (ω,(y,x))).re|≤
        2*(K*Real.sqrt (RowVariance k q r t w (y,x))*T)*|Current k q t w p χ (ω,x)|+
          |RowResidual k q r t w (y,x) ω|:=by
  have hsource:=MixedPastNativeMeanFTCClip.actual_clip_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hΛ hsmallPoint hrootNative hrootStop hspan haarAddCircle k
  have hsections:=HistoryProductMeasure.ae_relative_old_first _ k hsource
  filter_upwards [hsections] with t ht
  filter_upwards [ht] with w hw
  filter_upwards [hw] with x hx
  intro h anchor q hvq hqt r hqr hrt hp hp0 hsmall A0 ν hA0 hν hjet p hpχ χ hχ hχ1
    y target R E hE K T ω
  have hc:=hx q hvq hqt hp hsmall A0 ν hA0 hν hjet p hpχ χ hχ hχ1 E hE ω
  let mean:=fun θ=>MixedPastNativeConsistentPoint.meanField
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q ω h
  have hpoint(θ:ℝ):MixedPastNativeConsistentPoint.point
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q r h y ω=
      fderiv ℝ (ActualMeanKernel.cappedAverage (Base (θ,(U ω,Dir ω))) k q h) (mean θ) E:=by
    have hterm:(carrier (Base (θ,(U ω,Dir ω))) k).terminal h=(carrier Zero k).terminal h:=
      ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
        (θ,(U ω,Dir ω)) (0,(0,0)) k h
    have hqtθ:(q:ℝ)<(carrier (Base (θ,(U ω,Dir ω))) k).terminal h:=by rw [hterm];exact hqt
    have hrtθ:r<(carrier (Base (θ,(U ω,Dir ω))) k).terminal h:=by rw [hterm];exact hrt
    unfold MixedPastNativeConsistentPoint.point
    rw [ActualMeanKernel.rowPoint_of_active _ _ _ _ _ _ _ hqtθ hrtθ]
    simp only [ActualMeanKernel.cappedAverage,min_eq_left hqtθ.le]
    rw [ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (θ,(U ω,Dir ω)) (0,(0,0)) k h]
  have hold:=NativeCurrentCoordinates.old_envelope_relative
    Λ P haP v b hvb Z htarget hstop F hF hFm hrootTarget (fun x i=>(hrootNative x i).le)
    hcenter k t w x hp hp0
  have hCur:=NativeCurrentCoordinates.current_factor_relative
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hrootTarget hcenter k q t w x p χ ω
  have hT0:∀x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have hl:=FixedHistoryTimeFactors.lower_sections Zero b hT0 k t x 0 (fun i=>w i+x) (fun _=>0)
  have hu:=FixedHistoryTimeFactors.upper_sections Zero b hT0 k t x 0 (fun i=>w i+x) (fun _=>0)
  have htar:=FixedHistoryTimeFactors.targets_sections Zero b hT0 (fun _:Fin 1=>(b:ℝ)) hrootTarget
    k t x 0 (fun i=>w i+x) (fun _=>0)
  have hscale:MixedPastWordMoments.total (d:=1) P
      (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ))
      (fun j=>target (leafIndex k (fun i=>i) j)) A0 ν=T:=by
    dsimp only [target,T,h,anchor]
    rw [hl,hu,htar]
    rfl
  have hK:0≤K:=mul_nonneg
    (timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1)
      (fun j=>(uniformConstant_pos 1 j).le) k anchor hp0)
    (OrderedHeatForests.parentDensity_nonneg 2 (by norm_num) k _ _ _)
  have hT:0≤T:=MixedPastWordMoments.total_nonneg P _ _ _ A0 ν
  have hh:=hc.2
  change |fderiv ℝ (ActualMeanKernel.cappedAverage (Base (1,(U ω,Dir ω))) k q h) (mean 1) E-
      fderiv ℝ (ActualMeanKernel.cappedAverage (Base (0,(U ω,Dir ω))) k q h) (mean 0) E|≤_ at hh
  have hFfield:|(Field k q r t w (ω,(y,x))).re|=
      |fderiv ℝ (ActualMeanKernel.cappedAverage (Base (1,(U ω,Dir ω))) k q h) (mean 1) E-
        fderiv ℝ (ActualMeanKernel.cappedAverage (Base (0,(U ω,Dir ω))) k q h) (mean 0) E|:=by
    simp only [MixedPastNativeKernel.field,MixedPastNativeKernel.difference,Complex.ofReal_re]
    change |MixedPastNativeConsistentPoint.point
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k 1 q r h y ω-
      MixedPastNativeConsistentPoint.point
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k 0 q r h y ω|=_
    rw [hpoint,hpoint]
  rw [hFfield]
  dsimp only at hh
  rw [hold,hscale,hCur] at hh
  change _≤2*(K*Real.sqrt (RowVariance k q r t w (y,x))*T)*Current k q t w p χ (ω,x)+
    |RowResidual k q r t w (y,x) ω| at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left (le_abs_self _)
    (by positivity : 0≤2*(K*Real.sqrt (RowVariance k q r t w (y,x))*T))) le_rfl)

end SHE.MixedPastNativeKernelClipSections
