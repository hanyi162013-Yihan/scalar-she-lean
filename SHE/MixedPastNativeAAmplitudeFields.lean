module

public import SHE.QuarterSpatialEvent
public import SHE.ScalarRootRelativeGeometry
public import SHE.NativeCurrentOutputEnergy
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

public import SHE.MixedPastNativeThetaRMSFields
public import SHE.MixedPastNativeCovarianceMass
public import SHE.MixedPastDerivativeRMS
public import SHE.MixedPastNativeThetaCoordinates
public import SHE.MixedPastNativeCovarianceThetaJoint
public import SHE.MixedPastBaselineThetaJointSections
public import SHE.ScalarThetaSections
public import SHE.MixedPastNativeResidualThetaBound
public import SHE.MixedPastNativeCovarianceThetaEnergy
public import SHE.MixedPastNativeBaselineThetaGain
public import SHE.MixedPastNativeAAmplitude
@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeAAmplitudeFields
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





open QuarterSpatialEvent
local notation "CovAmp"=>MixedPastNativeCovarianceThetaEnergy.amplitude
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "BaseAmp"=>MixedPastNativeBaselineThetaGain.amplitude
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Amp"=>MixedPastNativeAAmplitude.amplitude
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "RelativeMass"=>MixedPastNativeCovarianceMass.scoreMass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

theorem covariance_measurable (hΛ:0≤Λ)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(w:Fin k→HeatCircle):Measurable (CovAmp k q t w):=by
  have hm:=(MixedPastNativeCovarianceThetaFields.scoreMass_joint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k q t).comp
      (measurable_snd.fst.prodMk ((measurable_fst.prodMk measurable_snd.snd).prodMk
        (measurable_const (a:=w))))
  have hGm:=ScalarFibreRMS.measurable μ _ hm
  have hh:=hGm.stronglyMeasurable.integral_prod_left' (μ:=MeanThetaAverage.thetaMeasure)
  convert! hh.measurable using 1

theorem baseline_measurable (hΛ:0≤Λ)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(j:Fin k)(A0 ν:ℝ):Measurable (BaseAmp k t w j A0 ν):=by
  let a:=anchor k t
  let age:=targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)
  have hu:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hd:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hm0:=(ControlledProfile.random_derivative_measurable P hΛ U Dir hu hd hsmall).comp
    ((measurable_fst.prodMk ((measurable_const (a:=age)).prodMk measurable_snd.snd)).prodMk measurable_snd.fst)
  have hm:Measurable (fun z:Ω×(ℝ×HeatCircle)=>MixedPastDerivativeRMS.field
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P v age z.2.1 (z.1,z.2.2)):=by
    convert! hm0 using 1
  have hGm:=ScalarFibreRMS.measurable μ _ hm
  have hi:=hGm.stronglyMeasurable.integral_prod_left' (μ:=MeanThetaAverage.thetaMeasure)
  have hshift:=hi.measurable.comp (measurable_id.add_const (w j))
  have hh:=hshift.const_mul (NativeOmittedTimeTotal.total (d:=1) P
    (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ))
    (fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)) j A0 ν)
  convert! hh using 1

theorem measurable (hΛ:0≤Λ)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(A0 ν:ℝ)(B0:ℝ≥0):
    Measurable (Amp k q t w A0 ν B0):=by
  have hc:=covariance_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k q t w
  have hb:=fun j:Fin k=>baseline_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k t w j A0 ν
  let a:=anchor k t
  let age:=fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)
  let C0:=(k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent
  have hleft:=hc.const_mul (Real.sqrt (TwoFreshCompleteWord.momentConstant P k k 1 C0)*
    (MixedPastWordMoments.total (d:=1) P (fun j=>lower Zero k a j-(v:ℝ))
      (fun j=>upper Zero k a j-(v:ℝ)) age A0 ν/2))
  have hright:=Finset.measurable_sum Finset.univ (fun j _=>(hb j).const_mul
    (Real.sqrt (NativeOmittedCompleteWord.momentConstant P k k j 1 C0)))
  have hh:=hleft.add hright
  convert! hh using 1

end SHE.MixedPastNativeAAmplitudeFields
