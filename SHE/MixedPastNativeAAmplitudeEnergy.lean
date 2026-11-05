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
public import SHE.MixedPastNativeAAmplitudeFields
public import SHE.ScalarFiniteEnergyAdd
@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeAAmplitudeEnergy
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

/-- The physical additive past amplitude is genuinely nonnegative. -/
theorem nonneg (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(A0 ν:ℝ)(B0:ℝ≥0)(x:HeatCircle):
    0≤Amp k q t w A0 ν B0 x:=by
  dsimp only [MixedPastNativeAAmplitude.amplitude]
  refine add_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (div_nonneg (MixedPastWordMoments.total_nonneg P _ _ _ A0 ν) (by norm_num))) ?_)
    (Finset.sum_nonneg (fun j _=>mul_nonneg (Real.sqrt_nonneg _) ?_))
  · exact integral_nonneg (fun _=>Real.sqrt_nonneg _)
  · dsimp only [MixedPastNativeBaselineThetaGain.amplitude]
    exact mul_nonneg (NativeOmittedTimeTotal.total_nonneg P _ _ _ j A0 ν)
      (integral_nonneg (fun _=>Real.sqrt_nonneg _))

attribute [local irreducible] MixedPastNativeCovarianceThetaEnergy.amplitude
  MixedPastNativeBaselineThetaGain.amplitude MixedPastWordMoments.total NativeOmittedTimeTotal.total

include hIJ₀ hIJ₁ in
/-- The actual COMPLETE additive A amplitude has true spatial L2
energy, with full original erased-leaf ages already restored. The
finite-sum cost is k+1, without a depth-dependent fresh-gap exponent. -/
theorem actual_energy (hΛ:0≤Λ)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH:v≤H)(hv1:(v:ℝ)≤1)(Bpast:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(k:ℕ):
    ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Set.Ioc (v:ℝ) (b:ℝ))),
      ∀hp:StrictHistory Zero k (anchor k t),∀q:ℝ≥0,v<q→
      (q:ℝ)<(carrier Zero k).terminal (anchor k t)→
      ∀w:Fin k→HeatCircle,∀A0 ν:ℝ,∀B0:ℝ≥0,
      let a:=anchor k t
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
      let A:=Amp k q t w A0 ν B0
      Integrable (fun x=>A x^2) haarAddCircle ∧
        (∫x,A x^2 ∂haarAddCircle)≤((k:ℝ)+1)*
          (c^2*(Cmass^2*D)+∑j:Fin k,(d j)^2*(Cbase^2*D)):=by
  filter_upwards [MixedPastNativeBaselineThetaGain.actual_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint hsmallL2 hvH hv1 Bpast hBDGpast hages k]
    with t ht
  intro hp q hvq hqt w A0 ν B0 a age sharp C0 c d Cmass Cbase D A
  have hactive:active Zero (b:ℝ) k q t:=by
    refine ⟨hp,?_⟩
    rw [←ActualMeanKernel.terminal_separated Zero (b:ℝ) (fun _=>rfl) k t (0:HeatCircle) (fun _=>0)]
    exact hqt
  have hc:=MixedPastNativeCovarianceThetaEnergy.actual_past_average_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint hsmallL2 hvH hv1 Bpast hBDGpast
    hages hspan k q hvq t hactive w
  have hb:=fun j:Fin k=>ht hp q hvq hqt w j A0 ν
  have hcm:=MixedPastNativeAAmplitudeFields.covariance_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint k q t w
  have hbm:=fun j:Fin k=>MixedPastNativeAAmplitudeFields.baseline_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint k t w j A0 ν
  have hc2:MemLp (CovAmp k q t w) 2 haarAddCircle:=
    (memLp_two_iff_integrable_sq hcm.aestronglyMeasurable).mpr hc.1
  have hb2:∀j:Fin k,MemLp (BaseAmp k t w j A0 ν) 2 haarAddCircle:=fun j=>
    (memLp_two_iff_integrable_sq (hbm j).aestronglyMeasurable).mpr (hb j).1
  let f:HeatCircle→ℝ:=fun x=>c*CovAmp k q t w x
  let g:Fin k→HeatCircle→ℝ:=fun j x=>d j*BaseAmp k t w j A0 ν x
  have hf2:MemLp f 2 haarAddCircle:=hc2.const_mul c
  have hg2:∀j:Fin k,MemLp (g j) 2 haarAddCircle:=fun j=>(hb2 j).const_mul (d j)
  have he:=ScalarFiniteEnergyAdd.bound haarAddCircle f g hf2 hg2
  have hA:A=(fun x=>f x+∑j,g j x):=by
    funext x
    rfl
  rw [hA]
  refine ⟨he.1,he.2.trans ?_⟩
  have hfBound:(∫x,(f x)^2 ∂haarAddCircle)≤c^2*(Cmass^2*D):=by
    have hi: (fun x=>(f x)^2)=(fun x=>c^2*(CovAmp k q t w x)^2):=by funext x;dsimp only [f];ring
    rw [hi,integral_const_mul]
    exact mul_le_mul_of_nonneg_left hc.2 (sq_nonneg c)
  have hgBound:∀j:Fin k,(∫x,(g j x)^2 ∂haarAddCircle)≤(d j)^2*(Cbase^2*D):=by
    intro j
    have hi: (fun x=>(g j x)^2)=(fun x=>(d j)^2*(BaseAmp k t w j A0 ν x)^2):=by funext x;dsimp only [g];ring
    rw [hi,integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hb j).2 (sq_nonneg (d j))
  simpa only [Fintype.card_fin] using
    mul_le_mul_of_nonneg_left (add_le_add hfBound (Finset.sum_le_sum (fun j _=>hgBound j)))
      (show 0≤(k:ℝ)+1 by positivity)

end SHE.MixedPastNativeAAmplitudeEnergy
