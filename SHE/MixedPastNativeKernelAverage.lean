module

public import SHE.MixedPastNativeKernel
public import SHE.ForestTranslation
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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeKernelAverage
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

local notation "Diff"=>MixedPastNativeKernel.difference
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Field"=>MixedPastNativeKernel.field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- The actual old-space integral of the COMPLETE original kernel
change, retaining the original output root and the same sample. -/
def spatial (k:ℕ) (q:ℝ≥0) (r:ℝ) (t:Fin k→ℝ) (z:Ω×(HeatCircle×HeatCircle)):ℂ:=
  ((∫w:Fin k→HeatCircle,Diff k q r (separated k (z.2.2,t,w)) z.2.1 z.1
    ∂Measure.pi (fun _=>AddCircle.haarAddCircle)):ℝ)

local notation "Spatial"=>spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Joint old-space/sample/input/output measurability precedes the
actual native column and Bessel averages. -/
theorem field_joint_measurable (k:ℕ) (q:ℝ≥0) (r:ℝ) (t:Fin k→ℝ):
    Measurable (fun z:((Fin k→HeatCircle)×Ω)×(HeatCircle×HeatCircle)=>
      Field k q r t z.1.1 (z.1.2,z.2)):=by
  have hs:Measurable (fun z:((Fin k→HeatCircle)×Ω)×(HeatCircle×HeatCircle)=>
      separated k (z.2.2,t,fun i=>z.1.1 i+z.2.2)):=
    (separated_measurable k).comp (measurable_snd.snd.prodMk
      (measurable_const.prodMk (measurable_pi_iff.mpr (fun i=>
        ((measurable_pi_apply i).comp measurable_fst.fst).add measurable_snd.snd))))
  have hh:=Complex.continuous_ofReal.measurable.comp
    ((MixedPastNativeKernel.difference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k q r).comp
        ((measurable_fst.snd.prodMk hs).prodMk measurable_snd.fst))
  convert! hh using 1

theorem average_eq_spatial (k:ℕ) (q:ℝ≥0) (r:ℝ) (t:Fin k→ℝ)
    (ω:Ω) (y x:HeatCircle):
    (∫w:Fin k→HeatCircle,Field k q r t w (ω,(y,x)) ∂Measure.pi (fun _=>AddCircle.haarAddCircle))=
      Spatial k q r t (ω,(y,x)):=by
  unfold MixedPastNativeKernel.field spatial
  rw [integral_complex_ofReal]
  congr 1
  exact (OrderedHeatForests.relativeShift_preserving k x).integral_comp'
    (fun w:Fin k→HeatCircle=>Diff k q r (separated k (x,t,w)) y ω)

attribute [local irreducible] MixedPastNativeKernel.field MixedPastNativeKernel.difference spatial

/-- The Bessel output of the ACTUAL old-space average equals the
old-space average of its actual native negative kernels, samplewise. -/
theorem negative_average (k:ℕ) (q:ℝ≥0) (r:ℝ) (t:Fin k→ℝ)
    {mass ρ:ℝ} (hmass:1≤mass) (hρ:0≤ρ) (ω:Ω):
    NativeRandomKernel.negativeKernel mass ρ hmass hρ (Spatial k q r t) ω=
      ∫w:Fin k→HeatCircle,NativeRandomKernel.negativeKernel mass ρ hmass hρ
        (Field k q r t w) ω ∂Measure.pi (fun _=>AddCircle.haarAddCircle):=by
  let ν:Measure (Fin k→HeatCircle):=Measure.pi (fun _=>AddCircle.haarAddCircle)
  let G:(Fin k→HeatCircle)×(HeatCircle×HeatCircle)→ℂ:=fun z=>Field k q r t z.1 (ω,z.2)
  have hmap:Measurable (fun z:(Fin k→HeatCircle)×(HeatCircle×HeatCircle)=>((z.1,ω),z.2)):=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hm0:=(field_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q r t).comp hmap
  have hm:Measurable G:=by convert! hm0 using 1
  obtain ⟨B,hB,hbound⟩:=MixedPastNativeKernel.field_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q r t
  have hh:=NativeKernelParameterAverage.negative_average ν hm hB (fun w y x=>hbound w ω y x) hmass hρ
  have heq:NativeKernelParameterAverage.average ν G=(fun z:Unit×(HeatCircle×HeatCircle)=>Spatial k q r t (ω,z.2)):=by
    funext z
    exact average_eq_spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k q r t ω z.2.1 z.2.2
  rw [heq] at hh
  convert! hh using 1

end SHE.MixedPastNativeKernelAverage
