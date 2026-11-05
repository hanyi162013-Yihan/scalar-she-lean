module

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
public import SHE.VariableMeanOperator
public import SHE.NativeKernelSubtraction
public import SHE.NativeKernelCongruence
@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeKernelSemigroup
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

local notation "Mean"=>MixedPastLiteralPoint.meanField
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

def endpoint (θ:ℝ)(k:ℕ)(q:ℝ≥0)(r:ℝ)(t:Fin k→ℝ)(z:Ω×(HeatCircle×HeatCircle)):ℂ:=
  ActualMeanKernel.weightedSpatial (Base (θ,(U z.1,Dir z.1))) k 0 q r
    (fun _:Unit=>Mean k θ q z.1) t () z.2.1 z.2.2
local notation "Endpoint"=>endpoint
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

private theorem rowPoint_zero {R:ReferenceData}{X:Type}[MeasurableSpace X]{n:ℕ}
    (L:Level R X n)(k:ℕ)(q r:ℝ)(m:History X k→WordRecursion.State (n+k))(h:History X k)(y:HeatCircle):
    ActualMeanKernel.rowPoint L k q r m h y=ActualMeanKernel.weightedPoint L k 0 q r m h y:=by
  classical
  unfold ActualMeanKernel.rowPoint ActualMeanKernel.weightedPoint
  split_ifs
  · congr 1
    apply PiLp.ext
    intro i
    simp only [StopWeightedRows.weightedHeatRow,StopWeightedRows.diagonal_apply,
      StopWeightedRows.weights,neg_zero,zero_mul,Real.exp_zero,one_mul]
  · rfl

private theorem mean_section (k:ℕ)(θ:ℝ)(q:ℝ≥0)(ω:Ω):Measurable (Mean k θ q ω):=by
  have hh:=MixedPastLiteralFields.meanField_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q
  convert! hh.comp (measurable_const.prodMk measurable_id) using 1

/-- The complete old-space difference is the difference of its actual
random-reference endpoints, with all histories and current means fixed. -/
theorem spatial_eq_endpoint_sub (k:ℕ)(q:ℝ≥0)(r:ℝ)(t:Fin k→ℝ)(ω:Ω)(y x:HeatCircle):
    Spatial k q r t (ω,(y,x))=Endpoint 1 k q r t (ω,(y,x))-Endpoint 0 k q r t (ω,(y,x)):=by
  obtain ⟨B,hB,hbound⟩:=ControlledFamilyKernelBounds.weightedPoint_family_uniform_bound
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k (by norm_num:(0:ℝ)≤0) q r t
  have hi(θ:ℝ):Integrable (fun w:Fin k→HeatCircle=>ActualMeanKernel.weightedPoint
      (Base (θ,(U ω,Dir ω))) k 0 q r (Mean k θ q ω) (separated k (x,t,w)) y)
      (Measure.pi (fun _=>haarAddCircle)):=by
    have hm:=ActualMeanKernel.weightedPoint_variable_measurable (Base (θ,(U ω,Dir ω))) k 0
      (fun _:Unit=>(q:ℝ)) (fun _:Unit=>r) measurable_const measurable_const
      (fun _:Unit=>Mean k θ q ω) ((mean_section
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q ω).comp measurable_snd)
    have hmap:Measurable (fun w:Fin k→HeatCircle=>(((),separated k (x,t,w)),y)):=
      (measurable_const.prodMk ((separated_measurable k).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)))).prodMk measurable_const
    have hs:=hm.comp hmap
    exact Integrable.of_bound hs.aestronglyMeasurable B (ae_of_all _ (fun w=>hbound _ _ y x w))
  unfold MixedPastNativeKernelAverage.spatial endpoint ActualMeanKernel.weightedSpatial
  rw [←Complex.ofReal_sub,←integral_sub (hi 1) (hi 0)]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun w=>by
    unfold MixedPastNativeKernel.difference MixedPastNativeConsistentPoint.point
    simp only [Prod.fst,Prod.snd,rowPoint_zero]
    rfl)

/-- Exact operator subtraction for the complete endpoint kernel. This
also validates its total L2 representative before applying any noise. -/
theorem operator_eq_endpoint_sub (k:ℕ)(q:ℝ≥0)(r:ℝ)(t:Fin k→ℝ)(ω:Ω):
    NativeRandomKernel.integralOperator (Spatial k q r t) ω=
      NativeRandomKernel.integralOperator (Endpoint 1 k q r t) ω-
      NativeRandomKernel.integralOperator (Endpoint 0 k q r t) ω:=by
  let E:ℝ→Unit×(HeatCircle×HeatCircle)→ℂ:=fun θ z=>Endpoint θ k q r t (ω,z.2)
  have hm(θ:ℝ):Measurable (E θ):=by
    exact ActualMeanKernel.weightedField_measurable (Base (θ,(U ω,Dir ω))) k 0 q r
      (fun _:Unit=>Mean k θ q ω) ((mean_section
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q ω).comp measurable_snd) t
  obtain ⟨B,hB,hbound⟩:=ControlledFamilyKernelBounds.weightedSpatial_family_uniform_bound
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k (by norm_num:(0:ℝ)≤0) q r t
  have hbd(θ:ℝ)(z:Unit)(y x:HeatCircle):‖E θ (z,(y,x))‖≤B:=hbound _ _ y x
  have hh:=NativeRandomKernel.integralOperator_eq_sub ((hm 1).sub (hm 0)) (hm 1) (hm 0)
    (by positivity:0≤2*B)
    (fun z y x=>(norm_sub_le _ _).trans (by linarith [hbd 1 z y x,hbd 0 z y x]))
    (fun z y x=>(hbd 1 z y x).trans (by linarith))
    (fun z y x=>(hbd 0 z y x).trans (by linarith)) (fun _ _ _=>rfl) ()
  have hcong:=NativeKernelCongruence.operator_congr (Spatial k q r t) (E 1-E 0) ω ()
    (fun y x=>spatial_eq_endpoint_sub
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q r t ω y x)
  rw [hcong,hh]
  congr 1 <;> apply NativeKernelCongruence.operator_congr <;> intros <;> rfl

/-- The actual q-law complete endpoint difference factors through the
actual later row-r and the genuine right heat, sample by sample. -/
theorem operator_split (k:ℕ)(q:ℝ≥0)(r:ℝ)(t:Fin k→ℝ)(hqr:(q:ℝ)≤r)
    (hr:r<ActualMeanKernel.fixedTerminal
      (R:=ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) (b:ℝ) k t)(ω:Ω):
    NativeRandomKernel.integralOperator (Spatial k q q t) ω=
      (NativeRandomKernel.integralOperator (Spatial k q r t) ω).comp
        (circleHeatOperator (r-(q:ℝ)) (sub_nonneg.mpr hqr)):=by
  have hs(θ:ℝ):NativeRandomKernel.integralOperator (Endpoint θ k q q t) ω=
      (NativeRandomKernel.integralOperator (Endpoint θ k q r t) ω).comp
        (circleHeatOperator (r-(q:ℝ)) (sub_nonneg.mpr hqr)):=by
    exact ActualMeanKernel.weighted_operator_split (Base (θ,(U ω,Dir ω))) (b:ℝ) (fun _=>rfl)
      k (by norm_num:(0:ℝ)≤0) q r (fun _:Unit=>Mean k θ q ω)
      ((mean_section 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q ω).comp measurable_snd)
      t hqr (by
        have he:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
          Z htarget hstop F hF hFm (θ,(U ω,Dir ω)) (0,(0,0)) k
          (QuarterSpatialEvent.anchor k t)
        unfold QuarterSpatialEvent.anchor at he
        rw [ActualMeanKernel.terminal_separated _ (b:ℝ) (fun _=>rfl),
          ActualMeanKernel.terminal_separated _ (b:ℝ) (fun _=>rfl)] at he
        exact he ▸ hr) ()
  rw [operator_eq_endpoint_sub,operator_eq_endpoint_sub,hs 1,hs 0]
  exact (ContinuousLinearMap.sub_comp _ _ _).symm
end SHE.MixedPastNativeKernelSemigroup
