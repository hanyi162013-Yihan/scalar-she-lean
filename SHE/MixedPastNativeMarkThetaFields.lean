module
public import SHE.NativeConditionalThetaFields
public import SHE.MixedPastNativeOmitted
public import SHE.MixedPastLiteralFields
public import SHE.MixedPastNativeCovariance
public import SHE.NativeReserveRowEnvelope

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

namespace SHE.MixedPastNativeMarkThetaFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralCovariance_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralCovariance_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralCovariance_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralCovariance_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralCovariance_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralCovariance_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastLiteralCovariance_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralCovariance_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open scoped BigOperators
local instance mixedPastLiteralCovariance_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

attribute [local irreducible] MixedPastNativeCovariance.point MixedPastNativeOmitted.average
  MixedPastJointData.pastU MixedPastJointData.pastD
local notation "Point"=>MixedPastNativeCovariance.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mean"=>MixedPastLiteralPoint.meanField
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Genuine joint Borel dependence of the entire actual theta-current
mean over interpolation, physical sample and arbitrary recursive history. -/
theorem meanField_joint_measurable (k : ℕ) (q : ℝ≥0) :
    Measurable (fun z : (ℝ×Ω)×History X k=>MixedPastLiteralPoint.meanField
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k z.1.1 q z.1.2 z.2) := by
  have hU : Measurable (S.first q):=
    ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted q).measurable.mono (𝓕.le q) le_rfl
  have hV : Measurable (S.second q):=
    ((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted q).measurable.mono (𝓕.le q) le_rfl
  apply (WithLp.measurable_toLp 2 (Fin (n+k)→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hT : Measurable (fun h : History X k=>targets Zero k h i):=
    (carrier Zero k).observations.target_measurable i
  have hx : Measurable (fun h : History X k=>centers Zero k h i):=
    (carrier Zero k).observations.center_measurable i
  have hs : Measurable (fun h : History X k=>stops Zero k h i):=by
    change Measurable (fun h : History X k=>min ((carrier Zero k).observations.observations h i).stop (b:ℝ))
    exact ((carrier Zero k).observations.stop_measurable i).min measurable_const
  have harg : Measurable (fun z : (ℝ×Ω)×History X k=>(targets Zero k z.2 i-(q:ℝ),centers Zero k z.2 i)):=
    ((hT.comp measurable_snd).sub_const (q:ℝ)).prodMk (hx.comp measurable_snd)
  have hu:=NativeHeatObservation.functional_joint_measurable.comp
    ((hU.comp measurable_fst.snd).prodMk harg)
  have hD : Measurable (fun ω=>S.second q ω-S.first q ω):=
    (((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted q).sub
      ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted q)).measurable.mono (𝓕.le q) le_rfl
  have hd:=NativeHeatObservation.functional_joint_measurable.comp
    ((hD.comp measurable_fst.snd).prodMk harg)
  have he : Measurable (fun z : (ℝ×Ω)×History X k=>z.1.1*exp (-Λ*(stops Zero k z.2 i-(q:ℝ)))):=
    measurable_fst.fst.mul (((hs.comp measurable_snd).sub_const (q:ℝ)).const_mul (-Λ)).exp
  have hh:=hu.add (he.mul hd)
  convert! hh using 1
  funext z
  simp only [MixedPastLiteralPoint.meanField,MixedPastJointData.mean,MixedNativePastThetaCentering.current,
    WithLp.ofLp_toLp,sub_add_cancel,Function.comp_def,Pi.add_apply,Pi.mul_apply]

/-- Genuine joint theta/sample Borel covariance mark, BEFORE actual
sample-L2 interpolation averaging. The signed profile multiplier stays
outside the complete dependent Gaussian packet. -/
theorem point_measurable (hΛ:0≤Λ)
    (hsmall:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ)(q:ℝ≥0)(h:History X k)(E:WordRecursion.State (n+k)):
    Measurable (fun z:ℝ×Ω=>Point k z.1 q h E z.2):=by
  let σ:=fun i=>stops Zero k h i-(v:ℝ)
  let target:=fun i=>targets Zero k h i-(v:ℝ)
  let lo:=fun j=>lower Zero k h j-(v:ℝ)
  let hi:=fun j=>upper Zero k h j-(v:ℝ)
  have hU:=(MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hd:=(MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hmean0:=(meanField_joint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q).comp
      (measurable_id.prodMk (measurable_const (a:=h)))
  have hmean:Measurable (fun z:(ℝ×Ω)×StoppedGaussianFeatures.Domain=>Mean k z.1.1 q z.1.2 h):=
    hmean0.comp measurable_fst
  have hV:Measurable (fun z:(ℝ×Ω)×StoppedGaussianFeatures.Domain=>
      StoppedGaussianFeatures.stoppedRow σ target (centers Zero k h) z.2):=
    (StoppedGaussianFeatures.stoppedRow_measurable σ target (centers Zero k h)).comp measurable_snd
  have hp:=NativeConditionalThetaFields.value_measurable P Λ ((q:ℝ)-(v:ℝ))
    (fun z:(ℝ×Ω)×StoppedGaussianFeatures.Domain=>U z.1.2)
    (fun z:(ℝ×Ω)×StoppedGaussianFeatures.Domain=>Dir z.1.2)
    (hU.comp measurable_fst.snd) (hd.comp measurable_fst.snd)
    (fun z=>z.1.1) measurable_fst.fst σ target (centers Zero k h) lo hi _ hmean true
    (fun _=>directions Zero ((carrier Zero k).observations.observations h) k h) (fun _=>measurable_const)
    (fun _=>E) _ measurable_const hV (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i))
    (F (rootParameter k h)) ((hF.smooth _).continuous.measurable)
  have he:=(ControlledProfile.random_derivative_measurable P hΛ U Dir hU hd hsmall).comp
    ((measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst)
  have hh:=((he.mul hp).stronglyMeasurable.integral_prod_right'
    (ν:=StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ)))).measurable.const_mul (1/2:ℝ)
  convert! hh using 1
  funext z
  simp only [MixedPastNativeCovariance.point,MixedPastLiteralPoint.meanField,σ,target,lo,hi,Function.comp_apply,Function.comp_def,Pi.mul_apply,id_eq]

/-- The complete native omitted packet is jointly Borel in theta and
actual sample before it is multiplied by the correlated leaf input. -/
theorem omitted_measurable (k:ℕ)(q:ℝ≥0)(h:History X k)(E:WordRecursion.State (n+k))(j0:Fin k):
    Measurable (fun z:ℝ×Ω=>MixedPastNativeOmitted.average
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k z.1 q h E j0 z.2):=by
  let σ:=fun i=>stops Zero k h i-(v:ℝ)
  let target:=fun i=>targets Zero k h i-(v:ℝ)
  let lo:=fun j=>lower Zero k h j-(v:ℝ)
  let hi:=fun j=>upper Zero k h j-(v:ℝ)
  have hU:=(MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hd:=(MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hmean:=(meanField_joint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q).comp
      (measurable_id.prodMk (measurable_const (a:=h)))
  have hh:=NativeConditionalThetaFields.omitted_value_measurable P Λ ((q:ℝ)-(v:ℝ))
    (fun z:ℝ×Ω=>U z.2) (fun z:ℝ×Ω=>Dir z.2) (hU.comp measurable_snd) (hd.comp measurable_snd)
    Prod.fst measurable_fst σ target (centers Zero k h) lo hi _ hmean
    (fun _=>directions Zero ((carrier Zero k).observations.observations h) k h) (fun _=>measurable_const)
    (fun _=>E) measurable_const (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) j0
    (F (rootParameter k h)) ((hF.smooth _).continuous.measurable)
  convert! hh using 1
  funext z
  simp only [MixedPastNativeOmitted.average,MixedPastLiteralPoint.meanField,σ,target,lo,hi,Function.comp_apply,Function.comp_def,Pi.mul_apply,id_eq]

end SHE.MixedPastNativeMarkThetaFields
