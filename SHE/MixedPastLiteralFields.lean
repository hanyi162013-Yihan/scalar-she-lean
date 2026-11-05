module

public import SHE.MixedPastLiteralPoint
public import SHE.JointInterpolationFields
public import SHE.WeightedRowTimeShift
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

namespace SHE.MixedPastLiteralFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastLiteralFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastLiteralFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v


/-- Genuine joint Borel dependence of the entire actual theta-current
mean over interpolation, physical sample and arbitrary recursive history. -/
theorem meanField_joint_measurable (k : ℕ) (q : ℝ≥0) :
    Measurable (fun z : (ℝ×Ω)×History X k=>MixedPastLiteralPoint.meanField
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k z.1.1 q z.1.2 z.2) := by
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

theorem meanField_measurable (k : ℕ) (θ : ℝ) (q : ℝ≥0) :
    Measurable (fun z : Ω×History X k=>MixedPastLiteralPoint.meanField
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q z.1 z.2) := by
  have hh:=meanField_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q
  convert! hh.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd) using 1

/-- Full literal random-reference point field, including a later row
time depending on the same history. This is Borel before any Fubini. -/
theorem point_joint_measurable (k : ℕ) (q : ℝ≥0) (r : History X k→ℝ) (hr : Measurable r) :
    Measurable (fun z : ((ℝ×Ω)×History X k)×HeatCircle=>MixedPastLiteralPoint.point
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k
      z.1.1.1 q (r z.1.2) z.1.2 z.2 z.1.1.2) := by
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hp : Measurable (fun z : ((ℝ×Ω)×History X k)×HeatCircle=>(z.1.1.1,(U z.1.1.2,Dir z.1.1.2))):=
    measurable_fst.fst.fst.prodMk ((hU.comp measurable_fst.fst.snd).prodMk (hd.comp measurable_fst.fst.snd))
  have hm:= (meanField_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q).comp
      (measurable_fst : Measurable (Prod.fst : (((ℝ×Ω)×History X k)×HeatCircle)→(ℝ×Ω)×History X k))
  have hh:=ControlledThetaWeightedFields.weightedPoint_measurable P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm k _ hp _ measurable_fst.snd (fun _=>q) (fun z=>r z.1.2)
    measurable_const (hr.comp measurable_fst.snd) _ hm _ measurable_snd
  convert! hh using 1

theorem point_measurable (k : ℕ) (θ : ℝ) (q : ℝ≥0) (r : History X k→ℝ) (hr : Measurable r) :
    Measurable (fun z : Ω×(History X k×HeatCircle)=>MixedPastLiteralPoint.point
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k
      θ q (r z.2.1) z.2.1 z.2.2 z.1) := by
  have hh:=point_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q r hr
  convert! hh.comp (((measurable_const.prodMk measurable_fst).prodMk measurable_snd.fst).prodMk measurable_snd.snd) using 1

end SHE.MixedPastLiteralFields
