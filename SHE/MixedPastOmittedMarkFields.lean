module

public import SHE.MixedPastProfileDerivative
public import SHE.MixedPastLiteralOmitted
public import SHE.ControlledThetaOmittedFields
public import SHE.ControlledFamilyProfileMarkFields
public import SHE.MixedPastLiteralFields
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

namespace SHE.MixedPastOmittedMarkFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastOmittedMarkFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastOmittedMarkFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastOmittedMarkFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastOmittedMarkFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastOmittedMarkFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastOmittedMarkFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastOmittedMarkFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastOmittedMarkFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastOmittedMarkFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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


/-- The actual omitted word on the original active conditional window.
It uses the original Gaussian law time and full moving profile baselines. -/
def activeAverage (k : ℕ) (θ : ℝ) (q : ℝ≥0) (h : History X k) (j0 : Fin k) (ω : Ω) : ℝ :=
  if (q:ℝ)<(carrier Zero k).terminal h then
    MixedPastLiteralOmitted.average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q h j0 ω else 0

/-- The original erased baseline derivative, including its actual
relative age and spatial center. -/
def leafInput (k : ℕ) (θ : ℝ) (h : History X k) (j0 : Fin k) (ω : Ω) : ℝ :=
  ControlledProfile.derivative P Λ (U ω) (Dir ω)
    ((lower Zero k h j0-(v:ℝ),space k h j0),θ)

/-- One literal baseline leaf contribution; its sign is supplied by the
finite baseline sum in the three-leg formula. -/
def leafMark (k : ℕ) (θ : ℝ) (q : ℝ≥0) (h : History X k) (j0 : Fin k) (ω : Ω) : ℝ :=
  leafInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ h j0 ω *
  activeAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q h j0 ω

/-- Joint Borel dependence is proved for the literal varying-reference
omitted word, before any history/sample/interpolation Fubini. -/
theorem active_average_joint_measurable (k : ℕ) (q : ℝ≥0) (j0 : Fin k) :
    Measurable (fun z : (ℝ×Ω)×History X k=>activeAverage
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k z.1.1 q z.2 j0 z.1.2) := by
  classical
  let pars : (ℝ×Ω)×History X k→ℝ×Inputs:=fun z=>(z.1.1,(U z.1.2,Dir z.1.2))
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hp : Measurable pars:=measurable_fst.fst.prodMk
    ((hU.comp measurable_fst.snd).prodMk (hd.comp measurable_fst.snd))
  have hc:=ControlledFamilyProfileMarkFields.old_profile_variable_measurable P Λ v
    (fun z : (ℝ×Ω)×History X k=>(U z.1.2,Dir z.1.2)) hp.snd
  have hm:=MixedPastLiteralFields.meanField_joint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q
  have ha:=ControlledThetaOmittedFields.capped_omitted_average_variable_measurable
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k pars hp
    Prod.snd measurable_snd (fun _=>(q:ℝ)) measurable_const _ hc _ hm j0
  have hset : MeasurableSet {z : (ℝ×Ω)×History X k | (q:ℝ)<(carrier Zero k).terminal z.2}:=
    measurableSet_lt measurable_const ((carrier Zero k).terminal_measurable.comp measurable_snd)
  let avg:=fun z : (ℝ×Ω)×History X k=>omittedAverage (Base (pars z))
    (oldProfile P Λ v (U z.1.2,Dir z.1.2)) k z.2
    (min (q:ℝ) ((carrier (Base (pars z)) k).terminal z.2)) j0
    (MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k z.1.1 q z.1.2 z.2)
  have hh : Measurable (fun z : (ℝ×Ω)×History X k=>
      if (q:ℝ)<(carrier Zero k).terminal z.2 then avg z else (0:ℝ)) :=
    ha.ite hset measurable_const
  convert! hh using 1
  funext z
  dsimp only [avg]
  unfold activeAverage
  split_ifs with h
  · unfold MixedPastLiteralOmitted.average
    have ht:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
      Z htarget hstop F hF hFm (pars z) (0,(0,0)) k z.2
    dsimp only [pars] at ht
    rw [ht,min_eq_left h.le]
  · rfl

theorem leaf_input_joint_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (j0 : Fin k) :
    Measurable (fun z : (ℝ×Ω)×History X k=>leafInput
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k z.1.1 z.2 j0 z.1.2) := by
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hlo : Measurable (fun z : (ℝ×Ω)×History X k=>lower Zero k z.2 j0):=(lower_measurable Zero k j0).comp measurable_snd
  have hsp : Measurable (fun z : (ℝ×Ω)×History X k=>space k z.2 j0):=(space_measurable k j0).comp measurable_snd
  have hm:=ControlledProfile.derivative_joint_measurable P hΛ hsmall
  convert! hm.comp ((((hU.comp measurable_fst.snd).prodMk (hd.comp measurable_fst.snd)).prodMk
    ((hlo.sub_const (v:ℝ)).prodMk hsp)).prodMk measurable_fst.fst) using 1

theorem leaf_mark_joint_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (q : ℝ≥0) (j0 : Fin k) :
    Measurable (fun z : (ℝ×Ω)×History X k=>leafMark
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k z.1.1 q z.2 j0 z.1.2) :=
  (leaf_input_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k j0).mul
  (active_average_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q j0)

/-- The derivative multiplier is measurable at the ORIGINAL past, so it
is a legitimate weight for the actual conditional word inequality. -/
theorem leaf_input_past_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (θ : ℝ) (h : History X k) (j0 : Fin k) :
    Measurable[𝓕 v] (leafInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ h j0) := by
  have hm:=MixedPastProfileDerivative.derivative_past_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hΛ hsmall v
  letI : MeasurableSpace Ω:=𝓕 v
  convert! hm.comp ((measurable_id.prodMk (measurable_const : Measurable
    (fun _ : Ω=>(lower Zero k h j0-(v:ℝ),space k h j0)))).prodMk
      (measurable_const : Measurable (fun _ : Ω=>θ))) using 1

end SHE.MixedPastOmittedMarkFields
