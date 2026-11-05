module

public import SHE.MixedPastTerminalEndpointIdentity
public import SHE.MixedPastTerminalEndpointWord
public import SHE.UncutHistoryMass
public import SHE.ControlledThetaSupported
public import SHE.MixedPastTerminalPairedWord
public import SHE.MixedPastTerminalCovarianceFields
public import SHE.MixedPastTerminalCovarianceEnvelope
public import SHE.MixedPastTerminalFiniteCovarianceRelative
public import SHE.MixedPastTerminalCovarianceMassNative
public import SHE.MixedPastTerminalRootEnvelope
public import SHE.HistoryNewestMoment
public import SHE.ControlledTerminalPairedAmplitude
public import SHE.ControlledRelativeScoreForest
public import SHE.TerminalConditionalGeometry
public import SHE.ParentMeanDensity
public import SHE.MixedPastTerminalPairedIdentity
public import SHE.MixedPastTerminalPairedFields
public import SHE.ControlledTerminalPairedRelative
public import SHE.TerminalSuccessorGeometry
public import SHE.MixedPastTerminalState
public import SHE.MixedPastTerminalFirstState
public import SHE.JointHistoryFields
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastTerminalWordMass
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralPoint_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralPoint_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralPoint_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralPoint_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralPoint_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralPoint_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastLiteralPoint_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralPoint_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastLiteralPoint_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

local notation "DataU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "DataV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S


open MixedPastTerminalPairedFields


local notation "G"=>MixedPastTerminalCovarianceFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Raw"=>MixedPastTerminalFiniteCovariance.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mass"=>MixedPastTerminalCovarianceFields.mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Amp"=>MixedPastTerminalCovarianceFields.amplitude Λ P haP v b hvb Z htarget hstop F hF hFm

open GaussianConvolution Classical
local notation "Cur"=>MixedPastTerminalPairedFields.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "End"=>MixedPastTerminalEndpointIdentity.endpoint
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Diff"=>MixedPastTerminalEndpointIdentity.difference
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Pair"=>MixedPastTerminalPairedWord.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "WordDiff"=>MixedPastTerminalEndpointWord.wordDifference
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Coarse domination of the ACTUAL endpoint word is needed only for
absolute original-history Fubini, independently of the sharp paired
remainder energy. It follows from genuine normalized smooth words. -/
theorem word_bound (k:ℕ):∃K:ℝ,0≤K ∧
    ∀h:History X k,∀ω:Ω,|WordDiff k h ω|≤K*UncutSmoothWords.weight Zero k h:=by
  obtain ⟨K,hK0,hK⟩:=(ControlledThetaWordFields.normalized_uniform
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k).norm_bound
  have hb(second:Bool)(h:History X k)(ω:Ω):
      |UncutSmoothWords.test (Base ((if second then 1 else 0),(U ω,Dir ω))) k h (Cur second k h ω)|≤
        K*UncutSmoothWords.weight Zero k h:=by
    rw [UncutSmoothWords.test_eq_weight_normalized,Pi.smul_apply,smul_eq_mul,abs_mul,
      abs_of_nonneg (UncutSmoothWords.weight_nonneg _ _ _),
      ControlledReferenceThetaGeometry.weight_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
        ((if second then 1 else 0),(U ω,Dir ω)) (0,(0,0)) k h]
    have hh:=hK (((if second then 1 else 0),(U ω,Dir ω)),h) (Cur second k h ω)
    rw [Real.norm_eq_abs] at hh
    exact (mul_le_mul_of_nonneg_left hh (UncutSmoothWords.weight_nonneg Zero k h)).trans_eq (mul_comm _ _)
  refine ⟨2*K,mul_nonneg (by norm_num) hK0,?_⟩
  intro h ω
  unfold MixedPastTerminalEndpointWord.wordDifference
  split_ifs
  · have ht:=hb true h ω
    have hf:=hb false h ω
    rw [if_pos (rfl:(true:Bool)=true)] at ht
    rw [if_neg (show ¬(false:Bool)=true from by decide)] at hf
    exact (abs_sub _ _).trans (by linarith [ht,hf])
  · exact (abs_zero.le.trans (mul_nonneg (mul_nonneg (by norm_num) hK0)
      (UncutSmoothWords.weight_nonneg Zero k h)))

theorem word_measurable (k:ℕ):
    Measurable (fun z:Ω×History X k=>WordDiff k z.2 z.1):=by
  have hu:Measurable U:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd:Measurable Dir:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hm(second:Bool):Measurable (fun z:Ω×History X k=>
      UncutSmoothWords.test (Base ((if second then 1 else 0),(U z.1,Dir z.1))) k z.2
        (Cur second k z.2 z.1)):=by
    have hc:Measurable (fun z:Ω×History X k=>Cur second k z.2 z.1):=by
      convert! (MixedPastTerminalPairedFields.current_measurable
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm second k).comp
          measurable_swap using 1
    convert! (ControlledThetaWordFields.test_joint_measurable
      P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k).comp
      (((measurable_const.prodMk ((hu.comp measurable_fst).prodMk (hd.comp measurable_fst))).prodMk
        measurable_snd).prodMk hc) using 1
  exact (hm true|>.sub (hm false)).ite
    ((strictHistory_measurableSet Zero k).preimage measurable_snd) measurable_const

theorem word_integrable (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    Integrable (fun z:Ω×History X k=>WordDiff k z.2 z.1)
      (μ.prod (historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k)):=by
  obtain ⟨K,hK0,hK⟩:=word_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k
  have hi:=((UncutHistoryMass.weight_integrable Zero ρ k).const_mul K).comp_snd μ
  apply hi.mono' (word_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm k).aestronglyMeasurable
  exact ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs] using hK z.2 z.1)

end SHE.MixedPastTerminalWordMass

