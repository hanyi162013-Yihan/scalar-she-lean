module

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

namespace SHE.MixedPastNativeKernel
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

/-- Literal complete endpoint difference of the original recursive
backward kernel; covariance, mean and every baseline move together. -/
def difference (k:ℕ) (q:ℝ≥0) (r:ℝ) (h:History HeatCircle k) (y:HeatCircle) (ω:Ω):ℝ:=
  MixedPastNativeConsistentPoint.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k 1 q r h y ω-
  MixedPastNativeConsistentPoint.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k 0 q r h y ω

local notation "Diff"=>difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

theorem difference_measurable (k:ℕ) (q:ℝ≥0) (r:ℝ):
    Measurable (fun z:(Ω×History HeatCircle k)×HeatCircle=>Diff k q r z.1.2 z.2 z.1.1):=by
  have hU:Measurable U:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hDir:Measurable Dir:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hp(θ:ℝ):Measurable (fun z:(Ω×History HeatCircle k)×HeatCircle=>(θ,(U z.1.1,Dir z.1.1))):=
    measurable_const.prodMk ((hU.comp measurable_fst.fst).prodMk (hDir.comp measurable_fst.fst))
  have hpoint(θ:ℝ):Measurable (fun z:(Ω×History HeatCircle k)×HeatCircle=>
      MixedPastNativeConsistentPoint.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q r z.1.2 z.2 z.1.1):=by
    have hm:Measurable (fun z:(Ω×History HeatCircle k)×HeatCircle=>
        MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
          P haP v b hvb Z htarget hstop F hF hFm k θ q z.1.1 z.1.2):=
      (MixedPastLiteralFields.meanField_measurable
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q).comp measurable_fst
    have hh:=ControlledThetaNativePointFields.rowPoint_measurable P haP Λ v b hvb Z htarget hstop F hF hFm k
      (fun z:(Ω×History HeatCircle k)×HeatCircle=>(θ,(U z.1.1,Dir z.1.1))) (hp θ)
      (fun z=>z.1.2) measurable_fst.snd (fun _=>(q:ℝ)) (fun _=>r) measurable_const measurable_const
      (fun z=>MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q z.1.1 z.1.2) hm Prod.snd measurable_snd
    convert! hh using 1
  exact (hpoint 1).sub (hpoint 0)

private theorem rowPoint_zero {R:ReferenceData} {X:Type} [MeasurableSpace X] {n:ℕ}
    (L:Level R X n) (k:ℕ) (q r:ℝ) (m:History X k→WordRecursion.State (n+k)) (h:History X k) (y:HeatCircle):
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

/-- A finite smooth cap is used solely for Borel/Fubini realization of
the COMPLETE field. It is uniform in all actual past and current states. -/
theorem difference_bound (k:ℕ) (q:ℝ≥0) (r:ℝ) (t:Fin k→ℝ):
    ∃B:ℝ,0≤B ∧ ∀ω y x w,|Diff k q r (separated k (x,t,w)) y ω|≤B:=by
  obtain ⟨B,hB,hbound⟩:=ControlledFamilyKernelBounds.weightedPoint_family_uniform_bound
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k (by norm_num : (0:ℝ)≤0) q r t
  refine ⟨2*B,by positivity,?_⟩
  intro ω y x w
  have hb(θ:ℝ):|MixedPastNativeConsistentPoint.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q r (separated k (x,t,w)) y ω|≤B:=by
    change ‖ActualMeanKernel.rowPoint _ _ _ _ _ _ _‖≤B
    rw [rowPoint_zero]
    exact hbound (θ,(U ω,Dir ω)) _ y x w
  exact (abs_sub _ _).trans (by linarith [hb 1,hb 0])

/-- Original old histories are translated relative to the retained
native output. The original law-q and the independent row-r are fixed. -/
def field (k:ℕ) (q:ℝ≥0) (r:ℝ) (t:Fin k→ℝ) (w:Fin k→HeatCircle)
    (z:Ω×(HeatCircle×HeatCircle)):ℂ:=
  (Diff k q r (separated k (z.2.2,t,fun i=>w i+z.2.2)) z.2.1 z.1:ℂ)

attribute [local irreducible] difference MixedPastJointData.pastU MixedPastJointData.pastD

local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

theorem field_measurable (k:ℕ) (q:ℝ≥0) (r:ℝ) (t:Fin k→ℝ) (w:Fin k→HeatCircle):
    Measurable (Field k q r t w):=by
  unfold field
  have hs:Measurable (fun z:Ω×(HeatCircle×HeatCircle)=>
      separated k (z.2.2,t,fun i=>w i+z.2.2)):=
    (separated_measurable k).comp
      (measurable_snd.snd.prodMk (measurable_const.prodMk
        (measurable_pi_iff.mpr (fun i=>measurable_const.add measurable_snd.snd))))
  exact Complex.continuous_ofReal.measurable.comp ((difference_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q r).comp
      ((measurable_fst.prodMk hs).prodMk measurable_snd.fst))

theorem field_bound (k:ℕ) (q:ℝ≥0) (r:ℝ) (t:Fin k→ℝ):
    ∃B:ℝ,0≤B ∧ ∀w ω y x,‖Field k q r t w (ω,(y,x))‖≤B:=by
  obtain ⟨B,hB,hbound⟩:=difference_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q r t
  exact ⟨B,hB,fun w ω y x=>by simpa only [field,Complex.norm_real,Real.norm_eq_abs] using hbound ω y x (fun i=>w i+x)⟩

end SHE.MixedPastNativeKernel
