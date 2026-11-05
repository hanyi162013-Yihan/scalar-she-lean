module

public import SHE.MixedPastProfileDerivative
public import SHE.MixedPastBaselineSpatialEnergy
public import SHE.BaselineStrictSupport
public import SHE.MixedPastBaselineLeafEnergy
public import SHE.MixedPastOmittedLeafAbsolute
public import SHE.FiniteSpatialBaseline
public import SHE.MixedPastBaselineFTCIdentity
public import SHE.MixedPastOmittedLeafSpatial
public import SHE.MixedPastBaselineEnergySections
public import SHE.BaselineUnitGain
public import SHE.ForestLeafMarkEnergy
public import SHE.MixedPastOmittedLeafMoments
public import SHE.ScalarRootSharpSections
public import SHE.HistoryRelativeSections
public import SHE.MixedPastDerivativeRMS
public import SHE.MixedPastOmittedMarkFields
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
set_option maxHeartbeats 650000

namespace SHE.MixedPastBaselineSpatialFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastBaselineSpatialFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastBaselineSpatialFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastBaselineSpatialFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastBaselineSpatialFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastBaselineSpatialFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastBaselineSpatialFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastBaselineSpatialFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastBaselineSpatialFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastBaselineSpatialFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v


open HistoryProductMeasure ScalarRootRelativeGeometry ProfileL2

open MixedPastBaselineSpatialEnergy

/-- Entire literal baseline field is Borel in interpolation, original
old times, actual sample/output and every relative old spatial site. -/
theorem point_joint_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (k : ℕ) (q : ℝ≥0) (hvq : v≤q) :
    Measurable (fun z : (((ℝ×(Fin k→ℝ))×(Ω×HeatCircle))×(Fin k→HeatCircle))=>
      relativeBaseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm k z.1.1.1 q z.1.1.2 (z.1.2,z.2)) := by
  let ph:=fun z : (((ℝ×(Fin k→ℝ))×(Ω×HeatCircle))×(Fin k→HeatCircle))=>
    separated k (z.1.2.2,z.1.1.2,fun i=>z.2 i+z.1.2.2)
  have hsites : Measurable (fun z : (((ℝ×(Fin k→ℝ))×(Ω×HeatCircle))×(Fin k→HeatCircle))=>
      fun i=>z.2 i+z.1.2.2):=Measurable.of_eval (fun i=>
        ((measurable_pi_apply i).comp measurable_snd).add measurable_fst.snd.snd)
  have hph : Measurable ph:=(separated_measurable k).comp
    (measurable_fst.snd.snd.prodMk (measurable_fst.fst.snd.prodMk hsites))
  have hj (j : Fin k) : Measurable (fun z : (((ℝ×(Fin k→ℝ))×(Ω×HeatCircle))×(Fin k→HeatCircle))=>
      MixedPastOmittedMarkFields.leafMark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm k z.1.1.1 q (ph z) j z.1.2.1) := by
    have hh:=MixedPastOmittedMarkFields.leaf_mark_joint_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k q j
    convert! hh.comp ((measurable_fst.fst.fst.prodMk measurable_fst.snd.fst).prodMk hph) using 1
  have hm:=(Finset.measurable_sum Finset.univ (fun j _=>hj j)).neg
  convert! hm using 1
  funext z
  exact MixedPastBaselineFTCIdentity.active_baseline_eq_neg_sum
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k (ph z) z.1.1.1 q hvq z.1.2.1

def averaged (k : ℕ) (θ : ℝ) (q : ℝ≥0) (t : Fin k→ℝ) (z : Ω×HeatCircle) : ℝ:=
  ∫ w,relativeBaseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q t (z,w)
    ∂Measure.pi (fun _ : Fin k=>haarAddCircle)

theorem averaged_joint_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (k : ℕ) (q : ℝ≥0) (hvq : v≤q) :
    Measurable (fun z : (ℝ×(Fin k→ℝ))×(Ω×HeatCircle)=>averaged
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k z.1.1 q z.1.2 z.2) :=
  (point_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall hages hrootStop k q hvq).stronglyMeasurable.integral_prod_right'.measurable

/-- Nonstrict old-time sections vanish exactly, uniformly over the
actual reference parameter and every sample/current mean. -/
theorem point_zero_of_not_strict (k : ℕ) (θ : ℝ) (q : ℝ≥0) (t : Fin k→ℝ)
    (hn : ¬StrictHistory Zero k (separated k ((0:HeatCircle),t,fun _=>(0:HeatCircle))))
    (z : (Ω×HeatCircle)×(Fin k→HeatCircle)) :
    relativeBaseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q t z=0 := by
  have hT : ∀ x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  let h:=separated k (z.1.2,t,fun i=>z.2 i+z.1.2)
  have hn' : ¬StrictHistory (Base (θ,(U z.1.1,Dir z.1.1))) k h:=by
    intro hh
    have hh0:=(ControlledThetaPhysicalGeometry.strict_iff P P.coefficient haP Λ v b hvb
      Z htarget hstop F hF hFm (θ,(U z.1.1,Dir z.1.1)) (0,(0,0)) k h).mp hh
    exact hn ((FixedHistoryTimeFactors.strict_sections Zero (b:ℝ) hT k t z.1.2 0 _ _).mp hh0)
  unfold relativeBaseline ControlledFamilyLegFubini.baseline
  split_ifs
  · exact baselinePoint_zero_of_not_strict _ _ k h hn' _ _ _
  · rfl

/-- Sections outside the original current window are literal zero. -/
theorem point_zero_of_inactive (k : ℕ) (θ : ℝ) (q : ℝ≥0) (t : Fin k→ℝ)
    (hn : ¬(q:ℝ)<(carrier Zero k).terminal (separated k ((0:HeatCircle),t,fun _=>(0:HeatCircle))))
    (z : (Ω×HeatCircle)×(Fin k→HeatCircle)) :
    relativeBaseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q t z=0 := by
  have hT : ∀ x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have ht:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (0,(U z.1.1,Dir z.1.1)) (0,(0,0)) k
    (separated k (z.1.2,t,fun i=>z.2 i+z.1.2))
  have hq : ¬(q:ℝ)<(carrier (Base (0,(U z.1.1,Dir z.1.1))) k).terminal
      (separated k (z.1.2,t,fun i=>z.2 i+z.1.2)):=by
    rw [ht,ActualMeanKernel.terminal_separated Zero (b:ℝ) hT]
    simpa only [ActualMeanKernel.terminal_separated Zero (b:ℝ) hT] using hn
  simp only [relativeBaseline,ControlledFamilyLegFubini.baseline,hq,and_false,ite_false]

end SHE.MixedPastBaselineSpatialFields
