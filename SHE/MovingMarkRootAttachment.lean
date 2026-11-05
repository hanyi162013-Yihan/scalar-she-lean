module

public import SHE.MovingMarkRootTheta
public import SHE.MixedNativeRootThreeLeg
public import SHE.MovingMarkRootShift
public import SHE.MovingProfileBudget
public import SHE.MixedPastCovarianceAverageUniform
public import SHE.MixedNativeCovarianceFTCIdentity

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMarkRootAttachment
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMarkRootAttachment_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMarkRootAttachment_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMarkRootAttachment_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMarkRootAttachment_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMarkRootAttachment_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMarkRootAttachment_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingMarkRootAttachment_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMarkRootAttachment_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMarkRootAttachment_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMarkRootAttachment_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]



open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
  PhysicalScoreChain ControlledOldIntervals
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "AA"=>ControlledMeanOldAverageShift.absoluteAt P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v



local notation "CV"=>MovingMarkRootFields.covarianceValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "CT"=>MovingMarkRootTheta.covarianceTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

theorem covariance_eq_actual_average (k : ℕ) (v s : ℝ≥0) (ω : Ω) (x : HeatCircle) :
    MovingMarkRootTheta.covarianceTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P P.coefficient haP h Z htarget hstop F hF hFm k (v,(s,(ω,x)))=
    MixedNativeRootThreeLeg.covarianceAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k (v+s) (ω,x) := by
  unfold MovingMarkRootTheta.covarianceTheta MixedNativeRootThreeLeg.covarianceAverage
  apply integral_congr_ae
  filter_upwards [] with θ
  simpa only [HistoryProductMeasure.rootAverage,MixedNativeRootLegMass.covarianceField,
    MixedPastJointData.pastU,MixedPastJointData.pastD,NNReal.coe_add,ControlledReferenceLevel.referenceData] using
    MovingMarkRootShift.covariance_eq_absolute 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P P.coefficient haP h Z htarget hstop F hF hFm k θ v s ω x

theorem baseline_eq_actual_average (k : ℕ) (v s : ℝ≥0) (ω : Ω) (x : HeatCircle) :
    MovingMarkRootTheta.baselineTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P P.coefficient haP h Z htarget hstop F hF hFm k (v,(s,(ω,x)))=
    MixedNativeRootThreeLeg.baselineAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k (v+s) (ω,x) := by
  unfold MovingMarkRootTheta.baselineTheta MixedNativeRootThreeLeg.baselineAverage
  apply integral_congr_ae
  filter_upwards [] with θ
  simpa only [HistoryProductMeasure.rootAverage,MixedNativeRootLegMass.baselineField,
    MixedPastJointData.pastU,MixedPastJointData.pastD,NNReal.coe_add,ControlledReferenceLevel.referenceData] using
    MovingMarkRootShift.baseline_eq_absolute 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P P.coefficient haP h Z htarget hstop F hF hFm k θ v s ω x

end SHE.MovingMarkRootAttachment
