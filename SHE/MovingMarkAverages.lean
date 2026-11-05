module

public import SHE.MovingNativeMarks

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMarkAverages
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMarkAverages_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMarkAverages_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMarkAverages_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMarkAverages_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMarkAverages_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMarkAverages_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

local instance movingMarkAverages_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMarkAverages_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMarkAverages_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMarkAverages_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]


open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Cov"=>ControlledFamilyLegFubini.covariance P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le)
  Z htarget hstop F hF hFm
local notation "Base"=>ControlledFamilyLegFubini.baseline P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le)
  Z htarget hstop F hF hFm


local notation "Rzero"=>ControlledReferenceLevel.referenceData P A hA Λ 0 0 h (show (0:ℝ≥0)≤h from bot_le) (0,0)

def covarianceAverage (k : ℕ) (past age : W→ℝ≥0) (θ : W→ℝ) (ω : W→Ω) (w : W) : ℝ :=
  ∫ hist,MovingNativeMarks.covariance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm k
    (fun z : W×History HeatCircle k=>past z.1) (fun z=>age z.1) Prod.snd (fun z=>θ z.1)
    (fun z=>ω z.1) (w,hist) ∂historyMeasure Rzero AddCircle.haarAddCircle k

def baselineAverage (k : ℕ) (past age : W→ℝ≥0) (θ : W→ℝ) (ω : W→Ω) (w : W) : ℝ :=
  ∫ hist,MovingNativeMarks.baseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm k
    (fun z : W×History HeatCircle k=>past z.1) (fun z=>age z.1) Prod.snd (fun z=>θ z.1)
    (fun z=>ω z.1) (w,hist) ∂historyMeasure Rzero AddCircle.haarAddCircle k

theorem covarianceAverage_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (past age : W→ℝ≥0) (hpast : Measurable past) (hage : Measurable age)
    (θ : W→ℝ) (hθ : Measurable θ) (ω : W→Ω) (hω : Measurable ω) :
    Measurable (covarianceAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k past age θ ω) :=
  (MovingNativeMarks.covariance_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm hΛ hsmall k
    (fun z : W×History HeatCircle k=>past z.1) (fun z=>age z.1) (hpast.comp measurable_fst) (hage.comp measurable_fst)
    Prod.snd measurable_snd (fun z=>θ z.1) (hθ.comp measurable_fst) (fun z=>ω z.1) (hω.comp measurable_fst)).stronglyMeasurable.integral_prod_right'.measurable

theorem baselineAverage_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (past age : W→ℝ≥0) (hpast : Measurable past) (hage : Measurable age)
    (θ : W→ℝ) (hθ : Measurable θ) (ω : W→Ω) (hω : Measurable ω) :
    Measurable (baselineAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k past age θ ω) :=
  (MovingNativeMarks.baseline_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm hΛ hsmall k
    (fun z : W×History HeatCircle k=>past z.1) (fun z=>age z.1) (hpast.comp measurable_fst) (hage.comp measurable_fst)
    Prod.snd measurable_snd (fun z=>θ z.1) (hθ.comp measurable_fst) (fun z=>ω z.1) (hω.comp measurable_fst)).stronglyMeasurable.integral_prod_right'.measurable

end SHE.MovingMarkAverages

