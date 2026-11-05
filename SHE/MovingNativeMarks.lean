module

public import SHE.MovingNativeFields
public import SHE.ControlledFamilyCovarianceFieldsBorel
public import SHE.ControlledFamilyBaselineFieldsBorel

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingNativeMarks
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingNativeMarks_realSigma : MeasurableSpace RealL2 := borel _
local instance movingNativeMarks_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingNativeMarks_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingNativeMarks_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingNativeMarks_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingNativeMarks_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

local instance movingNativeMarks_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingNativeMarks_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingNativeMarks_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingNativeMarks_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]


open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (h : ℝ≥0) {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Cov"=>ControlledFamilyLegFubini.covariance P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le)
  Z htarget hstop F hF hFm
local notation "Base"=>ControlledFamilyLegFubini.baseline P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le)
  Z htarget hstop F hF hFm

/-- Literal relative-clock covariance leg with the original moving
past and actual current states, before every history average. -/
def covariance (k : ℕ) (past age : W→ℝ≥0) (hist : W→History X k)
    (θ : W→ℝ) (ω : W→Ω) (w : W) : ℝ :=
  Cov (embed (S.first (past w) (ω w)),embed (S.second (past w) (ω w)-S.first (past w) (ω w)))
    k (hist w) (age w) (embed (S.first (past w+age w) (ω w)))
    (embed (S.second (past w+age w) (ω w)-S.first (past w+age w) (ω w))) (θ w)

def baseline (k : ℕ) (past age : W→ℝ≥0) (hist : W→History X k)
    (θ : W→ℝ) (ω : W→Ω) (w : W) : ℝ :=
  Base (embed (S.first (past w) (ω w)),embed (S.second (past w) (ω w)-S.first (past w) (ω w)))
    k (hist w) (age w) (embed (S.first (past w+age w) (ω w)))
    (embed (S.second (past w+age w) (ω w)-S.first (past w+age w) (ω w))) (θ w)

theorem covariance_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (past age : W→ℝ≥0) (hpast : Measurable past) (hage : Measurable age)
    (hist : W→History X k) (hhist : Measurable hist) (θ : W→ℝ) (hθ : Measurable θ)
    (ω : W→Ω) (hω : Measurable ω) :
    Measurable (covariance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k past age hist θ ω) := by
  have hp:=(MovingNativeFields.past_inputs_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).comp (hpast.prodMk hω)
  have hc:=MovingNativeFields.shifted_states_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S past age hpast hage ω hω
  exact ControlledFamilyCovarianceFieldsBorel.covariance_variable_measurable
    P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le) Z htarget hstop F hF hFm hΛ hsmall k _ hp hist hhist
    (fun w=>(age w:ℝ)) (measurable_subtype_coe.comp hage)
    _ _ (embed.continuous.measurable.comp hc.fst) (embed.continuous.measurable.comp (hc.snd.sub hc.fst)) θ hθ

theorem baseline_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (past age : W→ℝ≥0) (hpast : Measurable past) (hage : Measurable age)
    (hist : W→History X k) (hhist : Measurable hist) (θ : W→ℝ) (hθ : Measurable θ)
    (ω : W→Ω) (hω : Measurable ω) :
    Measurable (baseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k past age hist θ ω) := by
  have hp:=(MovingNativeFields.past_inputs_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).comp (hpast.prodMk hω)
  have hc:=MovingNativeFields.shifted_states_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S past age hpast hage ω hω
  exact ControlledFamilyBaselineFieldsBorel.baseline_variable_measurable
    P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le) Z htarget hstop F hF hFm hΛ hsmall k _ hp hist hhist
    (fun w=>(age w:ℝ)) (measurable_subtype_coe.comp hage)
    _ _ (embed.continuous.measurable.comp hc.fst) (embed.continuous.measurable.comp (hc.snd.sub hc.fst)) θ hθ

end SHE.MovingNativeMarks

