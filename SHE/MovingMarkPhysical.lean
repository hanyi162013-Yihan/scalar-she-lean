module

public import SHE.MovingMarkAverages
public import SHE.ControlledMarkTimeShift
public import SHE.ShiftedHistoryMeasure
public import SHE.MixedPastCovarianceCurrentFields
public import SHE.MixedPastBaselineCurrentFields

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMarkPhysical
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMarkPhysical_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMarkPhysical_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMarkPhysical_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMarkPhysical_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMarkPhysical_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMarkPhysical_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

local instance movingMarkPhysical_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMarkPhysical_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMarkPhysical_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMarkPhysical_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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


local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v
local notation "Rabs" v=>ControlledReferenceLevel.referenceData P A hA Λ 0 v (v+h) (show v≤v+h from le_self_add) (0,0)

def covarianceValue (k : ℕ) (z : ℝ×(ℝ≥0×(ℝ≥0×Ω))) : ℝ :=
  MovingMarkAverages.covarianceAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm k
    (fun w : ℝ×(ℝ≥0×(ℝ≥0×Ω))=>w.2.1) (fun w=>w.2.2.1) Prod.fst (fun w=>w.2.2.2) z

def baselineValue (k : ℕ) (z : ℝ×(ℝ≥0×(ℝ≥0×Ω))) : ℝ :=
  MovingMarkAverages.baselineAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm k
    (fun w : ℝ×(ℝ≥0×(ℝ≥0×Ω))=>w.2.1) (fun w=>w.2.2.1) Prod.fst (fun w=>w.2.2.2) z
local notation "CV"=>covarianceValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P A hA h Z htarget hstop F hF hFm
local notation "BV"=>baselineValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P A hA h Z htarget hstop F hF hFm

theorem covarianceValue_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (CV k) := by
  unfold covarianceValue
  exact MovingMarkAverages.covarianceAverage_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm hΛ hsmall k
    (fun w : ℝ×(ℝ≥0×(ℝ≥0×Ω))=>w.2.1) (fun w=>w.2.2.1)
    measurable_snd.fst measurable_snd.snd.fst Prod.fst measurable_fst (fun w=>w.2.2.2) measurable_snd.snd.snd

theorem baselineValue_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (BV k) := by
  unfold baselineValue
  exact MovingMarkAverages.baselineAverage_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm hΛ hsmall k
    (fun w : ℝ×(ℝ≥0×(ℝ≥0×Ω))=>w.2.1) (fun w=>w.2.2.1)
    measurable_snd.fst measurable_snd.snd.fst Prod.fst measurable_fst (fun w=>w.2.2.2) measurable_snd.snd.snd

/-- Literal original-history covariance average on the moving physical
window, identified before any norm or current/past averaging. -/
theorem covariance_eq_absolute (k : ℕ) (θ : ℝ) (v s : ℝ≥0) (ω : Ω) :
    CV k (θ,(v,(s,ω)))=
    ∫ hist,ControlledFamilyLegFubini.covariance P A hA Λ v (v+h) (show v≤v+h from le_self_add)
      (ZT v) (HT v) (HS v) F hF hFm
      (embed (S.first v ω),embed (S.second v ω-S.first v ω)) k hist (v+s)
      (embed (S.first (v+s) ω)) (embed (S.second (v+s) ω-S.first (v+s) ω)) θ
      ∂historyMeasure (Rabs v) AddCircle.haarAddCircle k := by
  have hb : (Rabs v).base=(Rzero).base+(v:ℝ):=by change (v:ℝ)=(0:ℝ)+(v:ℝ);ring
  have hh : (Rabs v).horizon=(Rzero).horizon+(v:ℝ):=by
    change ((v+h:ℝ≥0):ℝ)=(h:ℝ)+(v:ℝ)
    simp only [NNReal.coe_add,add_comm]
  rw [←ShiftedHistoryMeasure.integral_translation Rzero (Rabs v) (v:ℝ) hb hh AddCircle.haarAddCircle k]
  unfold covarianceValue MovingMarkAverages.covarianceAverage MovingNativeMarks.covariance
  apply integral_congr_ae
  filter_upwards [] with hist
  have he:=ControlledMarkTimeShift.covariance_translation P A hA Λ h Z htarget hstop F hF hFm
    v (embed (S.first v ω),embed (S.second v ω-S.first v ω)) k hist s
    (embed (S.first (v+s) ω)) (embed (S.second (v+s) ω-S.first (v+s) ω)) θ
  have hq : (s:ℝ)+(v:ℝ)=((v+s:ℝ≥0):ℝ):=by simp only [NNReal.coe_add,add_comm]
  simpa only [hq,NNReal.coe_add] using he.symm

theorem baseline_eq_absolute (k : ℕ) (θ : ℝ) (v s : ℝ≥0) (ω : Ω) :
    BV k (θ,(v,(s,ω)))=
    ∫ hist,ControlledFamilyLegFubini.baseline P A hA Λ v (v+h) (show v≤v+h from le_self_add)
      (ZT v) (HT v) (HS v) F hF hFm
      (embed (S.first v ω),embed (S.second v ω-S.first v ω)) k hist (v+s)
      (embed (S.first (v+s) ω)) (embed (S.second (v+s) ω-S.first (v+s) ω)) θ
      ∂historyMeasure (Rabs v) AddCircle.haarAddCircle k := by
  have hb : (Rabs v).base=(Rzero).base+(v:ℝ):=by change (v:ℝ)=(0:ℝ)+(v:ℝ);ring
  have hh : (Rabs v).horizon=(Rzero).horizon+(v:ℝ):=by
    change ((v+h:ℝ≥0):ℝ)=(h:ℝ)+(v:ℝ)
    simp only [NNReal.coe_add,add_comm]
  rw [←ShiftedHistoryMeasure.integral_translation Rzero (Rabs v) (v:ℝ) hb hh AddCircle.haarAddCircle k]
  unfold baselineValue MovingMarkAverages.baselineAverage MovingNativeMarks.baseline
  apply integral_congr_ae
  filter_upwards [] with hist
  have he:=ControlledMarkTimeShift.baseline_translation P A hA Λ h Z htarget hstop F hF hFm
    v (embed (S.first v ω),embed (S.second v ω-S.first v ω)) k hist s
    (embed (S.first (v+s) ω)) (embed (S.second (v+s) ω-S.first (v+s) ω)) θ
  have hq : (s:ℝ)+(v:ℝ)=((v+s:ℝ≥0):ℝ):=by simp only [NNReal.coe_add,add_comm]
  simpa only [hq,NNReal.coe_add] using he.symm

end SHE.MovingMarkPhysical

