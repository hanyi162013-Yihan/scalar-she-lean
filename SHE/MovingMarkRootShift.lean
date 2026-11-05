module

public import SHE.MovingMarkRootFields
public import SHE.MovingMarkPhysical
public import SHE.ControlledMeanSpatialShift
public import SHE.ShiftedOldTimeMeasure

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMarkRootShift
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMarkRootShift_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMarkRootShift_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMarkRootShift_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMarkRootShift_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMarkRootShift_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMarkRootShift_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

local instance movingMarkRootShift_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMarkRootShift_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMarkRootShift_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMarkRootShift_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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

/-- Literal root-retained physical old-time and old-space average;
no integration over the output point is performed. -/
theorem covariance_eq_absolute (k : ℕ) (θ : ℝ) (v s : ℝ≥0) (ω : Ω) (x : HeatCircle) :
    MovingMarkRootFields.covarianceValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k (θ,(v,(s,(ω,x))))=
    ∫ t : Fin k→ℝ,∫ w : Fin k→HeatCircle,
      ControlledFamilyLegFubini.covariance P A hA Λ v (v+h) (show v≤v+h from le_self_add)
        (ObservationFamilyTimeShift.family (v:ℝ) Z)
        (ControlledWordTimeShift.translatedTargets h Z htarget v)
        (ControlledWordTimeShift.translatedStops h Z hstop v) F hF hFm
        (embed (S.first v ω),embed (S.second v ω-S.first v ω))
        k (HistoryProductMeasure.separated k (x,t,fun i=>w i+x)) (v+s)
        (embed (S.first (v+s) ω)) (embed (S.second (v+s) ω-S.first (v+s) ω)) θ
      ∂Measure.pi (fun _=>AddCircle.haarAddCircle)
      ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ))) := by
  simp only [NNReal.coe_add]
  rw [←ShiftedOldTimeMeasure.integral_translation (v:ℝ) (h:ℝ) k]
  unfold MovingMarkRootFields.covarianceValue MovingMarkRootFields.covarianceRaw MovingNativeMarks.covariance
  apply integral_congr_ae
  filter_upwards [] with t
  apply integral_congr_ae
  filter_upwards [] with w
  have he:=ControlledMarkTimeShift.covariance_translation P A hA Λ h Z htarget hstop F hF hFm
    v (embed (S.first v ω),embed (S.second v ω-S.first v ω))
    k (HistoryProductMeasure.separated k (x,t,fun i=>w i+x)) s
    (embed (S.first (v+s) ω)) (embed (S.second (v+s) ω-S.first (v+s) ω)) θ
  have hq : (s:ℝ)+(v:ℝ)=((v+s:ℝ≥0):ℝ):=by simp only [NNReal.coe_add,add_comm]
  simpa only [hq,ControlledMeanSpatialShift.shift_separated,NNReal.coe_add] using he.symm

/-- Literal root-retained physical old-time and old-space average;
no integration over the output point is performed. -/
theorem baseline_eq_absolute (k : ℕ) (θ : ℝ) (v s : ℝ≥0) (ω : Ω) (x : HeatCircle) :
    MovingMarkRootFields.baselineValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k (θ,(v,(s,(ω,x))))=
    ∫ t : Fin k→ℝ,∫ w : Fin k→HeatCircle,
      ControlledFamilyLegFubini.baseline P A hA Λ v (v+h) (show v≤v+h from le_self_add)
        (ObservationFamilyTimeShift.family (v:ℝ) Z)
        (ControlledWordTimeShift.translatedTargets h Z htarget v)
        (ControlledWordTimeShift.translatedStops h Z hstop v) F hF hFm
        (embed (S.first v ω),embed (S.second v ω-S.first v ω))
        k (HistoryProductMeasure.separated k (x,t,fun i=>w i+x)) (v+s)
        (embed (S.first (v+s) ω)) (embed (S.second (v+s) ω-S.first (v+s) ω)) θ
      ∂Measure.pi (fun _=>AddCircle.haarAddCircle)
      ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ))) := by
  simp only [NNReal.coe_add]
  rw [←ShiftedOldTimeMeasure.integral_translation (v:ℝ) (h:ℝ) k]
  unfold MovingMarkRootFields.baselineValue MovingMarkRootFields.baselineRaw MovingNativeMarks.baseline
  apply integral_congr_ae
  filter_upwards [] with t
  apply integral_congr_ae
  filter_upwards [] with w
  have he:=ControlledMarkTimeShift.baseline_translation P A hA Λ h Z htarget hstop F hF hFm
    v (embed (S.first v ω),embed (S.second v ω-S.first v ω))
    k (HistoryProductMeasure.separated k (x,t,fun i=>w i+x)) s
    (embed (S.first (v+s) ω)) (embed (S.second (v+s) ω-S.first (v+s) ω)) θ
  have hq : (s:ℝ)+(v:ℝ)=((v+s:ℝ≥0):ℝ):=by simp only [NNReal.coe_add,add_comm]
  simpa only [hq,ControlledMeanSpatialShift.shift_separated,NNReal.coe_add] using he.symm

end SHE.MovingMarkRootShift
