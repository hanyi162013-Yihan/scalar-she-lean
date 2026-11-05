module

public import SHE.MovingMeanPhysicalField

public import SHE.ControlledMeanLegShift
public import SHE.MovingNativeFields
public import SHE.MixedNativeRootThreeLeg
public import SHE.MixedPastMeanThetaFourier
public import SHE.MovingMeanThetaEnergy
public import SHE.MovingMeanSectionEnergy
public import SHE.MeanThetaAverage
public import SHE.MovingMeanCost

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMeanRootScalar
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMeanRootScalar_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMeanRootScalar_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMeanRootScalar_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMeanRootScalar_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMeanRootScalar_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMeanRootScalar_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingMeanRootScalar_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMeanRootScalar_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMeanRootScalar_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMeanRootScalar_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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

abbrev RootData:=ℝ×(ℝ≥0×(ℝ≥0×(Ω×HeatCircle)))
local notation "Leg"=>ControlledFamilyLegFubini.mean P P.coefficient haP Λ 0 h (show (0:ℝ≥0)≤h from bot_le)
  Z htarget hstop F hF hFm

def meanRaw (k : ℕ) (z : RootData (Ω:=Ω)×((Fin k→ℝ)×(Fin k→HeatCircle))) : ℝ:=
  Leg (embed (S.first z.1.2.1 z.1.2.2.2.1),embed (S.second z.1.2.1 z.1.2.2.2.1-S.first z.1.2.1 z.1.2.2.2.1))
    k (HistoryProductMeasure.separated k (z.1.2.2.2.2,z.2.1,fun i=>z.2.2 i+z.1.2.2.2.2)) z.1.2.2.1
    (embed (S.first (z.1.2.1+z.1.2.2.1) z.1.2.2.2.1))
    (embed (S.second (z.1.2.1+z.1.2.2.1) z.1.2.2.2.1-S.first (z.1.2.1+z.1.2.2.1) z.1.2.2.2.1)) z.1.1
local notation "Raw"=>meanRaw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

def meanValue (k : ℕ) (z : RootData (Ω:=Ω)) : ℝ:=
  ∫ t : Fin k→ℝ,∫ w : Fin k→HeatCircle,Raw k (z,(t,w)) ∂Measure.pi (fun _=>AddCircle.haarAddCircle)
    ∂Measure.pi (fun _=>volume.restrict (Ioc (0:ℝ) (h:ℝ)))
local notation "Value"=>meanValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem meanRaw_measurable (k : ℕ) : Measurable (Raw k) := by
  have hh : Measurable (fun z : RootData (Ω:=Ω)×((Fin k→ℝ)×(Fin k→HeatCircle))=>
      HistoryProductMeasure.separated k (z.1.2.2.2.2,z.2.1,fun i=>z.2.2 i+z.1.2.2.2.2)) :=
    (HistoryProductMeasure.separated_measurable k).comp
      (measurable_fst.snd.snd.snd.snd.prodMk (measurable_snd.fst.prodMk
        (Measurable.of_eval (fun i=>((measurable_pi_apply i).comp measurable_snd.snd).add
          measurable_fst.snd.snd.snd.snd))))
  exact MovingNativeFields.relative_mean_leg_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P P.coefficient haP h Z htarget hstop F hF hFm k
    (fun z : RootData (Ω:=Ω)×((Fin k→ℝ)×(Fin k→HeatCircle))=>z.1.2.1)
    (fun z=>z.1.2.2.1) measurable_fst.snd.fst measurable_fst.snd.snd.fst
    (fun z=>z.1.2.2.2.1) measurable_fst.snd.snd.snd.fst _ hh (fun z=>z.1.1) measurable_fst.fst

theorem meanValue_measurable (k : ℕ) : Measurable (Value k) := by
  have hm:=(meanRaw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm k).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

def meanTheta (k : ℕ) (z : ℝ≥0×(ℝ≥0×(Ω×HeatCircle))) : ℝ:=
  ∫ θ,Value k (θ,z) ∂MeanThetaAverage.thetaMeasure
local notation "Theta"=>meanTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem meanTheta_measurable (k : ℕ) : Measurable (Theta k):=
  (meanValue_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm k).stronglyMeasurable.integral_prod_left'.measurable

def meanField (k : ℕ) (z : ℝ×(ℝ×(Ω×HeatCircle))) : ℝ:=
  if MovingMeanPhysicalField.valid H h z.1 z.2.1 then Theta k (z.1.toNNReal,(z.2.1.toNNReal,z.2.2)) else 0

theorem meanField_measurable (k : ℕ) : Measurable (meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm k) := by
  have hm:=(meanTheta_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm k).comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk
      ((measurable_real_toNNReal.comp measurable_snd.fst).prodMk measurable_snd.snd))
  have hv : MeasurableSet {z : ℝ×(ℝ×(Ω×HeatCircle))|MovingMeanPhysicalField.valid H h z.1 z.2.1} :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd.fst).inter
        ((measurableSet_lt measurable_snd.fst measurable_const).inter
          (measurableSet_le (measurable_fst.add_const (h:ℝ)) measurable_const)))
  exact hm.ite hv measurable_const

theorem meanValue_eq_absolute (k : ℕ) (θ : ℝ) (v s : ℝ≥0) (ω : Ω) (x : HeatCircle) :
    Value k (θ,(v,(s,(ω,x))))=
      ∫ t : Fin k→ℝ,∫ w : Fin k→HeatCircle,
        ControlledFamilyLegFubini.mean P P.coefficient haP Λ v (v+h) (show v≤v+h from le_self_add)
          (ZT v) (HT v) (HS v) F hF hFm
          (embed (S.first v ω),embed (S.second v ω-S.first v ω))
          k (HistoryProductMeasure.separated k (x,t,fun i=>w i+x)) (v+s)
          (embed (S.first (v+s) ω)) (embed (S.second (v+s) ω-S.first (v+s) ω)) θ
        ∂Measure.pi (fun _=>AddCircle.haarAddCircle)
        ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ))) := by
  simp only [NNReal.coe_add]
  rw [←ShiftedOldTimeMeasure.integral_translation (v:ℝ) (h:ℝ) k]
  unfold meanValue meanRaw
  apply integral_congr_ae
  filter_upwards with t
  apply integral_congr_ae
  filter_upwards with w
  have he:=ControlledMeanLegShift.mean_translation P P.coefficient haP Λ h Z htarget hstop F hF hFm
    v (embed (S.first v ω),embed (S.second v ω-S.first v ω))
    k (HistoryProductMeasure.separated k (x,t,fun i=>w i+x)) s
    (embed (S.first (v+s) ω)) (embed (S.second (v+s) ω-S.first (v+s) ω)) θ
  have hq : (s:ℝ)+(v:ℝ)=((v+s:ℝ≥0):ℝ):=by simp only [NNReal.coe_add,add_comm]
  simpa only [hq,ControlledMeanSpatialShift.shift_separated,NNReal.coe_add] using he.symm

theorem meanTheta_eq_absolute (k : ℕ) (v s : ℝ≥0) (ω : Ω) (x : HeatCircle) :
    Theta k (v,(s,(ω,x)))=MixedNativeRootThreeLeg.meanAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k (v+s) (ω,x) := by
  unfold meanTheta MixedNativeRootThreeLeg.meanAverage
  apply integral_congr_ae
  filter_upwards with θ
  simpa only [HistoryProductMeasure.rootAverage,MixedNativeRootLegMass.meanField,MixedPastJointData.pastU,
    MixedPastJointData.pastD,ControlledReferenceLevel.referenceData,NNReal.coe_add] using
      meanValue_eq_absolute 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k θ v s ω x

end SHE.MovingMeanRootScalar



