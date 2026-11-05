module

public import SHE.MovingMarkRootFields
public import SHE.MeanThetaAverage
public import SHE.MovingMeanPhysicalField

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMarkRootTheta
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMarkRootTheta_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMarkRootTheta_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMarkRootTheta_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMarkRootTheta_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMarkRootTheta_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMarkRootTheta_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

local instance movingMarkRootTheta_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMarkRootTheta_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMarkRootTheta_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMarkRootTheta_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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


local notation "CV"=>MovingMarkRootFields.covarianceValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P A hA h Z htarget hstop F hF hFm
local notation "BV"=>MovingMarkRootFields.baselineValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P A hA h Z htarget hstop F hF hFm

def covarianceTheta (k : ℕ) (z : ℝ≥0×(ℝ≥0×(Ω×HeatCircle))) : ℝ :=
  ∫ θ,CV k (θ,z) ∂MeanThetaAverage.thetaMeasure

def baselineTheta (k : ℕ) (z : ℝ≥0×(ℝ≥0×(Ω×HeatCircle))) : ℝ :=
  ∫ θ,BV k (θ,z) ∂MeanThetaAverage.thetaMeasure
local notation "CT"=>covarianceTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P A hA h Z htarget hstop F hF hFm
local notation "BT"=>baselineTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P A hA h Z htarget hstop F hF hFm

theorem covarianceTheta_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (CT k) :=
  (MovingMarkRootFields.covarianceValue_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm hΛ hsmall k).stronglyMeasurable.integral_prod_left'.measurable

theorem baselineTheta_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (BT k) :=
  (MovingMarkRootFields.baselineValue_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm hΛ hsmall k).stronglyMeasurable.integral_prod_left'.measurable

def covarianceField (k : ℕ) (z : ℝ×(ℝ×(Ω×HeatCircle))) : ℝ :=
  if MovingMeanPhysicalField.valid H h z.1 z.2.1 then CT k (z.1.toNNReal,(z.2.1.toNNReal,z.2.2)) else 0

def baselineField (k : ℕ) (z : ℝ×(ℝ×(Ω×HeatCircle))) : ℝ :=
  if MovingMeanPhysicalField.valid H h z.1 z.2.1 then BT k (z.1.toNNReal,(z.2.1.toNNReal,z.2.2)) else 0

theorem covarianceField_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (covarianceField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k) := by
  have hmap : Measurable (fun z : ℝ×(ℝ×(Ω×HeatCircle))=>(z.1.toNNReal,(z.2.1.toNNReal,z.2.2))) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk
      ((measurable_real_toNNReal.comp measurable_snd.fst).prodMk measurable_snd.snd)
  have hm:=(covarianceTheta_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm hΛ hsmall k).comp hmap
  have hv : MeasurableSet {z : ℝ×(ℝ×(Ω×HeatCircle))|MovingMeanPhysicalField.valid H h z.1 z.2.1} :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd.fst).inter
        ((measurableSet_lt measurable_snd.fst measurable_const).inter
          (measurableSet_le (measurable_fst.add_const (h:ℝ)) measurable_const)))
  exact hm.ite hv measurable_const

theorem baselineField_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (baselineField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k) := by
  have hmap : Measurable (fun z : ℝ×(ℝ×(Ω×HeatCircle))=>(z.1.toNNReal,(z.2.1.toNNReal,z.2.2))) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk
      ((measurable_real_toNNReal.comp measurable_snd.fst).prodMk measurable_snd.snd)
  have hm:=(baselineTheta_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm hΛ hsmall k).comp hmap
  have hv : MeasurableSet {z : ℝ×(ℝ×(Ω×HeatCircle))|MovingMeanPhysicalField.valid H h z.1 z.2.1} :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd.fst).inter
        ((measurableSet_lt measurable_snd.fst measurable_const).inter
          (measurableSet_le (measurable_fst.add_const (h:ℝ)) measurable_const)))
  exact hm.ite hv measurable_const

end SHE.MovingMarkRootTheta

