module

public import SHE.MovingNativeMarks

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMarkRootFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMarkRootFields_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMarkRootFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMarkRootFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMarkRootFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMarkRootFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMarkRootFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

local instance movingMarkRootFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMarkRootFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMarkRootFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMarkRootFields_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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

/-- The native output point is retained, before old-space/time or
interpolation averaging. -/
abbrev RootData := ℝ×(ℝ≥0×(ℝ≥0×(Ω×HeatCircle)))

def covarianceRaw (k : ℕ)
    (z : RootData (Ω:=Ω)×((Fin k→ℝ)×(Fin k→HeatCircle))) : ℝ :=
  MovingNativeMarks.covariance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm k
    (fun z : RootData (Ω:=Ω)×((Fin k→ℝ)×(Fin k→HeatCircle))=>z.1.2.1)
    (fun z=>z.1.2.2.1)
    (fun z=>HistoryProductMeasure.separated k (z.1.2.2.2.2,z.2.1,fun i=>z.2.2 i+z.1.2.2.2.2))
    (fun z=>z.1.1) (fun z=>z.1.2.2.2.1) z

def covarianceValue (k : ℕ) (z : RootData (Ω:=Ω)) : ℝ :=
  ∫ t : Fin k→ℝ,∫ w : Fin k→HeatCircle,
    covarianceRaw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k (z,(t,w))
    ∂Measure.pi (fun _=>AddCircle.haarAddCircle)
    ∂Measure.pi (fun _=>volume.restrict (Ioc (0:ℝ) (h:ℝ)))

theorem covarianceRaw_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (covarianceRaw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k) := by
  have hh : Measurable (fun z : RootData (Ω:=Ω)×((Fin k→ℝ)×(Fin k→HeatCircle))=>
      HistoryProductMeasure.separated k (z.1.2.2.2.2,z.2.1,fun i=>z.2.2 i+z.1.2.2.2.2)) :=
    (HistoryProductMeasure.separated_measurable k).comp
      (measurable_fst.snd.snd.snd.snd.prodMk (measurable_snd.fst.prodMk
        (Measurable.of_eval (fun i=>((measurable_pi_apply i).comp measurable_snd.snd).add
          measurable_fst.snd.snd.snd.snd))))
  exact MovingNativeMarks.covariance_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm hΛ hsmall k
    (fun z : RootData (Ω:=Ω)×((Fin k→ℝ)×(Fin k→HeatCircle))=>z.1.2.1)
    (fun z=>z.1.2.2.1) measurable_fst.snd.fst measurable_fst.snd.snd.fst
    _ hh (fun z=>z.1.1) measurable_fst.fst (fun z=>z.1.2.2.2.1) measurable_fst.snd.snd.snd.fst

theorem covarianceValue_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (covarianceValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k) := by
  have hm:=(covarianceRaw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm hΛ hsmall k).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

def baselineRaw (k : ℕ)
    (z : RootData (Ω:=Ω)×((Fin k→ℝ)×(Fin k→HeatCircle))) : ℝ :=
  MovingNativeMarks.baseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm k
    (fun z : RootData (Ω:=Ω)×((Fin k→ℝ)×(Fin k→HeatCircle))=>z.1.2.1)
    (fun z=>z.1.2.2.1)
    (fun z=>HistoryProductMeasure.separated k (z.1.2.2.2.2,z.2.1,fun i=>z.2.2 i+z.1.2.2.2.2))
    (fun z=>z.1.1) (fun z=>z.1.2.2.2.1) z

def baselineValue (k : ℕ) (z : RootData (Ω:=Ω)) : ℝ :=
  ∫ t : Fin k→ℝ,∫ w : Fin k→HeatCircle,
    baselineRaw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k (z,(t,w))
    ∂Measure.pi (fun _=>AddCircle.haarAddCircle)
    ∂Measure.pi (fun _=>volume.restrict (Ioc (0:ℝ) (h:ℝ)))

theorem baselineRaw_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (baselineRaw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k) := by
  have hh : Measurable (fun z : RootData (Ω:=Ω)×((Fin k→ℝ)×(Fin k→HeatCircle))=>
      HistoryProductMeasure.separated k (z.1.2.2.2.2,z.2.1,fun i=>z.2.2 i+z.1.2.2.2.2)) :=
    (HistoryProductMeasure.separated_measurable k).comp
      (measurable_fst.snd.snd.snd.snd.prodMk (measurable_snd.fst.prodMk
        (Measurable.of_eval (fun i=>((measurable_pi_apply i).comp measurable_snd.snd).add
          measurable_fst.snd.snd.snd.snd))))
  exact MovingNativeMarks.baseline_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm hΛ hsmall k
    (fun z : RootData (Ω:=Ω)×((Fin k→ℝ)×(Fin k→HeatCircle))=>z.1.2.1)
    (fun z=>z.1.2.2.1) measurable_fst.snd.fst measurable_fst.snd.snd.fst
    _ hh (fun z=>z.1.1) measurable_fst.fst (fun z=>z.1.2.2.2.1) measurable_fst.snd.snd.snd.fst

theorem baselineValue_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (k : ℕ) :
    Measurable (baselineValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k) := by
  have hm:=(baselineRaw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm hΛ hsmall k).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

end SHE.MovingMarkRootFields
