module

public import SHE.ControlledFamilyExpectedTransfer
public import SHE.RootHistoryFubini
public import SHE.ControlledFamilyFrontFields
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyRootAverageFTC
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyRootAverageFTC_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyRootAverageFTC_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyRootAverageFTC_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : VariableObservations.Family HeatCircle n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : HeatCircle×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Sig" => ControlledFamilyThreeLeg.sigma P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Tar" => ControlledFamilyThreeLeg.target P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Cen" => ControlledFamilyThreeLeg.center P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Value" => ControlledFamilyThreeLeg.value P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Mark" => ControlledFamilyThreeLeg.mark P A hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Active" => ControlledFamilyFrontFields.activeValue P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Physical" => ControlledFamilyPhysicalTransfer.physicalMark P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "R₀" => referenceData P A hA Λ 0 v b hvb (0,0)

local notation "ActiveMark" => ControlledFamilyHistoryTransfer.activeMark P A hA Λ v b hvb Z htarget hstop F hF hFm

theorem root_retained_transfer (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (k : ℕ)
    (p : Ω→Inputs) (hp : Measurable p) (q : Ω→ℝ) (hq : Measurable q)
    (U D : Ω→CircleL2) (hU : Measurable U) (hD : Measurable D)
    (hfinite : HasFiniteIntegral (fun z : ℝ×(Ω×History HeatCircle k)=>
      ActiveMark (p z.2.1) k z.2.2 (q z.2.1) (U z.2.1) (D z.2.1) z.1)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod (μ.prod (historyMeasure R₀ haarAddCircle k)))) :
    ∀ᵐ z : Ω×HeatCircle ∂μ.prod haarAddCircle,
      Integrable (fun θ=>HistoryProductMeasure.rootAverage R₀ k
        (fun a=>ActiveMark (p a.1) k a.2 (q a.1) (U a.1) (D a.1) θ) z)
        (volume.restrict (Ioc (0:ℝ) 1)) ∧
      (∫ θ in Ioc (0:ℝ) 1,HistoryProductMeasure.rootAverage R₀ k
        (fun a=>ActiveMark (p a.1) k a.2 (q a.1) (U a.1) (D a.1) θ) z)=
      HistoryProductMeasure.rootAverage R₀ k
        (fun a=>Active (p a.1) k a.2 (q a.1) (U a.1) (D a.1) 1) z-
      HistoryProductMeasure.rootAverage R₀ k
        (fun a=>Active (p a.1) k a.2 (q a.1) (U a.1) (D a.1) 0) z := by
  let G : ℝ×(Ω×History HeatCircle k)→ℝ:=fun z=>
    ActiveMark (p z.2.1) k z.2.2 (q z.2.1) (U z.2.1) (D z.2.1) z.1
  have hGm : Measurable G:=ControlledFamilyMarkedFields.active_mark_variable_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall k
    (fun z : ℝ×(Ω×History HeatCircle k)=>p z.2.1) (hp.comp measurable_snd.fst)
    (fun z=>z.2.2) measurable_snd.snd (fun z=>q z.2.1) (hq.comp measurable_snd.fst)
    (fun z=>U z.2.1) (fun z=>D z.2.1) (hU.comp measurable_snd.fst) (hD.comp measurable_snd.fst)
    Prod.fst measurable_fst
  have hGi : Integrable G ((volume.restrict (Ioc (0:ℝ) 1)).prod
      (μ.prod (historyMeasure R₀ haarAddCircle k))):=⟨hGm.aestronglyMeasurable,hfinite⟩
  let E1 : Ω×History HeatCircle k→ℝ:=fun a=>Active (p a.1) k a.2 (q a.1) (U a.1) (D a.1) 1
  let E0 : Ω×History HeatCircle k→ℝ:=fun a=>Active (p a.1) k a.2 (q a.1) (U a.1) (D a.1) 0
  have h1 : Integrable E1 (μ.prod (historyMeasure R₀ haarAddCircle k)):=
    ControlledFamilyExpectedTransfer.endpoint_product_integrable P A hA Λ v b hvb Z htarget hstop F hF hFm
      μ haarAddCircle k p hp q hq U D hU hD 1
  have h0 : Integrable E0 (μ.prod (historyMeasure R₀ haarAddCircle k)):=
    ControlledFamilyExpectedTransfer.endpoint_product_integrable P A hA Λ v b hvb Z htarget hstop F hF hFm
      μ haarAddCircle k p hp q hq U D hU hD 0
  have he : (fun a : Ω×History HeatCircle k=>∫ θ in Ioc (0:ℝ) 1,G (θ,a))=ᵐ[
      μ.prod (historyMeasure R₀ haarAddCircle k)] E1-E0 := by
    have hh:=(Measure.quasiMeasurePreserving_snd (μ:=μ) (ν:=historyMeasure R₀ haarAddCircle k)).ae
      (ControlledFamilyPhysicalTransfer.physical_transfer_all_parameters_ae
        P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall hroot hspan haarAddCircle k)
    filter_upwards [hh] with a ha
    by_cases hac : (v:ℝ)≤q a.1 ∧ q a.1<(carrier (Base (0,p a.1)) k).terminal a.2
    · have hi:=(ha (p a.1) (q a.1) hac.1 hac.2 (U a.1) (D a.1)).2 0 1
      have hf : (fun θ=>G (θ,a))=Physical (p a.1) k a.2 (q a.1) (U a.1) (D a.1):=
        funext (fun _=>if_pos hac)
      change (∫ θ in Ioc (0:ℝ) 1,G (θ,a))=E1 a-E0 a
      rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),hf]
      simpa only [E1,E0,ControlledFamilyFrontFields.activeValue,if_pos hac] using hi.2
    · have hf : (fun θ=>G (θ,a))=(fun _=>0):=funext (fun _=>if_neg hac)
      change (∫ θ in Ioc (0:ℝ) 1,G (θ,a))=E1 a-E0 a
      rw [hf]
      simp only [integral_zero,E1,E0,ControlledFamilyFrontFields.activeValue,if_neg hac,sub_self]
  have hs:=HistoryProductMeasure.root_average_swap R₀ k (volume.restrict (Ioc (0:ℝ) 1)) μ G hGm hGi
  have hc:=HistoryProductMeasure.root_average_congr_ae R₀ k μ _ _ he
  have hd:=HistoryProductMeasure.root_average_sub_ae R₀ k μ E1 E0 h1 h0
  filter_upwards [hs,hc,hd] with z hz hc hd
  exact ⟨hz.1,hz.2.trans (hc.trans hd)⟩

end SHE.ControlledFamilyRootAverageFTC
