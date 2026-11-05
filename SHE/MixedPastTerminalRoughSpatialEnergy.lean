module

public import SHE.MixedPastTerminalSourceSections
public import SHE.MixedPastTerminalSourceFields
public import SHE.TranslatedTwoSourceAverage
public import SHE.RandomProfilePairSource
public import SHE.MixedPastTerminalSlotSpatial
public import SHE.ControlledTerminalPairedSections
public import SHE.HistoryRelativeEvenMoment
public import SHE.MixedPastTerminalRootHistory
public import SHE.MixedPastTerminalRoughHistory
public import SHE.PairedTerminalConstants
public import SHE.MixedPastTerminalPairedActive
public import SHE.MixedPastTerminalRootEnvelope
public import SHE.HistoryNewestMoment
public import SHE.ControlledTerminalPairedAmplitude
public import SHE.ControlledRelativeScoreForest
public import SHE.TerminalConditionalGeometry
public import SHE.ParentMeanDensity
public import SHE.MixedPastTerminalPairedIdentity
public import SHE.MixedPastTerminalPairedFields
public import SHE.ControlledTerminalPairedRelative
public import SHE.TerminalSuccessorGeometry
public import SHE.MixedPastTerminalState
public import SHE.MixedPastTerminalFirstState
public import SHE.JointHistoryFields
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastTerminalRoughSpatialEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralPoint_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralPoint_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralPoint_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralPoint_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralPoint_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralPoint_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastLiteralPoint_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralPoint_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastLiteralPoint_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

local notation "DataU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "DataV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S


open MixedPastTerminalPairedFields


local notation "G" => MixedPastTerminalPairedActive.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Raw" => MixedPastTerminalPairedFields.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Amp" => ControlledTerminalPairedAmplitude.amplitude P haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Sc" => ControlledTerminalPairedAmplitude.scale P haP Λ v b hvb Z htarget hstop F hF hFm


open HistoryProductMeasure OrderedHeatForests Classical ProfileL2 ProfileStability
local notation "Src"=>MixedPastTerminalSources.source 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "TimeAmp"=>MixedPastTerminalSlotSpatial.timeAmplitude Λ P haP v b hvb Z htarget hstop F hF hFm

/-- The actual rough paired source is multiplied back into its literal
normalized word BEFORE spatial averaging. Both true current energy and
true past difference energy survive; every old score and complementary
rough time gain stays in TimeAmp. -/
theorem section_energy (hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (hsmall:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ) (t:Fin k→ℝ) (hp:StrictHistory Zero k (MixedPastTerminalSlotSpatial.anchor k t))
    (choices:List (Fin k×Fin (k+1))) {A0 ν χ:ℝ} (hν:0≤ν)
    (hχ:0≤χ) (hχβ:χ<P.exponent) (j:Fin k)
    (order:ℕ) (horder:0<order) (ho0:1≤(order:ℝ)*(1-χ))
    (ho1:1≤(order:ℝ)*(1-χ/P.exponent))
    (C:ℝ) (hC:0≤C)
    (hMom:∀ᵐ w:Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),
      let GG:=fun y:Ω×HeatCircle=>G k choices ν χ j.succ
        (separated k (y.2,t,fun l=>w l+y.2)) y.1
      Integrable (fun y=>|GG y|^(2*order)) (μ.prod haarAddCircle) ∧
      (∫y,|GG y|^(2*order) ∂μ.prod haarAddCircle)≤
        C*(TimeAmp k t choices χ A0 ν j.succ*
          parentDensity 2 (by norm_num) k (targets Zero k (MixedPastTerminalSlotSpatial.anchor k t))
            (carrier_orderedTimes Zero hages k _ hp) (values (fun _:Fin 1=>(0:HeatCircle)) k w))^(2*order))
    (hcurrent:Integrable (fun ω=>‖S.second (((carrier Zero k).terminal (MixedPastTerminalSlotSpatial.anchor k t)).toNNReal) ω-
      S.first (((carrier Zero k).terminal (MixedPastTerminalSlotSpatial.anchor k t)).toNNReal) ω‖^2) μ)
    (hpast:Integrable (fun ω=>‖Dir ω‖^2) μ)
    (hage:targets Zero k (MixedPastTerminalSlotSpatial.anchor k t) (leafIndex k (fun i:Fin (1+k)=>i) j)-(v:ℝ)∈Ioc 0 P.horizon):
    let Q:=(carrier Zero k).terminal (MixedPastTerminalSlotSpatial.anchor k t)
    let E0:=∫ω,‖S.second Q.toNNReal ω-S.first Q.toNNReal ω‖^2 ∂μ
    let E1:=(2*P.holder)^2*(∫ω,‖Dir ω‖^2 ∂μ)^P.exponent
    let V:=fun z:(Ω×HeatCircle)×(Fin k→HeatCircle)=>
      Src k choices ν χ j.succ (separated k (z.1.2,t,fun l=>z.2 l+z.1.2)) z.1.1*
        G k choices ν χ j.succ (separated k (z.1.2,t,fun l=>z.2 l+z.1.2)) z.1.1
    Integrable V ((μ.prod haarAddCircle).prod (Measure.pi (fun _:Fin k=>haarAddCircle))) ∧
      Integrable (fun y=>|∫w,V (y,w) ∂Measure.pi (fun _:Fin k=>haarAddCircle)|^2) (μ.prod haarAddCircle) ∧
      (∫y,|∫w,V (y,w) ∂Measure.pi (fun _:Fin k=>haarAddCircle)|^2 ∂μ.prod haarAddCircle)≤
        2*C^(1/(order:ℝ))*(max 1 (P.holder^(χ/P.exponent))^2*E0^χ+E1^(χ/P.exponent))*
          (TimeAmp k t choices χ A0 ν j.succ*(Fintype.card (Choices 1 k):ℝ))^2:=by
  intro Q E0 E1 V
  let anchor:=MixedPastTerminalSlotSpatial.anchor k t
  let idx:=leafIndex k (fun i:Fin (1+k)=>i) j
  let age:=targets Zero k anchor idx-(v:ℝ)
  let τ:=targets Zero k anchor idx-Q
  let Uq:Ω→RealL2:=fun ω=>S.first Q.toNNReal ω
  let Vq:Ω→RealL2:=fun ω=>S.second Q.toNNReal ω
  have hUq:Measurable Uq:=
    ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted Q.toNNReal).measurable.mono (𝓕.le _) le_rfl
  have hVq:Measurable Vq:=
    ((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted Q.toNNReal).measurable.mono (𝓕.le _) le_rfl
  let f0:=NativeCurrentSourceEnergy.value Uq Vq τ
  let f1:Ω×HeatCircle→ℝ:=fun y=>profile P Λ (U y.1) (Dir y.1) (1,(age,y.2))-
    profile P Λ (U y.1) (Dir y.1) (0,(age,y.2))
  have hf0:=NativeCurrentSourceEnergy.value_measurable Uq Vq hUq hVq τ
  have hi0:=NativeCurrentSourceEnergy.product_energy μ Uq Vq hUq hVq hcurrent τ
  have hu:Measurable U:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd:Measurable Dir:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hf1:Measurable f1:=by
    have hm(a:ℝ):Measurable (fun y:Ω×HeatCircle=>((y.1,a),(age,y.2))):=
      (measurable_fst.prodMk measurable_const).prodMk (measurable_const.prodMk measurable_snd)
    convert! ((random_profile_measurable P hu hd Λ).comp (hm 1)).sub
      ((random_profile_measurable P hu hd Λ).comp (hm 0)) using 1
  have hi1:Integrable (fun y=>f1 y^2) (μ.prod haarAddCircle) ∧
      (∫y,f1 y^2 ∂μ.prod haarAddCircle)≤E1:=by
    have hh:=RandomProfilePairSource.energy P hΛ U Dir hu hd hsmall μ hpast 1 0
      hage P.exponent_pos.le (le_refl P.exponent)
    have he:2*P.exponent/P.exponent=2:=by field_simp [P.exponent_pos.ne']
    simp only [div_self P.exponent_pos.ne',Real.rpow_one,sub_zero,abs_one,Real.one_rpow,
      mul_one,he,Real.rpow_two,sq_abs] at hh
    convert! hh using 1
  let z: (Fin k→HeatCircle)→HeatCircle:=fun w=>values (fun _:Fin 1=>(0:HeatCircle)) k w idx
  have hz:Measurable z:=(continuous_apply idx).measurable.comp (values_continuous (fun _:Fin 1=>(0:HeatCircle)) k).measurable
  let K: (Fin k→HeatCircle)→ℝ:=fun w=>parentDensity 2 (by norm_num) k (targets Zero k anchor)
    (carrier_orderedTimes Zero hages k anchor hp) (values (fun _:Fin 1=>(0:HeatCircle)) k w)
  have hKc:Continuous K:=(ForestedScoreInput.parentDensity_continuous 2 (by norm_num) k _ _).comp
    (values_continuous (fun _:Fin 1=>(0:HeatCircle)) k)
  have hKi:Integrable K (Measure.pi (fun _:Fin k=>haarAddCircle)):=
    hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ht0:0≤TimeAmp k t choices χ A0 ν j.succ:=by
    apply mul_nonneg
    · exact timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1)
        (fun l=>(uniformConstant_pos 1 l).le) k anchor hp
    · exact abs_nonneg _
  let HH:=fun w=>TimeAmp k t choices χ A0 ν j.succ*K w
  have hHi:Integrable HH (Measure.pi (fun _:Fin k=>haarAddCircle)):=hKi.const_mul _
  have hHm:Measurable HH:=measurable_const.mul hKc.measurable
  have hH0(w):0≤HH w:=mul_nonneg ht0 (parentDensity_nonneg 2 (by norm_num) k _ _ _)
  let FF:=fun z:(Ω×HeatCircle)×(Fin k→HeatCircle)=>G k choices ν χ j.succ
    (separated k (z.1.2,t,fun l=>z.2 l+z.1.2)) z.1.1
  let SS:=fun z:(Ω×HeatCircle)×(Fin k→HeatCircle)=>Src k choices ν χ j.succ
    (separated k (z.1.2,t,fun l=>z.2 l+z.1.2)) z.1.1
  have hhist:Measurable (fun z:(Ω×HeatCircle)×(Fin k→HeatCircle)=>
      separated k (z.1.2,t,fun l=>z.2 l+z.1.2)):=
    (separated_measurable k).comp (measurable_fst.snd.prodMk (measurable_const.prodMk
      (Measurable.of_eval (fun l=>((measurable_pi_apply l).comp measurable_snd).add measurable_fst.snd))))
  have hFF:Measurable FF:=(MixedPastTerminalPairedActive.point_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
    k choices ν χ j.succ).comp (hhist.prodMk measurable_fst.fst)
  have hSS:Measurable SS:=by
    convert! (MixedPastTerminalSourceFields.source_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
    k choices ν χ j.succ).comp (hhist.prodMk measurable_fst.fst) using 1
  have hb(y:Ω×HeatCircle)(w:Fin k→HeatCircle):|SS (y,w)|≤
      max 1 (P.holder^(χ/P.exponent))*|f0 (y.1,y.2+z w)|^χ+|f1 (y.1,y.2+z w)|^(χ/P.exponent):=by
    convert! MixedPastTerminalSourceSections.rough_relative_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
      hΛ hrootage hcenter k t choices hν hχ j y.2 w y.1 using 1
  have hh:=TranslatedTwoSourceAverage.energy μ (Measure.pi (fun _:Fin k=>haarAddCircle))
    FF SS hFF hSS f0 f1 hf0 hf1 hi0.1 hi1.1 z z hz hz HH hHm hHi hH0
    hχ (lt_of_lt_of_le hχβ P.exponent_le_one) (div_nonneg hχ P.exponent_pos.le)
    ((div_lt_one P.exponent_pos).mpr hχβ) (by positivity) hC
    (integral_nonneg (fun _=>sq_nonneg _)) (by positivity) hi0.2 hi1.2 order horder ho0 ho1 hMom hb
  simpa only [HH,K,integral_const_mul,ForestedScoreInput.parentDensity_mass] using hh

end SHE.MixedPastTerminalRoughSpatialEnergy
