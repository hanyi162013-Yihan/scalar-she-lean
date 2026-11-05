module

public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields
public import SHE.MixedPastKernelSections
public import SHE.ControlledFamilyMeanEnergy
public import SHE.MixedPastMeanInputEnergy
public import SHE.NativeKernelReindex
public import SHE.MeanInputTimeFields
public import SHE.MixedPastMeanFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option quotPrecheck false

namespace SHE.MixedPastMeanTimeFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanTimeFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanTimeFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanTimeFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanTimeFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanTimeFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanTimeFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedPastMeanTimeFields_finiteExponent : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastMeanTimeFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanTimeFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanTimeFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedPastMeanTimeFields_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
open NativeRandomKernel NormalizedKernelSplit QuarterSpatialEvent
local notation "Input" => MixedPastMeanInputEnergy.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastLiteralPoint.meanField MixedPastJointData.pastU MixedPastJointData.pastD

/-- The actual current mean is jointly Borel in interpolation, current
time, sample and history, including every inactive extension. -/
theorem mean_time_joint_measurable (k : ℕ) :
    Measurable (fun z : (ℝ×(ℝ≥0×Ω))×History HeatCircle k=>Mean k z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  have hU:=(S.first_predictable.mono (predictable_le_product 𝓕)).measurable
  have hV:=(S.second_predictable.mono (predictable_le_product 𝓕)).measurable
  have hD:=hV.sub hU
  apply (WithLp.measurable_toLp 2 (Fin (1+k)→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hT : Measurable (fun h : History HeatCircle k=>targets Zero k h i):=
    (carrier Zero k).observations.target_measurable i
  have hx : Measurable (fun h : History HeatCircle k=>centers Zero k h i):=
    (carrier Zero k).observations.center_measurable i
  have hs : Measurable (fun h : History HeatCircle k=>stops Zero k h i):=by
    change Measurable (fun h=>min ((carrier Zero k).observations.observations h i).stop (b:ℝ))
    exact ((carrier Zero k).observations.stop_measurable i).min measurable_const
  have hQ : Measurable (fun z : (ℝ×(ℝ≥0×Ω))×History HeatCircle k=>(z.1.2.1:ℝ)):=
    measurable_subtype_coe.comp measurable_fst.snd.fst
  have harg:=((hT.comp measurable_snd).sub hQ).prodMk (hx.comp measurable_snd)
  have hu:=functional_joint_measurable.comp ((hU.comp measurable_fst.snd).prodMk harg)
  have hd:=functional_joint_measurable.comp ((hD.comp measurable_fst.snd).prodMk harg)
  have he:=measurable_fst.fst.mul (((hs.comp measurable_snd).sub hQ).const_mul (-Λ)).exp
  have hh:=hu.add (he.mul hd)
  convert! hh using 1
  funext z
  simp only [MixedPastLiteralPoint.meanField,MixedPastJointData.mean,MixedNativePastThetaCentering.current,
    WithLp.ofLp_toLp,sub_add_cancel,Function.comp_def,Pi.add_apply,Pi.mul_apply]
  rfl

theorem input_time_joint_measurable (hΛ : 0≤Λ) (k : ℕ)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ) :
    Measurable (fun z : ℝ×((Fin k→ℝ)×(ℝ≥0×Ω))=>
      Input k z.1 z.2.2.1 mass ρ hmass hρ z.2.1 z.2.2.2) := by
  let W:=ℝ×((Fin k→ℝ)×(ℝ≥0×Ω))
  let a : W→ℝ×Inputs:=fun z=>(z.1,(U z.2.2.2,Dir z.2.2.2))
  let m : W→History HeatCircle k→WordRecursion.State (1+k):=
    fun z=>Mean k z.1 z.2.2.1 z.2.2.2
  let V : W→RealL2:=fun z=>S.second z.2.2.1 z.2.2.2-S.first z.2.2.1 z.2.2.2
  let Ref:=fun a : ℝ×Inputs=>referenceData P P.coefficient haP Λ a.1 v b hvb a.2
  let Q : W→ℝ:=fun z=>(z.2.2.1:ℝ)
  let G:=familyWeightedField Ref Base a k (fun _=>Λ) Q Q m (fun z=>z.2.1)
  have hQ : Measurable Q:=measurable_subtype_coe.comp measurable_snd.snd.fst
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hD := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have ha : Measurable a:=measurable_fst.prodMk
    ((hU.comp measurable_snd.snd.snd).prodMk (hD.comp measurable_snd.snd.snd))
  have hm : Measurable (fun z : W×History HeatCircle k=>m z.1 z.2):=
    (mean_time_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k).comp
        ((measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd)
  have hG : Measurable G:=ControlledFamilyMeanFields.familyWeightedField_measurable P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
    a ha k Q Q hQ hQ m hm (fun z=>z.2.1) measurable_snd.fst
  have hb : ∀ z : W,∃ B : ℝ,∀ y x,‖G (z,(y,x))‖≤B := by
    intro z
    obtain ⟨B,hB,hbound⟩:=ControlledFamilyKernelBounds.weightedSpatial_family_uniform_bound
      P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k hΛ (Q z) (Q z) z.2.1
    exact ⟨B,fun y x=>hbound (a z) (m z) y x⟩
  have hV : Measurable V:=((S.second_predictable.mono (predictable_le_product 𝓕)).measurable.sub
    (S.first_predictable.mono (predictable_le_product 𝓕)).measurable).comp measurable_snd.snd
  have hh:=(OneInputOperator.besselHalf mass ρ hmass hρ).continuous.measurable.comp
    (action_measurable hG hb (fun z=>embed (V z)) (embed.continuous.measurable.comp hV))
  have he (z : W) : Input k z.1 z.2.2.1 mass ρ hmass hρ z.2.1 z.2.2.2=
      OneInputOperator.besselHalf mass ρ hmass hρ (integralOperator G z (embed (V z))) := by
    have hr:=integralOperator_reindex G (fun ω : Ω=>(z.1,(z.2.1,(z.2.2.1,ω)))) z.2.2.2
    have hk : (fun w : Ω×(HeatCircle×HeatCircle)=>G ((z.1,(z.2.1,(z.2.2.1,w.1))),w.2))=
        MixedPastKernelFields.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
          k z.1 z.2.2.1 z.2.2.1 z.2.1 := by funext w;rfl
    rw [hk] at hr
    unfold MixedPastMeanInputEnergy.input
    rw [hr]
  have heq : (fun z : W=>Input k z.1 z.2.2.1 mass ρ hmass hρ z.2.1 z.2.2.2)=
      fun z=>OneInputOperator.besselHalf mass ρ hmass hρ (integralOperator G z (embed (V z))) := funext he
  rw [heq]
  exact hh

theorem average_time_joint_measurable (hΛ : 0≤Λ) (k : ℕ)
    (old : Measure (Fin k→ℝ)) [SFinite old] (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ) :
    Measurable (fun z : ℝ×(ℝ≥0×Ω)=>MixedPastMeanFields.average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k old z.1 z.2.1 mass ρ hmass hρ z.2.2) := by
  have hh:=input_time_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ k mass ρ hmass hρ
  exact (hh.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))).stronglyMeasurable.integral_prod_right'.measurable

end SHE.MixedPastMeanTimeFields
