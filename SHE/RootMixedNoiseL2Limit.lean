module

public import SHE.MixedHeatAveragedMark
public import SHE.RootJointHeatLeafLimit
public import SHE.RootJointReferenceLimit
public import SHE.RootJointRemainderConvergence
public import SHE.RootMixedMarkConvergence
public import SHE.RootMixedZeroHeatExpectation
public import SHE.JointHeatAveragedL2
public import SHE.JointHeatAveragedRemainder
public import SHE.ScalarL2LimitAlgebra
public import SHE.MixedJointIntegratedLevel
public import SHE.WeightedHistoryL2Limit
public import SHE.JointRecursiveHessian
public import SHE.NativeRowTargetContinuity
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.RootMixedNoiseL2Limit
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open scoped ENNReal NNReal
local instance mixedJointMarkConvergenceInstance1 : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance mixedJointMarkConvergenceInstance2 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedJointMarkConvergenceInstance3 : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance mixedJointMarkConvergenceInstance4 : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance mixedJointMarkConvergenceInstance5 : MeasurableSpace CircleL2 := borel _
local instance mixedJointMarkConvergenceInstance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedJointMarkConvergenceInstance7 : MeasurableSpace RealL2 := borel _
local instance mixedJointMarkConvergenceInstance8 : BorelSpace RealL2 := ⟨rfl⟩
variable {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} {n : ℕ} (L : Level R P n)
local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

open CutoffWordHistories RootHeatBounds Filter Topology
variable (δ : ℝ) (hδ : 0<δ)

local notation "Mmark" => RootMixedMarkLimit.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ
local notation "D" => MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "I" => fun ε k => JointWordDefect.integrand (level L δ hδ ε k) Λ U V XU XV (D (level L δ hδ ε k))



/-- The actual complete physical noise converges strongly as the ORIGINAL
root heat gap and all inserted heat ages reach ZERO. Only the existing
proved scalar root L1 limit is required; delta and finite depth stay fixed. -/
theorem noise_limit (hΛ:0≤Λ) (ν:Measure P) [IsFiniteMeasure ν]
    (hstart:∀p,R.base<L.terminal p)
    (hroot:RootMixedZeroHeatExpectation.RootConverges 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S L δ hδ ν)(k:ℕ):
    let E:=fun ε:ℝ=>fun ω=>∫p,
      MixedJointIntegratedLevel.noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (level L δ hδ ε.toNNReal k) p ω-
      MixedJointIntegratedLevel.noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (level L δ hδ 0 k) p ω ∂historyMeasure R ν k
    (∀ε,Integrable (fun ω=>‖E ε ω‖^2) μ) ∧
      Tendsto (fun ε=>∫ω,‖E ε ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
  intro E
  let σ:=historyMeasure R ν k
  let FL:=fun ε:ℝ≥0=>fun z:History P k×Ω=>MixedJointLevelData.leaf
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k) z.1 z.2
  let FR:=fun ε:ℝ≥0=>fun z:History P k×Ω=>MixedJointLevelData.reference
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k) z.1 z.2
  let FC:=fun ε:ℝ≥0=>fun z:History P k×Ω=>MixedJointLevelData.localRemainder
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k) z.1 z.2
  let FM:=fun ε:ℝ≥0=>fun z:History P k×Ω=>Mmark ε k z.1 z.2
  let error:=fun (F:ℝ≥0→History P k×Ω→ℝ)=>fun ε:ℝ=>fun ω=>∫p,F ε.toNNReal (p,ω)-F 0 (p,ω) ∂σ
  have hfmL(ε:ℝ≥0):Measurable (FL ε):=MixedJointLevelData.leaf_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k)
  have hfmR(ε:ℝ≥0):Measurable (FR ε):=MixedJointLevelData.reference_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k)
  have hfmC(ε:ℝ≥0):Measurable (FC ε):=MixedJointLevelData.localRemainder_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k)
  have hfmM(ε:ℝ≥0):Measurable (FM ε):=MixedJointLevelData.mark_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k)
  have hem (F:ℝ≥0→History P k×Ω→ℝ) (hm:∀ε,Measurable (F ε)) (ε:ℝ):Measurable (error F ε):=
    ((((hm ε.toNNReal).sub (hm 0)).comp measurable_swap).stronglyMeasurable.integral_prod_right').measurable
  have avg (F:ℝ≥0→History P k×Ω→ℝ)(hm:∀ε,Measurable (F ε))
      (C:ℝ)(hC:0≤C)(hb:∀ε p ω,‖F ε (p,ω)‖≤C)
      (ht:Tendsto (fun ε:ℝ=>∫q,‖F ε.toNNReal q-F 0 q‖ ∂σ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0)):
      (∀ε,Integrable (fun ω=>‖error F ε ω‖^2) μ) ∧
        Tendsto (fun ε=>∫ω,‖error F ε ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    exact WeightedHistoryL2Limit.averaged_limit σ μ (fun ε:ℝ=>F ε.toNNReal) (F 0)
      (fun ε=>hm ε.toNNReal) (hm 0) (fun _=>1) (integrable_const 1) (fun _=>zero_le_one) hC
      (fun ε p ω=>by simpa only [mul_one] using hb ε.toNNReal p ω)
      (fun p ω=>by simpa only [mul_one] using hb 0 p ω) (𝓝[>] (0:ℝ)) ht
  obtain ⟨B,hB,hBb⟩:=(RootHeatBounds.test_uniform L δ hδ k).norm_bound
  have hbL:∀ε p ω,‖FL ε (p,ω)‖≤B:=fun ε p ω=>hBb (ε,p) _
  have hbR:∀ε p ω,‖FR ε (p,ω)‖≤B:=by
    intro ε p ω
    change ‖JointWordAnalytic.reference (level L δ hδ ε k) Λ U V XU XV p ω‖≤B
    rw [RootJointReferenceLimit.reference_eq_average]
    exact GaussianSmooth.average_norm_bound _ (hBb (ε,p)) _
  have htL:Tendsto (fun ε:ℝ=>∫q,‖FL ε.toNNReal q-FL 0 q‖ ∂σ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    simpa only [FL,MixedJointLevelData.leaf,RootJointHeatLeafLimit.leaf,Real.norm_eq_abs] using
      RootJointHeatLeafLimit.integrated_leaf_difference_tendsto_zero L δ hδ dU dV Λ ν hroot k
  have htR:Tendsto (fun ε:ℝ=>∫q,‖FR ε.toNNReal q-FR 0 q‖ ∂σ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    simpa only [FR,MixedJointLevelData.reference,Real.norm_eq_abs] using
      RootJointReferenceLimit.integrated_reference_difference_tendsto_zero L δ hδ Λ U V XU XV hstart
        (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable
        (dV).physicalField_measurable ν μ k
  obtain ⟨C,hC,hCb⟩:=RootJointRemainderConvergence.uniform_remainder_bound L δ hδ Λ U V XU XV k
  have htC:Tendsto (fun ε:ℝ=>∫q,‖FC ε.toNNReal q-FC 0 q‖ ∂σ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    simpa only [FC,MixedJointLevelData.localRemainder,RootJointRemainderConvergence.remainder,Real.norm_eq_abs] using
      RootJointRemainderConvergence.integrated_remainder_difference_tendsto_zero L δ hδ Λ U V XU XV
        (dU).physicalState_measurable (dV).physicalState_measurable (dU).physicalField_measurable
        (dV).physicalField_measurable ν μ k
  obtain ⟨MarkCap,hD,hDb⟩:=RootMixedMarkConvergence.uniform_mark_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S L δ hδ hΛ k
  have htM:Tendsto (fun ε:ℝ=>∫q,‖FM ε.toNNReal q-FM 0 q‖ ∂σ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    simpa only [FM,Real.norm_eq_abs] using
      RootMixedMarkConvergence.integrated_mark_difference_tendsto_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ v₀ S L δ hδ hΛ ν k
  have hL:=avg FL hfmL B hB hbL htL
  have hR:=avg FR hfmR B hB hbR htR
  have hC:=avg FC hfmC C hC (fun ε p ω=>hCb ε p ω) htC
  have hM:=avg FM hfmM MarkCap hD (fun ε p ω=>hDb ε p ω) htM
  change (∀ε,Integrable (fun ω=>‖error FL ε ω‖^2) μ) ∧
    Tendsto (fun ε=>∫ω,‖error FL ε ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) at hL
  change (∀ε,Integrable (fun ω=>‖error FR ε ω‖^2) μ) ∧
    Tendsto (fun ε=>∫ω,‖error FR ε ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) at hR
  change (∀ε,Integrable (fun ω=>‖error FC ε ω‖^2) μ) ∧
    Tendsto (fun ε=>∫ω,‖error FC ε ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) at hC
  change (∀ε,Integrable (fun ω=>‖error FM ε ω‖^2) μ) ∧
    Tendsto (fun ε=>∫ω,‖error FM ε ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) at hM
  have hLR:=ScalarL2LimitAlgebra.sub μ (error FL) (error FR) (hem FL hfmL) (hem FR hfmR)
    hL.1 hR.1 (𝓝[>] (0:ℝ)) hL.2 hR.2
  have hLRC:=ScalarL2LimitAlgebra.sub μ (fun ε ω=>error FL ε ω-error FR ε ω) (error FC)
    (fun ε=>(hem FL hfmL ε).sub (hem FR hfmR ε)) (hem FC hfmC)
    hLR.1 hC.1 (𝓝[>] (0:ℝ)) hLR.2 hC.2
  have hfinal:=ScalarL2LimitAlgebra.sub μ
    (fun ε ω=>error FL ε ω-error FR ε ω-error FC ε ω) (error FM)
    (fun ε=>((hem FL hfmL ε).sub (hem FR hfmR ε)).sub (hem FC hfmC ε)) (hem FM hfmM)
    hLRC.1 hM.1 (𝓝[>] (0:ℝ)) hLRC.2 hM.2
  have hparts(ε:ℝ≥0)(ω:Ω):Integrable (fun p=>FL ε (p,ω)) σ ∧
      Integrable (fun p=>FR ε (p,ω)) σ ∧ Integrable (fun p=>FC ε (p,ω)) σ ∧ Integrable (fun p=>FM ε (p,ω)) σ:=by
    obtain ⟨B,hB,hBb⟩:=MixedJointIntegratedLevel.uniform_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k) hΛ
    have hi (F:History P k×Ω→ℝ)(hm:Measurable F)(hb:∀p,‖F (p,ω)‖≤B):Integrable (fun p=>F (p,ω)) σ:=
      (integrable_const B).mono' (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (Eventually.of_forall hb)
    exact ⟨hi _ (hfmL ε) (fun p=>(hBb p ω).1),hi _ (hfmR ε) (fun p=>(hBb p ω).2.1),
      hi _ (hfmC ε) (fun p=>(hBb p ω).2.2.1),hi _ (hfmM ε) (fun p=>(hBb p ω).2.2.2.1)⟩
  have he:E=fun ε ω=>error FL ε ω-error FR ε ω-error FC ε ω-error FM ε ω:=by
    funext ε ω
    obtain ⟨hl,hr,hc,hm⟩:=hparts ε.toNNReal ω
    obtain ⟨hl0,hr0,hc0,hm0⟩:=hparts 0 ω
    have hh:E ε ω=∫p,(FL ε.toNNReal (p,ω)-FL 0 (p,ω))-
        (FR ε.toNNReal (p,ω)-FR 0 (p,ω))-(FC ε.toNNReal (p,ω)-FC 0 (p,ω))-
        (FM ε.toNNReal (p,ω)-FM 0 (p,ω)) ∂σ:=by
      apply integral_congr_ae
      filter_upwards with p
      dsimp only [MixedJointIntegratedLevel.noiseVersion,FL,FR,FC,FM,RootMixedMarkLimit.mark]
      ring
    rw [hh]
    have hs1:=integral_sub (hl.sub hl0) (hr.sub hr0)
    have hs2:=integral_sub ((hl.sub hl0).sub (hr.sub hr0)) (hc.sub hc0)
    have hs3:=integral_sub (((hl.sub hl0).sub (hr.sub hr0)).sub (hc.sub hc0)) (hm.sub hm0)
    simp only [Pi.sub_apply] at hs1 hs2 hs3
    dsimp only [error]
    linarith only [hs1,hs2,hs3]
  rw [he]
  exact hfinal

end SHE.RootMixedNoiseL2Limit
