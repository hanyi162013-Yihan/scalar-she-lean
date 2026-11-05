module

public import SHE.MixedCanonicalGradientHeatAverage
public import SHE.MixedNativeRandomHeatAnalyticLimit
public import SHE.ControlledReferenceRandomHeatLeafLimit
public import SHE.NativeVariableTerminalCap
public import SHE.MixedCanonicalGradientAverage
public import SHE.TerminalItoRawLimit
public import SHE.WeightedHistoryL2Limit
public import SHE.RecursiveHeatGradientContinuity
public import SHE.NativeRowTargetContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option quotPrecheck false
namespace SHE.MixedCanonicalGradientNoiseHeat
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic GaussianItoTest ControlledProfile ControlledReferenceLevel
open Filter Topology
open scoped ENNReal NNReal
local instance mixedCanonicalGradientNoiseHeat_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedCanonicalGradientNoiseHeat_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedCanonicalGradientNoiseHeat_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedCanonicalGradientNoiseHeat_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedCanonicalGradientNoiseHeat_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedCanonicalGradientNoiseHeat_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedCanonicalGradientNoiseHeat_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedCanonicalGradientNoiseHeat_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedCanonicalGradientNoiseHeat_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

open ControlledProfile ControlledReferenceLevel
variable (P : CanonicalCovariance.ProfileParameters) (hAs : SmoothCylinders.BoundedSmooth (fun z => κ+aV z))
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : SmoothCylinders.BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)
local notation "L" => ControlledReferenceRecursiveBounds.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ

local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (hΛ:0≤Λ) (hbH:b≤H)

variable (k:ℕ)
local notation "Obs" => (fun ε:ℝ≥0=>((L (0,0) ε k).observations.observations))
local notation "Terminal" => (fun ε:ℝ≥0=>((L (0,0) ε k).terminal))
local notation "Held"=>PredictablePastParameter.held v pastParameter (0,0)

local notation "Noise" => (fun ε:ℝ≥0=>fun z:CutoffWordHistories.History Unit k×Ω=>
  MixedJointPastExpectedLevel.noiseVersion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L (pastParameter z.2) ε k) z.1 z.2)
local notation "Leaf" => (fun ε:ℝ≥0=>fun z:CutoffWordHistories.History Unit k×Ω=>
  MixedJointLevelData.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L (pastParameter z.2) ε k) z.1 z.2)
local notation "Ref" => (fun ε:ℝ≥0=>fun z:CutoffWordHistories.History Unit k×Ω=>
  MixedJointLevelData.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L (pastParameter z.2) ε k) z.1 z.2)
local notation "Loc" => (fun ε:ℝ≥0=>fun z:CutoffWordHistories.History Unit k×Ω=>
  MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L (pastParameter z.2) ε k) z.1 z.2)
local notation "Mark" => (fun ε:ℝ≥0=>fun z:CutoffWordHistories.History Unit k×Ω=>
  MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L (pastParameter z.2) ε k) z.1 z.2)
local notation "R₀"=>ControlledReferenceLevel.referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)

include hsmall hΛ in
/-- The actual random-reference kth noise converges strongly in sample
L2 AFTER its full original-history average. This upgrades the proved
four physical L1 limits using fixed smooth-depth domination. -/
theorem averaged_noise_limit (ν:Measure Unit)[IsFiniteMeasure ν]:
    let σ:=CutoffWordHistories.historyMeasure R₀ ν k
    let E:=fun ε:ℝ=>fun ω=>∫h,Noise ε.toNNReal (h,ω)-Noise 0 (h,ω) ∂σ
    (∀ε,Integrable (fun ω=>‖E ε ω‖^2) μ) ∧
      Filter.Tendsto (fun ε=>∫ω,‖E ε ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
  intro σ E
  obtain ⟨C,hC,hCb⟩:=ControlledReferenceRecursiveResidualBounds.uniform_piece_bounds
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hΛ k
  have hnm(ε:ℝ≥0):Measurable (Noise ε):=
    MixedCanonicalGradientAverage.noise_joint_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k
  have hp(ε:ℝ≥0):Integrable (Leaf ε) (σ.prod μ) ∧ Integrable (Ref ε) (σ.prod μ) ∧
      Integrable (Loc ε) (σ.prod μ) ∧ Integrable (Mark ε) (σ.prod μ):=by
    simpa only [Measure.restrict_univ] using
      MixedNativeRandomRecursiveIdentity.pieces_integrable
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k σ Set.univ
  let eL:=fun ε:ℝ=>fun z:CutoffWordHistories.History Unit k×Ω=>‖Leaf ε.toNNReal z-Leaf 0 z‖
  let eR:=fun ε:ℝ=>fun z:CutoffWordHistories.History Unit k×Ω=>‖Ref ε.toNNReal z-Ref 0 z‖
  let eC:=fun ε:ℝ=>fun z:CutoffWordHistories.History Unit k×Ω=>‖Loc ε.toNNReal z-Loc 0 z‖
  let eM:=fun ε:ℝ=>fun z:CutoffWordHistories.History Unit k×Ω=>‖Mark ε.toNNReal z-Mark 0 z‖
  have hiL(ε:ℝ):Integrable (eL ε) (σ.prod μ):=((hp ε.toNNReal).1.sub (hp 0).1).norm
  have hiR(ε:ℝ):Integrable (eR ε) (σ.prod μ):=((hp ε.toNNReal).2.1.sub (hp 0).2.1).norm
  have hiC(ε:ℝ):Integrable (eC ε) (σ.prod μ):=((hp ε.toNNReal).2.2.1.sub (hp 0).2.2.1).norm
  have hiM(ε:ℝ):Integrable (eM ε) (σ.prod μ):=((hp ε.toNNReal).2.2.2.sub (hp 0).2.2.2).norm
  have hu:StronglyMeasurable pastParameter:=
    (MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v)
  have hl:=ControlledReferenceRandomHeatLeafLimit.integrated_leaf_difference_tendsto_zero
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall
    dU dV pastParameter hu hΛ ν k μ
  have hr:Filter.Tendsto (fun ε=>∫z,eR ε z ∂σ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    simpa only [eR,Measure.restrict_univ,Real.norm_eq_abs] using
      (MixedNativeRandomHeatAnalyticLimit.reference_converges
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ k σ Set.univ).1
  have hc:Filter.Tendsto (fun ε=>∫z,eC ε z ∂σ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    simpa only [eC,Measure.restrict_univ,Real.norm_eq_abs] using
      (MixedNativeRandomHeatAnalyticLimit.remainder_converges
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ k σ Set.univ).1
  have hm:Filter.Tendsto (fun ε=>∫z,eM ε z ∂σ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    simpa only [eM,Measure.restrict_univ,Real.norm_eq_abs] using
      (MixedNativeRandomHeatAnalyticLimit.mark_converges
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ k σ Set.univ).1
  have hl':Filter.Tendsto (fun ε=>∫z,eL ε z ∂σ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
    simpa only [eL,Real.norm_eq_abs,ControlledReferenceRandomHeatLeafLimit.leaf,MixedJointLevelData.leaf,σ] using hl
  have hsum:=((hl'.add hr).add hc).add hm
  simp only [add_zero] at hsum
  have hbound(ε:ℝ):
      (∫z,‖Noise ε.toNNReal z-Noise 0 z‖ ∂σ.prod μ)≤
        (∫z,eL ε z ∂σ.prod μ)+(∫z,eR ε z ∂σ.prod μ)+
          (∫z,eC ε z ∂σ.prod μ)+(∫z,eM ε z ∂σ.prod μ):=by
    calc
      _≤∫z,(eL ε+eR ε+eC ε+eM ε) z ∂σ.prod μ:=by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
          (((hiL ε).add (hiR ε)).add (hiC ε) |>.add (hiM ε))
        filter_upwards with z
        change ‖Noise ε.toNNReal z-Noise 0 z‖≤eL ε z+eR ε z+eC ε z+eM ε z
        have he:Noise ε.toNNReal z-Noise 0 z=
            (Leaf ε.toNNReal z-Leaf 0 z)-(Ref ε.toNNReal z-Ref 0 z)-
              (Loc ε.toNNReal z-Loc 0 z)-(Mark ε.toNNReal z-Mark 0 z):=by
          dsimp only [MixedJointPastExpectedLevel.noiseVersion]
          ring
        rw [he]
        exact (norm_sub_le _ _).trans (add_le_add
          ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
      _=_:=by
        have h12:Integrable (fun z=>eL ε z+eR ε z) (σ.prod μ):=(hiL ε).add (hiR ε)
        have h123:Integrable (fun z=>eL ε z+eR ε z+eC ε z) (σ.prod μ):=h12.add (hiC ε)
        change (∫z,eL ε z+eR ε z+eC ε z+eM ε z ∂σ.prod μ)=_
        rw [integral_add h123 (hiM ε),integral_add h12 (hiC ε),integral_add (hiL ε) (hiR ε)]
  have hlim:Filter.Tendsto (fun ε:ℝ=>∫z,‖Noise ε.toNNReal z-Noise 0 z‖ ∂σ.prod μ)
      (𝓝[>] (0:ℝ)) (𝓝 0):=
    squeeze_zero' (Filter.Eventually.of_forall (fun _=>integral_nonneg (fun _=>norm_nonneg _)))
      (Filter.Eventually.of_forall hbound) hsum
  exact WeightedHistoryL2Limit.averaged_limit σ μ (fun ε:ℝ=>Noise ε.toNNReal) (Noise 0)
    (fun ε=>hnm ε.toNNReal) (hnm 0) (fun _=>1) (integrable_const 1) (fun _=>zero_le_one) hC
    (fun ε h ω=>by simpa only [mul_one] using (hCb (pastParameter ω) ε.toNNReal h ω).2.2.2.2)
    (fun h ω=>by simpa only [mul_one] using (hCb (pastParameter ω) 0 h ω).2.2.2.2)
    (𝓝[>] (0:ℝ)) hlim

end SHE.MixedCanonicalGradientNoiseHeat
