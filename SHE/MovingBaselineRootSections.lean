module

public import SHE.MovingMarkRootTheta
public import SHE.MovingMarkRootShift
public import SHE.MovingProfileBudget
public import SHE.MixedPastBaselineRMS

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingBaselineRootSections
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingBaselineRootSections_realSigma : MeasurableSpace RealL2 := borel _
local instance movingBaselineRootSections_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingBaselineRootSections_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingBaselineRootSections_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingBaselineRootSections_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingBaselineRootSections_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingBaselineRootSections_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingBaselineRootSections_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingBaselineRootSections_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingBaselineRootSections_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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




local notation "BV"=>MovingMarkRootFields.baselineValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "BT"=>MovingMarkRootTheta.baselineTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- The literal moving-window baseline section retains the entire
original gain and true past difference energy. Its depth-zero
contribution is exactly zero. -/
theorem actual_section_energy (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hH : (H:ℝ)≤1)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(h:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (h:ℝ)≤P.horizon) (k : ℕ) (hold : ∀ j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (Bpast : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (k+2) J B0)
    (v s : ℝ≥0) (hvH : v+h≤H) (hs : 0<s) (hsh : s<h) :
    let C:=MixedPastBaselineRMS.momentConstant P k
      ((NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
    let N:=(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)
    let En:=∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ
    Integrable (fun ω : Ω×HeatCircle=>|BT k (v,(s,ω))|^2) (μ.prod AddCircle.haarAddCircle) ∧
      (∫ ω : Ω×HeatCircle,|BT k (v,(s,ω))|^2 ∂μ.prod AddCircle.haarAddCircle)≤C*N^2*
        (MovingProfileBudget.baseline P (fraction P*P.lower) (uniformConstant 1) k h A0 ν s)^2*En := by
  intro C N En
  have hEn : 0≤En:=integral_nonneg (fun _=>sq_nonneg _)
  have hages' : ∀ x i,((ZT v).observations x i).stop≤((ZT v).observations x i).target := by
    intro x i
    change (Z.observations x i).stop+(v:ℝ)≤(Z.observations x i).target+(v:ℝ)
    linarith [hages x i]
  have hroot' : ∀ x i,((ZT v).observations x i).stop≤((v+h:ℝ≥0):ℝ) := by
    intro x i
    change (Z.observations x i).stop+(v:ℝ)≤((v+h:ℝ≥0):ℝ)
    rw [NNReal.coe_add]
    linarith [hrootStop x i]
  have htarg' : ∀ x i,((ZT v).observations x i).target=((v+h:ℝ≥0):ℝ) := by
    intro x i
    change (Z.observations x i).target+(v:ℝ)=((v+h:ℝ≥0):ℝ)
    rw [hrootTarget,NNReal.coe_add,add_comm]
  have hc' : ∀ x i,((ZT v).observations x i).center=x:=by
    intro x i
    have hi : i=0:=Subsingleton.elim _ _
    change (Z.observations x i).center=x
    simpa only [hi] using hcenter x
  have hbsub : ((v+h:ℝ≥0):ℝ)-(v:ℝ)=(h:ℝ):=by simp only [NNReal.coe_add,add_sub_cancel_left]
  have hqsub : ((v+s:ℝ≥0):ℝ)-(v:ℝ)=(s:ℝ):=by simp only [NNReal.coe_add,add_sub_cancel_left]
  have hqb : v+s<v+h:=by exact_mod_cast (show (v:ℝ)+(s:ℝ)<(v:ℝ)+(h:ℝ) by linarith [show (s:ℝ)<(h:ℝ) from hsh])
  have hqH : v+s≤H:=(le_of_lt hqb).trans hvH
  have hvH' : v≤H:=(show v≤v+h from le_self_add).trans hvH
  have hv1 : (v:ℝ)≤1:=(show (v:ℝ)≤(H:ℝ) from by exact_mod_cast hvH').trans hH
  have heval (θ : ℝ) (ω : Ω×HeatCircle) : BV k (θ,(v,(s,ω)))=
      ∫ t : Fin k→ℝ,∫ w : Fin k→HeatCircle,
        MixedNativeMarkedBudgets.baseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
          P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm
          k θ (v+s) ω.1 (HistoryProductMeasure.separated k (ω.2,t,fun i=>w i+ω.2))
        ∂Measure.pi (fun _=>AddCircle.haarAddCircle)
        ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ))) :=
    MovingMarkRootShift.baseline_eq_absolute 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P P.coefficient haP h Z htarget hstop F hF hFm k θ v s ω.1 ω.2
  by_cases hk:k=0
  · subst k
    have hz (θ : ℝ) (ω : Ω×HeatCircle) : BV 0 (θ,(v,(s,ω)))=0:=by
      rw [heval]
      have hp (t : Fin 0→ℝ) (w : Fin 0→HeatCircle) : MixedNativeMarkedBudgets.baseline
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
          P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm
          0 θ (v+s) ω.1 (HistoryProductMeasure.separated 0 (ω.2,t,fun i=>w i+ω.2))=0:=by
        unfold MixedNativeMarkedBudgets.baseline ControlledFamilyLegFubini.baseline
          ActualBaselineMarkFields.point PhysicalChainArrays.baselineMark
        split_ifs <;> simp only [Finset.univ_eq_empty,Finset.sum_empty,neg_zero]
      simp only [hp,integral_zero]
    have hzt (ω : Ω×HeatCircle) : BT 0 (v,(s,ω))=0:=by
      unfold MovingMarkRootTheta.baselineTheta
      simp only [hz,integral_zero]
    simpa only [hzt,abs_zero,zero_pow (by decide : (2:ℕ)≠0),integral_zero,
      MovingProfileBudget.baseline,if_pos rfl,if_true,mul_zero,zero_mul] using
      (show Integrable (fun _ : Ω×HeatCircle=>(0:ℝ)) (μ.prod AddCircle.haarAddCircle) ∧ (0:ℝ)≤0 from ⟨integrable_const 0,le_rfl⟩)
  have he:=MixedPastBaselineRMS.old_time_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    J hIJ₀ hIJ₁ P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm
    hlocal hΛ hsmallPoint hsmallL2 hages' hroot' (by simpa only [hbsub] using hspan) htarg' hc'
    rfl hvH' hv1 1 (by decide) Bpast hBDGpast
  let Cost:=C*N^2*(MovingProfileBudget.baseline P (fraction P*P.lower) (uniformConstant 1) k h A0 ν s)^2*En
  have hC : 0≤C:=MixedPastBaselineRMS.momentConstant_nonneg P k _
  have hCost : 0≤Cost:=mul_nonneg (mul_nonneg (mul_nonneg hC (sq_nonneg _)) (sq_nonneg _)) hEn
  let G : ℝ×(Ω×HeatCircle)→ℝ:=fun z=>BV k (z.1,(v,(s,z.2)))
  have hG : Measurable G:=
    (MovingMarkRootFields.baselineValue_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P P.coefficient haP h Z htarget hstop F hF hFm hΛ hsmallPoint k).comp
        (measurable_fst.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_snd)))
  have hsθ : ∀ᵐ θ ∂MeanThetaAverage.thetaMeasure,
      Integrable (fun ω=>‖G (θ,ω)‖^2) (μ.prod AddCircle.haarAddCircle) ∧ (∫ ω,‖G (θ,ω)‖^2 ∂μ.prod AddCircle.haarAddCircle)≤|Real.sqrt Cost|^2 := by
    filter_upwards [ae_restrict_of_ae he,ae_restrict_mem measurableSet_Ioc] with θ ht hθ
    have htθ : |θ|≤1:=by rw [abs_of_nonneg hθ.1.le];exact hθ.2
    have hh:=ht htθ k (by simpa only [hbsub] using hold) (v+s) le_self_add hqH hqb
      A0 ν hA0 hν hjet B0 hBDG
    have hh:=hh.2
    rw [sq_abs,Real.sq_sqrt hCost]
    simpa only [MixedPastBaselineSpatialFields.averaged,MixedPastBaselineSpatialEnergy.relativeBaseline,G,heval,
      MixedNativeMarkedBudgets.baseline,MixedPastJointData.pastU,MixedPastJointData.pastD,Real.norm_eq_abs,sq_abs,Cost,C,N,En,
      MovingProfileBudget.baseline,if_neg hk,PastBaselineTime.budget,hbsub,hqsub] using hh
  have hAvg:=HilbertParameterAverage.energy (μ.prod AddCircle.haarAddCircle) MeanThetaAverage.thetaMeasure G hG (fun _=>|Real.sqrt Cost|)
    measurable_const (integrable_const _) (fun _=>abs_nonneg _)
    (hsθ.mono (fun _ h=>h.1)) (hsθ.mono (fun _ h=>h.2))
  refine ⟨by simpa only [G,MovingMarkRootTheta.baselineTheta,Real.norm_eq_abs] using hAvg.2.1,?_⟩
  simpa only [integral_const,probReal_univ,one_smul,sq_abs,Real.sq_sqrt hCost,G,MovingMarkRootTheta.baselineTheta,
    Real.norm_eq_abs] using hAvg.2.2

end SHE.MovingBaselineRootSections

