module

public import SHE.MovingMarkRootTheta
public import SHE.MovingMarkRootShift
public import SHE.MovingProfileBudget
public import SHE.MixedPastCovarianceAverageUniform
public import SHE.MixedNativeCovarianceFTCIdentity

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.PastReferenceCovarianceSection
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingCovarianceRootSections_realSigma : MeasurableSpace RealL2 := borel _
local instance movingCovarianceRootSections_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingCovarianceRootSections_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingCovarianceRootSections_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingCovarianceRootSections_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingCovarianceRootSections_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingCovarianceRootSections_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingCovarianceRootSections_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingCovarianceRootSections_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingCovarianceRootSections_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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



local notation "CV"=>MovingMarkRootFields.covarianceValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "CT"=>MovingMarkRootTheta.covarianceTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Literal moving-window covariance section, with all original
histories and theta averaged before squaring. The true past energy
survives linearly, without any current-moment substitution. -/
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
    (v s : ℝ≥0) (hvH : v+h≤H) (hs : 0≤s) (hsh : s<h) :
    let CG:=MixedPastWordMoments.momentConstant P k k 1
      ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
    let K:=PastCovarianceRMS.coefficient P k CG
    let En:=∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ
    Integrable (fun ω : Ω×HeatCircle=>|CT k (v,(s,ω))|^2) (μ.prod AddCircle.haarAddCircle) ∧
      (∫ ω : Ω×HeatCircle,|CT k (v,(s,ω))|^2 ∂μ.prod AddCircle.haarAddCircle)≤K^2*
        (MovingProfileBudget.covariance P (fraction P*P.lower) (uniformConstant 1) k h A0 ν s)^2*En := by
  intro CG K En
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
  have hbsub : ((v+h:ℝ≥0):ℝ)-(v:ℝ)=(h:ℝ):=by simp only [NNReal.coe_add,add_sub_cancel_left]
  have hqsub : ((v+s:ℝ≥0):ℝ)-(v:ℝ)=(s:ℝ):=by simp only [NNReal.coe_add,add_sub_cancel_left]
  have hqb : v+s<v+h:=by exact_mod_cast (show (v:ℝ)+(s:ℝ)<(v:ℝ)+(h:ℝ) by linarith [show (s:ℝ)<(h:ℝ) from hsh])
  have hqH : v+s≤H:=(le_of_lt hqb).trans hvH
  have hvH' : v≤H:=(show v≤v+h from le_self_add).trans hvH
  have hv1 : (v:ℝ)≤1:=(show (v:ℝ)≤(H:ℝ) from by exact_mod_cast hvH').trans hH
  have he:=MixedPastCovarianceAverageUniform.actual_averaged_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm
    hlocal hΛ hsmallPoint hsmallL2 hvH' hv1 Bpast hBDGpast
    hages' hroot' htarg' hcenter (by simpa only [hbsub] using hspan) k
    (by simpa only [hbsub] using hold) A0 ν hA0 hν hjet B0 hBDG
  let Rms:=K*Real.sqrt En*MovingProfileBudget.covariance P (fraction P*P.lower) (uniformConstant 1) k h A0 ν s
  let G : ℝ×(Ω×HeatCircle)→ℝ:=fun z=>CV k (z.1,(v,(s,z.2)))
  have hG : Measurable G:=
    (MovingMarkRootFields.covarianceValue_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P P.coefficient haP h Z htarget hstop F hF hFm hΛ hsmallPoint k).comp
        (measurable_fst.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_snd)))
  have hsθ : ∀ᵐ θ ∂MeanThetaAverage.thetaMeasure,
      Integrable (fun ω=>‖G (θ,ω)‖^2) (μ.prod AddCircle.haarAddCircle) ∧ (∫ ω,‖G (θ,ω)‖^2 ∂μ.prod AddCircle.haarAddCircle)≤|Rms|^2 := by
    filter_upwards [ae_restrict_of_ae he,ae_restrict_mem measurableSet_Ioc] with θ ht hθ
    have htθ : |θ|≤1:=by rw [abs_of_nonneg hθ.1.le];exact hθ.2
    have hh:=(ht (v+s) le_self_add hqb hqH htθ).2
    have heval (ω : Ω×HeatCircle) : G (θ,ω)=
        ∫ t : Fin k→ℝ,∫ w : Fin k→HeatCircle,
          MixedPastLiteralCovariance.actualPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
            P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm
            k θ (v+s) (ω.1,HistoryProductMeasure.separated k (ω.2,t,fun i=>w i+ω.2))
          ∂Measure.pi (fun _=>AddCircle.haarAddCircle)
          ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ))) := by
      dsimp only [G]
      rw [MovingMarkRootShift.covariance_eq_absolute]
      apply integral_congr_ae
      filter_upwards [] with t
      apply integral_congr_ae
      filter_upwards [] with w
      exact MixedNativeCovarianceFTCIdentity.covariance_eq_actualPoint
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm
        hages' hroot' k θ (v+s) le_self_add ω.1 _
    simpa only [MixedPastCovarianceSpatialFields.relativePoint,heval,Real.norm_eq_abs,sq_abs,Rms,MovingProfileBudget.covariance,hbsub,hqsub] using hh
  have hAvg:=HilbertParameterAverage.energy (μ.prod AddCircle.haarAddCircle) MeanThetaAverage.thetaMeasure G hG (fun _=>|Rms|)
    measurable_const (integrable_const _) (fun _=>abs_nonneg _)
    (hsθ.mono (fun _ h=>h.1)) (hsθ.mono (fun _ h=>h.2))
  refine ⟨by simpa only [G,MovingMarkRootTheta.covarianceTheta,Real.norm_eq_abs] using hAvg.2.1,?_⟩
  have hnorm : |Rms|^2=K^2*
      (MovingProfileBudget.covariance P (fraction P*P.lower) (uniformConstant 1) k h A0 ν s)^2*En := by
    simp only [sq_abs,Rms,mul_pow,Real.sq_sqrt hEn]
    ring
  have hb:=hAvg.2.2
  simpa only [integral_const,probReal_univ,one_smul,hnorm,G,MovingMarkRootTheta.covarianceTheta,Real.norm_eq_abs] using hb

end SHE.PastReferenceCovarianceSection

