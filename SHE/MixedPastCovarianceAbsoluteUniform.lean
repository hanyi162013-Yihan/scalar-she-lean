module

public import SHE.MixedPastCovarianceTimeFields
public import SHE.PastCovarianceRMS
public import SHE.MixedPastCovarianceSpatialAbsoluteUniform
public import SHE.HistoryRelativeSample
public import SHE.RandomScoreSpatialAverage
public import SHE.HistoryRelativeOldFirst
public import SHE.ScalarRootSharpSections
public import SHE.MixedPastScoreEnergy
public import SHE.RandomFutureCenters
public import SHE.PastMeanSections
public import SHE.QuarterSpatialEvent
public import SHE.PastCovarianceMassSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastCovarianceAbsoluteUniform
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceAbsoluteUniform_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceAbsoluteUniform_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceAbsoluteUniform_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceAbsoluteUniform_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceAbsoluteUniform_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceAbsoluteUniform_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
local instance mixedPastCovarianceAbsoluteUniform_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceAbsoluteUniform_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceAbsoluteUniform_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

open ScalarRootRelativeGeometry ControlledResidualScoreInput MeasurableGaussianScores
  ProfileStability QuarterSpatialEvent OrderedHeatForests
local notation "Actual" => MixedPastLiteralCovariance.actualPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "Point" => MixedPastCovarianceSpatialFields.relativePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mass" => MixedPastCovarianceSpatialFields.scoreMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- Genuine sample times ORIGINAL-history absolute covariance mass,
before any signed cancellation, with an envelope independent of theta.
All actual-profile and correlated native-word applicability is derived. -/
theorem actual_absolute_history (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH : v≤H) (hv1 : (v:ℝ)≤1)
    (Bpast : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (k : ℕ)
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (k+2) J B0) :
    ∀ᵐ θ ∂volume,∀ q : ℝ≥0,v≤q→q<b→q≤H→|θ|≤1→
      let CG:=MixedPastWordMoments.momentConstant P k k 1
        ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
      let E:=∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ
      let R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
      Integrable (Actual k θ q) (μ.prod (historyMeasure R haarAddCircle k)) ∧
      (∫ z,|Actual k θ q z| ∂μ.prod (historyMeasure R haarAddCircle k))≤
        PastCovarianceRMS.coefficient P k CG*Real.sqrt E*
          QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
            k ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) (MarkedProfileTimeFactors.freshDegree P) A0 ν := by
  have hsp:=MixedPastCovarianceSpatialAbsoluteUniform.actual_spatial_absolute
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallPoint hsmallL2 hvH hv1
      Bpast hBDGpast hages hrootStop hrootTarget hcenter hspan k
  filter_upwards [hsp] with θ hθsp
  intro q hvq hqb hqH hθ CG E R
  let D:=fun t : Fin k→ℝ=>PastMeanTimeFactors.totalIntegrand Zero P (fraction P*P.lower)
    (uniformConstant 1) k q (MarkedProfileTimeFactors.freshDegree P) A0 ν (anchor k t)
  let K:=PastCovarianceRMS.coefficient P k CG*Real.sqrt E
  have hCG : 0≤CG:=MixedPastWordMoments.momentConstant_nonneg _ _ _ _ _
  have hE : 0≤E:=integral_nonneg (fun _=>sq_nonneg _)
  have hK : 0≤K:=mul_nonneg (PastCovarianceRMS.coefficient_nonneg P k CG) (sqrt_nonneg _)
  have hScoreEll : 0<fraction P*P.lower:=mul_pos (fraction_pos P) P.lower_pos
  have hCs : ∀ j,0≤uniformConstant 1 j:=fun j=>(uniformConstant_pos 1 j).le
  have hDn (t) : 0≤D t:=PastMeanTimeFactors.totalIntegrand_nonneg Zero P hScoreEll (uniformConstant 1) hCs k q
    (MarkedProfileTimeFactors.freshDegree P) A0 ν _
  have hd:=PastMeanTimeFactors.old_time_budget Zero P (b:ℝ) (fun _=>rfl) hScoreEll (uniformConstant 1) hCs k
    (by exact_mod_cast hvq) (by exact_mod_cast hqb) le_rfl (MarkedProfileTimeFactors.freshDegree_pos P)
      (MarkedProfileTimeFactors.freshDegree_le_one P) hA0 hν
  have hs : ∀ᵐ t ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      Integrable (Point k θ q t) ((μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle))) ∧
      (∫ z,|Point k θ q t z| ∂(μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle)))≤K*D t := by
    filter_upwards [hθsp q hvq hqH hθ] with t ht
    by_cases ha : active Zero (b:ℝ) k q t
    · have hsmall : SmallHistory Zero (uniformHorizon 1) k (anchor k t):=
        RelativeHistoryGeometry.smallHistory_of_span Zero (b:ℝ) (fun _=>le_rfl)
          (fun x i=>(hrootTarget x i).le) (uniformHorizon 1) k hold (anchor k t)
      have hh:=ht ha hsmall A0 ν hA0 hν hjet B0 hBDG
      let scale:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k (anchor k t)*
        PastWordTimeFields.total Zero P k (anchor k t) A0 ν/2
      let gain:=ControlledProfile.sharpUnit P*(((1+k:ℕ):ℝ)/(P.lower/2)*
        (((carrier Zero k).terminal (anchor k t)-(q:ℝ))/2)^((P.exponent-1)/4)*(1+2/(((P.exponent-1)/4)+1)))
      have hg : (q:ℝ)<(carrier Zero k).terminal (anchor k t):=by
        simpa only [anchor,terminal_separated Zero (b:ℝ) (fun _=>rfl)] using ha.2
      have hscale : 0≤scale:=div_nonneg
        (mul_nonneg (timeWeight_nonneg Zero hScoreEll (uniformConstant 1) hCs k _ ha.1)
          (PastWordTimeFields.total_nonneg Zero P k _ A0 ν)) (by norm_num)
      have hgain : gain=PastCovarianceRMS.unitGain P (1+k)*
          ((carrier Zero k).terminal (anchor k t)-(q:ℝ))^(MarkedProfileTimeFactors.freshDegree P-1):=
        PastCovarianceRMS.gain_identity P (1+k) (sub_pos.mpr hg)
      have hgain0 : 0≤gain:=by rw [hgain];exact mul_nonneg (PastCovarianceRMS.unitGain_nonneg P _) (rpow_nonneg (sub_nonneg.mpr hg.le) _)
      have he : Real.sqrt ((CG*scale^2)*(gain^2*E))*(Fintype.card (Choices 1 k):ℝ)=K*D t := by
        rw [Real.sqrt_mul (mul_nonneg hCG (sq_nonneg scale)),Real.sqrt_mul hCG,Real.sqrt_mul (sq_nonneg gain)]
        simp only [Real.sqrt_sq_eq_abs,abs_of_nonneg hscale,abs_of_nonneg hgain0]
        rw [hgain]
        dsimp only [K,D,PastCovarianceRMS.coefficient,scale]
        rw [PastMeanTimeFactors.totalIntegrand,if_pos ⟨ha.1,hg⟩]
        ring
      refine ⟨hh.1,hh.2.trans_eq ?_⟩
      exact he
    · have hz (z) : Point k θ q t z=0:=MixedPastCovarianceTimeFields.relative_point_zero_of_not_active
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q t ha z
      constructor
      · have hfzero : Point k θ q t=(fun _=>(0:ℝ)):=funext hz
        rw [hfzero]
        exact integrable_const 0
      · simpa only [hz,abs_zero,integral_zero] using mul_nonneg hK (hDn t)
  have hm:=MixedPastLiteralCovariance.actualPoint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint k θ q
  have hj:=relativeSample_integrable_bound R μ k (Actual k θ q) hm (fun t=>K*D t) (hd.1.const_mul K) hs
  refine ⟨hj.1,hj.2.trans ?_⟩
  rw [integral_const_mul]
  have hh:=mul_le_mul_of_nonneg_left hd.2 hK
  have hbase : R.base=(v:ℝ):=rfl
  have hbase0 : (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)).base=(v:ℝ):=rfl
  have hhor0 : (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)).horizon=(b:ℝ):=rfl
  have hhor : R.horizon=(b:ℝ):=rfl
  simp only [K,D,hbase,hbase0,hhor,hhor0] at hh ⊢
  convert! hh using 1

end SHE.MixedPastCovarianceAbsoluteUniform
