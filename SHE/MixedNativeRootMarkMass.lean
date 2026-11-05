module

public import SHE.MixedPastCovarianceAbsoluteUniform
public import SHE.MixedPastMeanAbsolute
public import SHE.MixedPastBaselineHistoryMass
public import SHE.MixedNativeCovarianceFTCIdentity
public import SHE.ControlledFamilyRootAverageFTC
public import SHE.ControlledFamilyLegFubini
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

namespace SHE.MixedNativeRootMarkMass
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeRootMarkMass_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeRootMarkMass_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeRootMarkMass_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeRootMarkMass_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeRootMarkMass_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeRootMarkMass_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
local instance mixedNativeRootMarkMass_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeRootMarkMass_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeRootMarkMass_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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
/-- Absolute theta/sample/original-history integrability of the ACTUAL
three-leg field. All three envelopes are derived from the constructed
mixed native pair; no new Fubini applicability input remains. -/
theorem marked_integrable (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
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
    (hfresh : (b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (k+2) J B0)
    (q : ℝ≥0) (hvq : v≤q) (hqb : q<b) (hqH : q≤H) (hq1 : (q:ℝ)≤1) :
    Integrable (fun z : ℝ×(Ω×History HeatCircle k)=>
      ControlledFamilyHistoryTransfer.activeMark P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
        (U z.2.1,Dir z.2.1) k z.2.2 q (embed (S.first q z.2.1))
        (embed (S.second q z.2.1-S.first q z.2.1)) z.1)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod
        (μ.prod (historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) haarAddCircle k))) := by
  have hc:=MixedPastCovarianceAbsoluteUniform.actual_absolute_history
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hsmallPoint hsmallL2 hvH hv1 Bpast hBDGpast
    hages hrootStop hrootTarget hcenter hspan k hold A0 ν hA0 hν hjet B0 hBDG
  have hcAll : ∀ x i,(Z.observations x i).center=x:=by
    intro x i
    have hi:i=0:=Subsingleton.elim _ _
    simpa only [hi] using hcenter x
  have hb:=MixedPastBaselineHistoryMass.history_mass
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hsmallPoint hsmallL2 hages hrootStop hspan hrootTarget hcAll rfl hvH hv1 1 (by decide) Bpast hBDGpast
  let CG:=MixedPastWordMoments.momentConstant P k k 1
    ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
  let Ev:=∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ
  let Eq:=∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ
  let Ec:=PastCovarianceRMS.coefficient P k CG*Real.sqrt Ev*
    QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
      k ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) (MarkedProfileTimeFactors.freshDegree P) A0 ν
  let Em:=Real.sqrt Eq*(Real.sqrt CG*((1+k:ℕ):ℝ)*Real.sqrt (2*UniformFutureProfileScores.constant (1+k)/P.lower))*
    ((haarAddCircle (T:=2*Real.pi)).real univ*(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)*
      QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
        k ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) (1/2:ℝ) A0 ν)
  let Eb:=MixedPastBaselineHistoryMass.momentConstant P k
      ((NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)*
    (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)*
      PastBaselineTime.budget P (fraction P*P.lower) (uniformConstant 1) k b v q A0 ν*Real.sqrt Ev
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hD := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hUq := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S q).mono (𝓕.le q) le_rfl
  have hDq := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S q).mono (𝓕.le q) le_rfl
  apply (ControlledFamilyLegFubini.product_integrable_of_leg_budgets P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm hΛ hsmallPoint μ haarAddCircle k
    (fun ω=>(U ω,Dir ω)) (hU.prodMk hD) (fun _=>(q:ℝ)) measurable_const
    (fun ω=>embed (S.first q ω)) (fun ω=>embed (S.second q ω-S.first q ω)) hUq hDq
    (fun _=>Ec) (fun _=>Em) (fun _=>Eb)
    intervalIntegrable_const intervalIntegrable_const intervalIntegrable_const ?_ ?_ ?_).1
  · filter_upwards [ae_restrict_of_ae hc,ae_restrict_mem measurableSet_Ioc] with θ ht hθ
    have htθ : |θ|≤1:=by rw [abs_of_nonneg hθ.1.le];exact hθ.2
    have hh:=ht q hvq hqb hqH htθ
    have heval (z : Ω×History HeatCircle k) :
        ControlledFamilyLegFubini.covariance P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
          (U z.1,Dir z.1) k z.2 q (embed (S.first q z.1)) (embed (S.second q z.1-S.first q z.1)) θ=
        Actual k θ q z:=MixedNativeCovarianceFTCIdentity.covariance_eq_actualPoint
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
          hages hrootStop k θ q hvq z.1 z.2
    simp_rw [heval]
    exact hh
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have htθ : |θ|≤1:=by rw [abs_of_nonneg hθ.1.le];exact hθ.2
    have hm:=MixedPastMeanAbsolute.actual_absolute_history
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
      hlocal hΛ hages hrootStop hrootTarget hspan haarAddCircle k hfresh hold θ htθ A0 ν hA0 hν hjet B0 hBDG
      q hvq hqb hqH hq1
    simpa only [MixedPastMeanLegIdentity.leg,CG,Eq,Em] using hm
  · filter_upwards [ae_restrict_of_ae hb,ae_restrict_mem measurableSet_Ioc] with θ ht hθ
    have htθ : |θ|≤1:=by rw [abs_of_nonneg hθ.1.le];exact hθ.2
    have hh:=ht htθ k hold q hvq hqH hqb A0 ν hA0 hν hjet B0 hBDG
    simpa only [MixedNativeMarkedBudgets.baseline,Eb,Ev] using hh

end SHE.MixedNativeRootMarkMass
