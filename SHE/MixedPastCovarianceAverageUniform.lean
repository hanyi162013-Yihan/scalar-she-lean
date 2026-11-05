module

public import SHE.MixedPastCovarianceTimeFields
public import SHE.PastCovarianceRMS
public import SHE.MixedPastCovarianceSpatialUniform
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

namespace SHE.MixedPastCovarianceAverageUniform
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceAverageUniform_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceAverageUniform_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceAverageUniform_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceAverageUniform_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceAverageUniform_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceAverageUniform_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
local instance mixedPastCovarianceAverageUniform_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceAverageUniform_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceAverageUniform_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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
/-- The full literal covariance leg with the ACTUAL random past profile,
first averaged over original old space and then over original old time,
before the sample/output square. Every applicability condition is
proved and the genuine past energy remains the only random factor. -/
theorem actual_averaged_energy (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
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
      let old:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))
      let raw:=fun z : (Fin k→ℝ)×(Ω×HeatCircle)=>∫ w : Fin k→HeatCircle,
        Point k θ q z.1 (z.2,w) ∂Measure.pi (fun _=>haarAddCircle)
      Integrable raw (old.prod (μ.prod haarAddCircle)) ∧
      Integrable (fun z : Ω×HeatCircle=>|∫ t,raw (t,z) ∂old|^2) (μ.prod haarAddCircle) ∧
      (∫ z : Ω×HeatCircle,|∫ t,raw (t,z) ∂old|^2 ∂μ.prod haarAddCircle)≤
        (PastCovarianceRMS.coefficient P k CG*Real.sqrt E*
          QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
            k ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) (MarkedProfileTimeFactors.freshDegree P) A0 ν)^2 := by
  have hsp:=MixedPastCovarianceSpatialUniform.actual_spatial_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallPoint hsmallL2 hvH hv1
      Bpast hBDGpast hages hrootStop hrootTarget hcenter hspan k
  filter_upwards [hsp] with θ hθsp
  intro q hvq hqb hqH hθ CG E old raw
  have hraw : Measurable raw:=MixedPastCovarianceTimeFields.averaged_point_time_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      hΛ hsmallPoint k θ q
  have hsmall (t : Fin k→ℝ) : SmallHistory Zero (uniformHorizon 1) k (anchor k t):=
    RelativeHistoryGeometry.smallHistory_of_span Zero (b:ℝ) (fun _=>le_rfl)
      (fun x i=>(hrootTarget x i).le) (uniformHorizon 1) k hold (anchor k t)
  have hs:=hθsp q hvq hqH hθ
  have hs' : ∀ᵐ t ∂old,active Zero (b:ℝ) k q t→
      let a:=anchor k t
      let scale:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*
        PastWordTimeFields.total Zero P k a A0 ν/2
      let gain:=ControlledProfile.sharpUnit P*(((1+k:ℕ):ℝ)/(P.lower/2)*
        (((carrier Zero k).terminal a-(q:ℝ))/2)^((P.exponent-1)/4)*(1+2/(((P.exponent-1)/4)+1)))
      Integrable (fun z : Ω×HeatCircle=>‖raw (t,z)‖^2) (μ.prod haarAddCircle) ∧
        (∫ z : Ω×HeatCircle,‖raw (t,z)‖^2 ∂μ.prod haarAddCircle)≤
          (CG*scale^2)*(gain^2*E)*(Fintype.card (Choices 1 k):ℝ)^2 := by
    filter_upwards [hs] with t ht
    intro ha
    simpa only [Real.norm_eq_abs] using ht ha (hsmall t) A0 ν hA0 hν hjet B0 hBDG
  have hz (t : Fin k→ℝ) (ha : ¬active Zero (b:ℝ) k q t) (z : Ω×HeatCircle) : raw (t,z)=0:=by
    apply integral_eq_zero_of_ae
    exact ae_of_all _ (fun w=>MixedPastCovarianceTimeFields.relative_point_zero_of_not_active
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
        k θ q t ha (z,w))
  have hh:=PastCovarianceRMS.old_time_energy Zero (μ.prod haarAddCircle) P (b:ℝ) (fun _=>rfl)
    k q A0 ν CG E (by exact_mod_cast hvq) (by exact_mod_cast hqb) le_rfl hA0 hν
      (MixedPastWordMoments.momentConstant_nonneg _ _ _ _ _) (integral_nonneg (fun _=>sq_nonneg _)) raw hraw hs' hz
  have hbase : (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)).base=(v:ℝ):=rfl
  have hhor : (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)).horizon=(b:ℝ):=rfl
  simpa only [Real.norm_eq_abs,hbase,hhor] using hh

end SHE.MixedPastCovarianceAverageUniform
