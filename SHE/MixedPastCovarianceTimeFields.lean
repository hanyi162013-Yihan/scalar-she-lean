module

public import SHE.MixedPastCovarianceSpatialEnergy
public import SHE.InactivePhysicalAverage
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

namespace SHE.MixedPastCovarianceTimeFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceTimeFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceTimeFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceTimeFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceTimeFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceTimeFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceTimeFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
local instance mixedPastCovarianceTimeFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceTimeFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceTimeFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

/-- The original old-time/sample/output field is jointly Borel before
any spatial or temporal averaging. -/
theorem relative_point_time_measurable (hΛ : 0≤Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (θ : ℝ) (q : ℝ≥0) :
    Measurable (fun z : ((Fin k→ℝ)×(Ω×HeatCircle))×(Fin k→HeatCircle)=>
      Point k θ q z.1.1 (z.1.2,z.2)) := by
  let p : ((Fin k→ℝ)×(Ω×HeatCircle))×(Fin k→HeatCircle)→History HeatCircle k:=
    fun z=>separated k (z.1.2.2,z.1.1,fun i=>z.2 i+z.1.2.2)
  have hsites : Measurable (fun z : ((Fin k→ℝ)×(Ω×HeatCircle))×(Fin k→HeatCircle)=>
      fun i=>z.2 i+z.1.2.2):=measurable_pi_iff.mpr (fun i=>
    ((measurable_pi_apply i).comp measurable_snd).add measurable_fst.snd.snd)
  have hp : Measurable p:=(separated_measurable k).comp
    (measurable_fst.snd.snd.prodMk (measurable_fst.fst.prodMk hsites))
  have hh:=MixedPastLiteralCovariance.actualPoint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint k θ q
  convert! hh.comp (measurable_fst.snd.fst.prodMk hp) using 1

theorem averaged_point_time_measurable (hΛ : 0≤Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (θ : ℝ) (q : ℝ≥0) :
    Measurable (fun z : (Fin k→ℝ)×(Ω×HeatCircle)=>∫ w : Fin k→HeatCircle,
      Point k θ q z.1 (z.2,w) ∂Measure.pi (fun _=>haarAddCircle)) :=
  (relative_point_time_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint k θ q).stronglyMeasurable.integral_prod_right'.measurable

/-- Inactive original time sections vanish pointwise with the same
random past profile retained, before all integrals. -/
theorem relative_point_zero_of_not_active (k : ℕ) (θ : ℝ) (q : ℝ≥0) (t : Fin k→ℝ)
    (ha : ¬active Zero (b:ℝ) k q t) (z : (Ω×HeatCircle)×(Fin k→HeatCircle)) :
    Point k θ q t z=0 := by
  classical
  let a : ℝ×Inputs:=(θ,(U z.1.1,Dir z.1.1))
  let p : History HeatCircle k:=separated k (z.1.2,t,fun i=>z.2 i+z.1.2)
  by_cases hs : StrictHistory Zero k (anchor k t)
  · have hn : ¬(q:ℝ)<(carrier (Base a) k).terminal p := by
      intro hq
      have he:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
        a (0,(0,0)) k p
      rw [he] at hq
      have hh : (q:ℝ)<fixedTerminal (R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) (b:ℝ) k t:=by
        simpa only [p,terminal_separated Zero (b:ℝ) (fun _=>rfl)] using hq
      exact ha ⟨hs,hh⟩
    change ActualCovarianceMarkFields.point (Base a) _ _ k q _ p=0
    simp only [ActualCovarianceMarkFields.point,if_neg hn]
  · have hn : ¬StrictHistory (Base a) k p := by
      intro hp
      have hz : StrictHistory Zero k p:=
        (ControlledThetaPhysicalGeometry.strict_iff P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
          a (0,(0,0)) k p).mp hp
      exact hs ((FixedHistoryTimeFactors.strict_sections Zero (b:ℝ) (fun _=>rfl) k t z.1.2 0 _ _).mp hz)
    change ActualCovarianceMarkFields.point (Base a) _ _ k q _ p=0
    unfold ActualCovarianceMarkFields.point
    split_ifs
    · rw [oldAverage_zero_of_not_strict (Base a) _ k p hn]
      simp only [FiniteWordScores.covarianceMark,Pi.zero_apply,zero_mul,integral_zero,mul_zero]
    · rfl

theorem relative_average_eq (k : ℕ) (θ : ℝ) (q : ℝ≥0) (t : Fin k→ℝ) (ω : Ω) (x : HeatCircle) :
    (∫ w : Fin k→HeatCircle,Point k θ q t ((ω,x),w) ∂Measure.pi (fun _=>haarAddCircle))=
      ∫ w : Fin k→HeatCircle,Actual k θ q (ω,separated k (x,t,w)) ∂Measure.pi (fun _=>haarAddCircle) :=
  (relativeShift_preserving k x).integral_comp' (fun w : Fin k→HeatCircle=>
    Actual k θ q (ω,separated k (x,t,w)))

end SHE.MixedPastCovarianceTimeFields
