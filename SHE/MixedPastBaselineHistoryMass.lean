module

public import SHE.MixedPastProfileDerivative
public import SHE.HistoryRelativeSample
public import SHE.MixedNativeBaselineJointFields
public import SHE.MixedPastBaselineSpatialMass
public import SHE.MixedPastBaselineSpatialFields
public import SHE.PastBaselineTimeFields
public import SHE.HilbertFiniteAverage
public import SHE.MixedPastBaselineSpatialEnergy
public import SHE.BaselineStrictSupport
public import SHE.MixedPastBaselineLeafEnergy
public import SHE.MixedPastOmittedLeafAbsolute
public import SHE.FiniteSpatialBaseline
public import SHE.MixedPastBaselineFTCIdentity
public import SHE.MixedPastOmittedLeafSpatial
public import SHE.MixedPastBaselineEnergySections
public import SHE.BaselineUnitGain
public import SHE.ForestLeafMarkEnergy
public import SHE.MixedPastOmittedLeafMoments
public import SHE.ScalarRootSharpSections
public import SHE.HistoryRelativeSections
public import SHE.MixedPastDerivativeRMS
public import SHE.MixedPastOmittedMarkFields
public import SHE.MixedPastLiteralOmitted
public import SHE.ControlledThetaOmittedFields
public import SHE.ControlledFamilyProfileMarkFields
public import SHE.MixedPastLiteralFields
public import SHE.JointInterpolationFields
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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 650000

namespace SHE.MixedPastBaselineHistoryMass
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastBaselineHistoryMass_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastBaselineHistoryMass_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastBaselineHistoryMass_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastBaselineHistoryMass_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastBaselineHistoryMass_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastBaselineHistoryMass_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastBaselineHistoryMass_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastBaselineHistoryMass_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastBaselineHistoryMass_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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


open HistoryProductMeasure ScalarRootRelativeGeometry ProfileL2

open MixedPastBaselineSpatialEnergy MixedPastBaselineSpatialFields

def momentConstant (k : ℕ) (Cnative : ℝ) : ℝ:=
  ∑ j0 : Fin k,sqrt (MixedPastOmittedWord.momentConstant P k k 1 j0 ((k:ℝ)*Cnative))

theorem momentConstant_nonneg (k : ℕ) (Cnative : ℝ) : 0≤momentConstant P k Cnative:=
  Finset.sum_nonneg (fun j _=>sqrt_nonneg _)

local notation "Leg"=>MixedNativeMarkedBudgets.baseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Rzero"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)

include hIJ₀ hIJ₁ in
/-- Honest ABSOLUTE original-history mass of the actual random-past
baseline leg. Original sample/history/time Fubini and every input/word
correlation are discharged; this supplies the theta FTC integrability
condition before any cancellation or signed history averaging. -/
theorem history_mass (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon)
    (hA : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hcenter : ∀ x i,(Z.observations x i).center=x)
    (hinit : v₀=u₀) (hvH : v≤H) (hv1 : (v:ℝ)≤1)
    (p : ℕ) (hp : 0<p) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B) :
    ∀ᵐ θ ∂volume,|θ|≤1→∀ k : ℕ,
    (∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)→
    ∀ q : ℝ≥0,v≤q→q≤H→q<b→∀ A0 ν : ℝ,0≤A0→0≤ν→
    (∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)→
    ∀ B0 : ℝ≥0,StandardTerminalBDGPower (k+2) J B0→
    let budget:=PastBaselineTime.budget P (fraction P*P.lower) (uniformConstant 1) k b v q A0 ν
    Integrable (fun z : Ω×History HeatCircle k=>Leg k θ q z.1 z.2)
      (μ.prod (historyMeasure Rzero haarAddCircle k)) ∧
    (∫ z : Ω×History HeatCircle k,|Leg k θ q z.1 z.2|
      ∂μ.prod (historyMeasure Rzero haarAddCircle k))≤
      momentConstant P k ((NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)*
        (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)*budget*
          sqrt (∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ) := by
  have hsp:=MixedPastBaselineSpatialMass.spatial_mass
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmall hsmallL2 hages hrootStop hspan b hA hcenter
    hinit hvH hv1 p hp B hBDG
  filter_upwards [hsp] with θ hθ
  intro hθ1 k hsmallOld q hvq hqH hqb A0 ν hA0 hν hjet B0 hBDG0 budget
  let C:=momentConstant P k ((NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
  let E:=∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ
  let N:=(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)
  let K:=C*N*sqrt E
  let D:=fun t : Fin k→ℝ=>PastBaselineTime.restoredDensity Zero P (fraction P*P.lower) (uniformConstant 1)
    k q A0 ν (QuarterSpatialEvent.anchor k t)
  let Amp:=fun t=>K*D t
  have hT : ∀ x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have hK : 0≤K:=mul_nonneg (mul_nonneg (momentConstant_nonneg P k _) (Nat.cast_nonneg _)) (sqrt_nonneg _)
  have hD0 (t) : 0≤D t:=PastBaselineTime.density_nonneg Zero P (mul_pos (fraction_pos P) P.lower_pos)
    (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le) k q A0 ν _
  have hdt:=PastBaselineTime.old_time_bound Zero P b hT (mul_pos (fraction_pos P) P.lower_pos)
    (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le) k
    (show _≤(q:ℝ) from hvq) (show (q:ℝ)<(b:ℝ) from hqb) (le_refl _) hA0 hν
  have hFi : Measurable (fun z : Ω×History HeatCircle k=>Leg k θ q z.1 z.2):=by
    have hm:=MixedNativeBaselineJointFields.baseline_joint_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k
    convert! hm.comp ((measurable_const : Measurable (fun _ : Ω×History HeatCircle k=>(θ,(q:ℝ)))).prodMk measurable_id) using 1
    funext z
    simp only [Function.comp_apply,id_eq,Real.toNNReal_coe]
  have hbase : (Rzero).base=(v:ℝ):=rfl
  have hsections : ∀ᵐ t ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      Integrable (fun z : (Ω×HeatCircle)×(Fin k→HeatCircle)=>
        Leg k θ q z.1.1 (separated k (z.1.2,t,fun i=>z.2 i+z.1.2)))
        ((μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle))) ∧
      (∫ z : (Ω×HeatCircle)×(Fin k→HeatCircle),
        |Leg k θ q z.1.1 (separated k (z.1.2,t,fun i=>z.2 i+z.1.2))|
        ∂(μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle)))≤Amp t := by
    filter_upwards [hθ k] with t ht
    let a:=QuarterSpatialEvent.anchor k t
    by_cases ha:StrictHistory Zero k a ∧ (q:ℝ)<(carrier Zero k).terminal a
    · have hs : SmallHistory Zero (uniformHorizon 1) k a:=RelativeHistoryGeometry.smallHistory_of_span
        Zero b (fun _=>le_refl _) (fun x i=>(hA x i).le) (uniformHorizon 1) k hsmallOld a
      have hh:=ht q hvq hqH ha.2 ha.1 hs hθ1 A0 ν hA0 hν hjet B0 hBDG0
      refine ⟨hh.1,?_⟩
      have hd:=PastBaselineTime.density_of_active Zero P (fraction P*P.lower) (uniformConstant 1)
        k q A0 ν a ha.1 ha.2
      dsimp only [Amp,D]
      rw [hd]
      convert! hh.2 using 1 <;> dsimp only [K,C,momentConstant,N,E,PastWordTimeFields.total,a,QuarterSpatialEvent.anchor] <;> simp only [hbase] <;> ring
    · have hz (z : (Ω×HeatCircle)×(Fin k→HeatCircle)) :
          Leg k θ q z.1.1 (separated k (z.1.2,t,fun i=>z.2 i+z.1.2))=0:=by
        by_cases hs:StrictHistory Zero k a
        · exact MixedPastBaselineSpatialFields.point_zero_of_inactive
            𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
            P haP v b hvb Z htarget hstop F hF hFm k θ q t (fun hh=>ha ⟨hs,hh⟩) z
        · exact MixedPastBaselineSpatialFields.point_zero_of_not_strict
            𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
            P haP v b hvb Z htarget hstop F hF hFm k θ q t hs z
      simp only [hz,abs_zero,integral_zero]
      exact ⟨integrable_const 0,mul_nonneg hK (hD0 t)⟩
  have hh:=HistoryProductMeasure.relativeSample_integrable_bound Rzero μ k _ hFi Amp
    (hdt.1.const_mul K) hsections
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [integral_const_mul]
  have hb:=mul_le_mul_of_nonneg_left hdt.2 hK
  rw [hbase] at hb
  convert! hb using 1 <;> dsimp only [K,C,N,E,budget] <;> ring

end SHE.MixedPastBaselineHistoryMass
