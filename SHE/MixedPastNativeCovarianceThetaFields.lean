module
public import SHE.MixedPastNativeCovarianceMass
public import SHE.MeanThetaAverage

public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastNativeScoreEnergy
public import SHE.NativePastAgeScoreEnergy
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

namespace SHE.MixedPastNativeCovarianceThetaFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceSpatialFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceSpatialFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceSpatialFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceSpatialFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
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
local instance mixedPastCovarianceSpatialFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceSpatialFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

/-- Literal physical random score mass in relative coordinates. -/
local notation "Mass"=>MixedPastNativeCovarianceMass.scoreMass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Joint theta/sample/root/old-space Borel field BEFORE any theta or
sample Fubini. The physical signed profile direction remains genuine. -/
theorem scoreMass_joint_measurable (hΛ:0≤Λ)
    (hsmall:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ):
    Measurable (fun z:ℝ×((Ω×HeatCircle)×(Fin k→HeatCircle))=>Mass k z.1 q t z.2):=by
  let a:=anchor k t
  let σ:=fun i=>stops Zero k a i-(v:ℝ)
  let target:=fun i=>targets Zero k a i-(v:ℝ)
  let lo:=fun j=>lower Zero k a j-(v:ℝ)
  let hi:=fun j=>upper Zero k a j-(v:ℝ)
  let u:ℝ×(Ω×(Fin k→HeatCircle))→CircleL2:=fun z=>U z.2.1
  let d:ℝ×(Ω×(Fin k→HeatCircle))→CircleL2:=fun z=>Dir z.2.1
  have hU:=(MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hDir:=(MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hu:Measurable u:=hU.comp measurable_snd.fst
  have hd:Measurable d:=hDir.comp measurable_snd.fst
  let c:(ℝ×(Ω×(Fin k→HeatCircle)))×ControlledProfile.Domain→ℝ:=fun z=>
    ControlledProfile.profile P Λ (u z.1) (d z.1) (z.1.1,z.2)-
      NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ (u z.1) (d z.1) lo hi) z.2
  let e:(ℝ×(Ω×(Fin k→HeatCircle)))×ControlledProfile.Domain→ℝ:=fun z=>
    ControlledProfile.derivative P Λ (u z.1) (d z.1) (z.2,z.1.1)
  have hmap:Measurable (fun z:(ℝ×(Ω×(Fin k→HeatCircle)))×ControlledProfile.Domain=>((z.1,z.1.1),z.2)):=
    (measurable_fst.prodMk measurable_fst.fst).prodMk measurable_snd
  have hc:Measurable c:=by
    convert! ((ControlledProfile.random_profile_measurable P hu hd Λ).comp hmap).sub
      ((VaryingControlledGaussianFields.fixed_profile_measurable P Λ u d hu hd lo hi).add_const _) using 1
  have he:Measurable e:=by
    have hm:Measurable (fun z:(ℝ×(Ω×(Fin k→HeatCircle)))×ControlledProfile.Domain=>(z,z.1.1)):=
      measurable_id.prodMk measurable_fst.fst
    convert! (ControlledProfile.random_derivative_measurable P hΛ u d hu hd hsmall).comp hm using 1
  let center:ℝ×(Ω×(Fin k→HeatCircle))→Fin (1+k)→HeatCircle:=
    fun z=>values (fun _:Fin 1=>(0:HeatCircle)) k z.2.2
  have hcenter:Measurable center:=(values_continuous (fun _:Fin 1=>(0:HeatCircle)) k).measurable.comp measurable_snd.snd
  have hh:=futureInput_random_centers_measurable σ target center hcenter c e hc he ((q:ℝ)-(v:ℝ))
  have hm:Measurable (fun z:ℝ×((Ω×HeatCircle)×(Fin k→HeatCircle))=>
      ((z.1,(z.2.1.1,z.2.2)),z.2.1.2)):=
    (measurable_fst.prodMk (measurable_snd.fst.fst.prodMk measurable_snd.snd)).prodMk measurable_snd.fst.snd
  convert! hh.comp hm using 1

end SHE.MixedPastNativeCovarianceThetaFields
