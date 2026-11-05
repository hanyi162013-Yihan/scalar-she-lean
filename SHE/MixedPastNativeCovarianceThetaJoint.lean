module
public import SHE.ScalarFibreThetaEnergy
public import SHE.MixedPastNativeCovarianceThetaFields
public import SHE.ScalarFibreRMS
public import SHE.FiniteGaussianAveraging
public import SHE.SectionFirstMoment
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

namespace SHE.MixedPastNativeCovarianceThetaJoint
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

/- Literal physical random score mass in relative coordinates. -/
attribute [local irreducible] MixedPastNativeCovarianceMass.scoreMass MixedPastJointData.pastU MixedPastJointData.pastD

local notation "Mass"=>MixedPastNativeCovarianceMass.scoreMass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

def rms (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(z:ℝ×HeatCircle):ℝ:=
  Real.sqrt (∫ω,|Mass k z.1 q t ((ω,z.2),w)|^2 ∂μ)

include hIJ₀ hIJ₁ in
/-- Genuine theta/spatial square integrability, needed BEFORE pointwise
sample-L2 Minkowski in theta. This also discharges theta integrability
of the RMS amplitude on AE output x, without a convention-zero shortcut. -/
theorem actual_joint_energy (hΛ:0≤Λ)
    (hsmallPoint:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH:v≤H)(hv1:(v:ℝ)≤1)(Bpast:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(k:ℕ)(q:ℝ≥0)(hvq:v<q)
    (t:Fin k→ℝ)(ht:active Zero (b:ℝ) k q t)(w:Fin k→HeatCircle):
    let C:=(ControlledProfile.sharpUnit P*((q:ℝ)-(v:ℝ))^((P.exponent-1)/4))*
      ((((1+k:ℕ):ℝ)/(3*P.lower/8))*3)
    let G:=rms 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q t w
    Integrable (fun z=>G z^2) (MeanThetaAverage.thetaMeasure.prod haarAddCircle) ∧
      (∫z,G z^2 ∂MeanThetaAverage.thetaMeasure.prod haarAddCircle)≤
        C^2*(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ):=by
  intro C G
  have hm:Measurable (fun z:Ω×(ℝ×HeatCircle)=>Mass k z.2.1 q t ((z.1,z.2.2),w)):=
    (MixedPastNativeCovarianceThetaFields.scoreMass_joint_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      hΛ hsmallPoint k q t).comp
        (measurable_snd.fst.prodMk ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_const))
  apply ScalarFibreThetaEnergy.joint μ haarAddCircle MeanThetaAverage.thetaMeasure _ hm
  have hs:=MixedPastNativeCovarianceMass.actual_past_mass_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint hsmallL2 hvH hv1 Bpast hBDGpast hages hspan k q hvq
  filter_upwards [ae_restrict_of_ae hs] with θ hθ
  exact hθ t ht w

end SHE.MixedPastNativeCovarianceThetaJoint
