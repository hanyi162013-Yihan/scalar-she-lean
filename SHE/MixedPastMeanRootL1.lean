module

public import SHE.MixedPastMeanThetaMass
public import SHE.HistoryFourierAverage
public import SHE.MixedNativeRootThreeLeg
public import SHE.MixedNativeRootLegMass

public import SHE.FamilyMeanCoordinates
public import SHE.MixedPastMeanLegIdentity
public import SHE.NativeFourierAverage
public import SHE.MixedPastMeanSupport
public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields
public import SHE.MixedPastKernelSections
public import SHE.ControlledFamilyMeanEnergy
public import SHE.ControlledFamilyMeanFirstMoment
public import SHE.PastMeanAbsoluteBudget
public import SHE.MixedPastMeanFirstMoment
public import SHE.MixedPastBaselineFTCIdentity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option quotPrecheck false

namespace SHE.MixedPastMeanRootL1
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanRootL1_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanRootL1_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanRootL1_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanRootL1_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanRootL1_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanRootL1_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
local instance mixedPastMeanRootL1_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanRootL1_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanRootL1_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

open NativeRandomKernel NormalizedKernelSplit QuarterSpatialEvent
local notation "Ref" => (fun a : ℝ×Inputs=>referenceData P P.coefficient haP Λ a.1 v b hvb a.2)

local notation "Input"=>MixedPastMeanInputEnergy.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Leg"=>MixedPastMeanLegIdentity.leg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastLiteralPoint.meanField MixedPastJointData.pastU MixedPastJointData.pastD

include hIJ₀ hIJ₁ in
theorem actual_meanAverage_integrable (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (Babs : ℝ≥0) (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (q : ℝ≥0) (hvq : v≤q) (hqb : q<b) (hqH : q≤H) (hq1 : (q:ℝ)≤1) :
    Integrable (MixedNativeRootThreeLeg.meanAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k q) (μ.prod haarAddCircle) := by
  have hi:=MixedPastMeanThetaMass.actual_theta_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hrootStop hrootTarget
    hspan k hfresh hold A0 ν hA0 hν hjet Babs hBDGabs q hvq hqb hqH hq1
  have hr:=thetaRootAverage_integrable (Ref (0,(0,0))) k (volume.restrict (Ioc (0:ℝ) 1)) μ
    (MixedNativeRootLegMass.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k q) hi
  exact hr.integral_prod_right

end SHE.MixedPastMeanRootL1

