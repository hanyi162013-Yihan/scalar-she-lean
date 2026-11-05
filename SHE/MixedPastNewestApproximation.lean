module
public import SHE.MixedPastNewestIntegratedError
public import SHE.NewestIntegratedConstants
public import SHE.MixedPastNewestTimeFields
public import SHE.NewestErrorConstants
public import SHE.ScalarApproximationDiscrepancy
public import SHE.PastNewestOldTimeEnergy
public import SHE.MixedPastNewestFields
public import SHE.ParentScoreInput
public import SHE.ParentMeanMass
public import SHE.WeightedSFiniteMoments
public import SHE.PastWordTimeFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
namespace SHE.MixedPastNewestApproximation
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestApproximation_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestApproximation_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestApproximation_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestApproximation_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestApproximation_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestApproximation_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestApproximation_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestApproximation_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestApproximation_period : Fact (0<2*π):=⟨by positivity⟩
attribute [local irreducible] MixedPastNewestError.value WordRecursion.directionalSecond
  GaussianConvolution.gaussianAverage UncutSmoothWords.test MeasurableGaussianScores.scoreVariance
  MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Value"=>MixedPastNewestError.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

open HistoryProductMeasure OrderedHeatForests
open ActualMeanKernel
local notation "Active"=>MixedPastNewestFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

open scoped Topology

theorem scalarError_tendsto (D:SmoothApproximation.ScalarData):
    Filter.Tendsto (ScalarApproximationDiscrepancy.scalarError D) Filter.atTop (𝓝 (0:ℝ)):=by
  change Filter.Tendsto (fun j=>D.holderConstant*CompactMollifier.radius j^D.beta) _ _
  simpa only [Real.zero_rpow D.beta_pos.ne',mul_zero] using
    (CompactMollifier.radius_tendsto.rpow_const (Or.inr D.beta_pos.le)).const_mul D.holderConstant

def budget (D:SmoothApproximation.ScalarData)(P:CanonicalCovariance.ProfileParameters)
    (κ M:ℝ)(v b:ℝ≥0)(B Hr:ℝ)(k:ℕ)(B0:ℝ≥0)(A0 ν:ℝ)(j:ℕ):ℝ:=
  (ScalarApproximationDiscrepancy.scalarError D j)^2*
    MixedPastNewestCurrentEnergy.constant κ (M:=M) P v b B Hr k B0 A0 ν*
      (((b:ℝ)-(v:ℝ))^(P.exponent/8)/(P.exponent/8))^2

theorem budget_tendsto (D:SmoothApproximation.ScalarData)(Q:CanonicalCovariance.ProfileParameters)
    (κ M:ℝ)(v b:ℝ≥0)(B Hr:ℝ)(k:ℕ)(B0:ℝ≥0)(A0 ν:ℝ):
    Filter.Tendsto (budget D Q κ M v b B Hr k B0 A0 ν) Filter.atTop (𝓝 (0:ℝ)):=by
  change Filter.Tendsto (fun j=>(ScalarApproximationDiscrepancy.scalarError D j)^2*
    MixedPastNewestCurrentEnergy.constant κ (M:=M) Q v b B Hr k B0 A0 ν*
      (((b:ℝ)-(v:ℝ))^(Q.exponent/8)/(Q.exponent/8))^2) _ _
  simpa only [zero_pow (by norm_num : 2≠0),zero_mul] using
    (((scalarError_tendsto D).pow 2).mul_const
      (MixedPastNewestCurrentEnergy.constant κ (M:=M) Q v b B Hr k B0 A0 ν)).mul_const
        ((((b:ℝ)-(v:ℝ))^(Q.exponent/8)/(Q.exponent/8))^2)

include hIJ₀ hIJ₁ in
/-- Actual one-state ordinary U-side error at every canonical smoothing
index. The majorant uses the common rough numerical parameters only;
the actual mixed companion process is arbitrary and need not converge. -/
theorem canonical_energy (D:SmoothApproximation.ScalarData){h:ℝ}(hh:0<h)(hh1:h≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*h^(D.beta/4)≤1/2)
    (j:ℕ)(hP:P=ControlledSmoothLimit.smoothTotalParameters D hh hh1 hsmall j)
    {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(hvb':v<b)(hbH:b≤H)(k:ℕ)
    (hold:∀i,i<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 i)
    (A0 ν:ℝ)(hA:0≤A0)(hν:0≤ν)
    (hjet:∀x i,i≤k→∀z,‖iteratedFDeriv ℝ i (F x) z‖≤A0*ν^i)
    (B0:ℝ≥0)(hBDG:StandardTerminalBDGPower (k+2) J B0):
    Integrable (fun z:HeatCircle×Ω=>
      |MixedPastNewestIntegratedError.drift 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k 0
        (MixedPastNewestIntegratedError.coefficientError 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D j) z|^2)
      (haarAddCircle.prod μ) ∧
    (∫z:HeatCircle×Ω,
      |MixedPastNewestIntegratedError.drift 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k 0
        (MixedPastNewestIntegratedError.coefficientError 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D j) z|^2
      ∂haarAddCircle.prod μ)≤
      budget D (ControlledSmoothLimit.roughTotalParameters D hh hh1 hsmall) κ M v b B Hr k B0 A0 ν j:=by
  have he:=MixedPastNewestIntegratedError.coefficientError_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D j
  have hc:=MixedPastNewestIntegratedError.coefficientError_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D j
  have hb:=MixedPastNewestIntegratedError.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hB hHr hroot hrootmod hlocal hΛ hages hrootStop hrootTarget hspan hvb' hbH k hold
    A0 ν hA hν hjet B0 hBDG (ScalarApproximationDiscrepancy.scalarError D j)
    (ScalarApproximationDiscrepancy.scalarError_nonneg D j) _ he hc 0 (by norm_num)
  refine ⟨hb.2.1,hb.2.2.trans_eq ?_⟩
  rw [hP,NewestErrorConstants.canonical_output D hh hh1 hsmall]
  rfl

end SHE.MixedPastNewestApproximation
