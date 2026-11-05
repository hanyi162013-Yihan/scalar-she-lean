module
public import SHE.NativeConditionalThetaFields
public import SHE.MixedPastNativeOmitted
public import SHE.MixedPastLiteralFields
public import SHE.MixedPastNativeCovariance
public import SHE.NativeReserveRowEnvelope

public import SHE.MixedPastTwoFreshCovarianceInput
public import SHE.NativeResidualInputApplicability
public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastProfileDerivative
public import SHE.ControlledThetaNativeCovariance
public import SHE.ActualCovarianceMarkFields
public import SHE.MixedPastCovarianceMass
public import SHE.ControlledThetaRelativeCovarianceMark
public import SHE.MixedPastLiteralPoint
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

public import SHE.MixedPastNativeThetaRMSFields
public import SHE.ScalarThetaMinkowski
public import SHE.MeanThetaAverage
public import SHE.MixedPastNativeCovarianceThetaBound
public import SHE.MixedPastNativeBaselineThetaBound
public import SHE.ScalarFiniteThetaResidual
@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeResidualThetaBound
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralCovariance_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralCovariance_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralCovariance_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralCovariance_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralCovariance_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralCovariance_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastLiteralCovariance_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralCovariance_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open scoped BigOperators
local instance mixedPastLiteralCovariance_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v



local notation "Cov"=>MixedPastNativeCovariance.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Leaf"=>MixedPastOmittedMarkFields.leafInput
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "BaseLeaf"=>MixedPastNativeBaselineLeaf.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mass"=>MixedPastNativeThetaRMSFields.mass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- The physical A residual before its interpolation integral. -/
def residual (k:ℕ)(q:ℝ≥0)(h:History X k)(E:WordRecursion.State (n+k))(z:ℝ×Ω):ℝ:=
  Cov k z.1 q h E z.2-∑j:Fin k,BaseLeaf k z.1 q h E j z.2

/-- The actual additive past amplitude. It is never multiplied by a
current damping score, and no sharp factor is divided out. -/
def amplitude (k:ℕ)(q:ℝ≥0)(h:History X k)(A0 ν:ℝ)(B0:ℝ≥0):ℝ:=
  let lo:=fun j=>lower Zero k h j-(v:ℝ)
  let hi:=fun j=>upper Zero k h j-(v:ℝ)
  let age:=fun j=>targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ)
  let C0:=(k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent
  Real.sqrt (TwoFreshCompleteWord.momentConstant P k k 1 C0)*
    (MixedPastWordMoments.total (d:=n) P lo hi age A0 ν/2)*
      (∫θ,Real.sqrt (∫ω,|Mass k θ q h ω|^2 ∂μ) ∂MeanThetaAverage.thetaMeasure)+
    ∑j:Fin k,Real.sqrt (NativeOmittedCompleteWord.momentConstant P k k j 1 C0)*
      NativeOmittedTimeTotal.total (d:=n) P lo hi age j A0 ν*
        (∫θ,Real.sqrt (∫ω,|Leaf k θ h j ω|^2 ∂μ) ∂MeanThetaAverage.thetaMeasure)

local notation "Res"=>residual
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Amp"=>amplitude
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastNativeCovariance.point MixedPastNativeBaselineLeaf.value
  MixedPastNativeThetaRMSFields.mass MixedPastOmittedMarkFields.leafInput
  MixedPastWordMoments.total NativeOmittedTimeTotal.total

include hIJ₀ hIJ₁ in
/-- The COMPLETE actual A residual has a sample-L2 interpolation
integral, with the original old forest and native first-score norm paid
once. The two genuine RMS theta integrability inputs are discharged on
AE outputs by MixedPastNativeThetaSections and LeafThetaSections. -/
theorem actual_bound_ae (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hsmallPoint:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH:v≤H)(hv1:(v:ℝ)≤1)(Bpast:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(ρ:Measure X)[IsFiniteMeasure ρ](k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k,
      ∀q:ℝ≥0,v≤q→q≤H→(q:ℝ)<(carrier Zero k).terminal h→
      ∀hp:StrictHistory Zero k h,SmallHistory Zero (uniformHorizon n) k h→
      ∀A0 ν:ℝ,0≤A0→0≤ν→
      (∀j,j≤k→∀z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j)→
      ∀B0:ℝ≥0,StandardTerminalBDGPower (k+2) J B0→
      ∀E:WordRecursion.State (n+k),
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ))
        (centers Zero k h) ((q:ℝ)-(v:ℝ)))).range→
      Integrable (fun θ=>Real.sqrt (∫ω,|Mass k θ q h ω|^2 ∂μ)) MeanThetaAverage.thetaMeasure→
      (∀j:Fin k,Integrable (fun θ=>Real.sqrt (∫ω,|Leaf k θ h j ω|^2 ∂μ)) MeanThetaAverage.thetaMeasure)→
      let oldEnvelope:=timeWeight Zero (fraction P*P.lower) (uniformConstant n) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero hages k h hp) (centers Zero k h)
      let R:=NativeFirstScoreReserve.covariance P
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ))
        (centers Zero k h) ((q:ℝ)-(v:ℝ))
      Integrable (Res k q h E) (MeanThetaAverage.thetaMeasure.prod μ) ∧
      MemLp (fun ω=>∫θ,Res k q h E (θ,ω) ∂MeanThetaAverage.thetaMeasure) 2 μ ∧
      normTwo μ (fun ω=>∫θ,Res k q h E (θ,ω) ∂MeanThetaAverage.thetaMeasure)≤
        oldEnvelope*Real.sqrt (scoreVariance R E)*Amp k q h A0 ν B0:=by
  filter_upwards [MixedPastNativeCovarianceThetaBound.actual_bound_ae
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
      P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallPoint hvH hv1 Bpast hBDGpast hages hspan ρ k,
    MixedPastNativeBaselineThetaBound.actual_bound_ae
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
      P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallPoint hvH hv1 Bpast hBDGpast hages hspan ρ k]
      with h hcov hbase
  intro q hvq hqH hqt hp hs A0 ν hA0 hν hjet B0 hBDG E hE hCi hBi oldEnvelope R
  have hc:=hcov q hvq hqH hqt hp hs A0 ν hA0 hν hjet B0 hBDG E hE hCi
  have hb:=fun j:Fin k=>hbase q hvq hqH hqt hp hs A0 ν hA0 hν hjet E hE j B0 hBDG (hBi j)
  have hh:=ScalarFiniteThetaResidual.bound μ MeanThetaAverage.thetaMeasure
    (fun z:ℝ×Ω=>Cov k z.1 q h E z.2) (fun j z=>BaseLeaf k z.1 q h E j z.2)
    hc.1 (fun j=>(hb j).1) hc.2.1 (fun j=>(hb j).2.1) _ _ hc.2.2 (fun j=>(hb j).2.2)
  refine ⟨hh.1,hh.2.1,hh.2.2.trans_eq ?_⟩
  simp only [amplitude,mul_add,Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

end SHE.MixedPastNativeResidualThetaBound
