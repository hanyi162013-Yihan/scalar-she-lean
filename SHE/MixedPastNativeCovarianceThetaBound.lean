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
@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeCovarianceThetaBound
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


local notation "Point"=>MixedPastNativeCovariance.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mass"=>MixedPastNativeThetaRMSFields.mass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastNativeCovariance.point MixedPastNativeThetaRMSFields.mass
  MixedPastWordMoments.total MixedPastJointData.pastU MixedPastJointData.pastD

include hIJ₀ hIJ₁ in
/-- Genuine sample-L2 interpolation integral of the actual native
covariance mark. Its correlated score mass is averaged in theta BEFORE
output squaring. No division by a sharp time factor is used. -/
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
      let σ:=fun i=>stops Zero k h i-(v:ℝ)
      let target:=fun i=>targets Zero k h i-(v:ℝ)
      let lo:=fun j=>lower Zero k h j-(v:ℝ)
      let hi:=fun j=>upper Zero k h j-(v:ℝ)
      ∀E:WordRecursion.State (n+k),
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (NativeFirstScoreReserve.covariance P σ target (centers Zero k h) ((q:ℝ)-(v:ℝ)))).range→
      let oldEnvelope:=timeWeight Zero (fraction P*P.lower) (uniformConstant n) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero hages k h hp) (centers Zero k h)
      let sharp:=MixedPastWordMoments.total (d:=n) P lo hi
        (fun j=>target (leafIndex k (fun i=>i) j)) A0 ν
      let C:=TwoFreshCompleteWord.momentConstant P k k 1
        ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
      let K:=oldEnvelope*Real.sqrt (scoreVariance
        (NativeFirstScoreReserve.covariance P σ target (centers Zero k h) ((q:ℝ)-(v:ℝ))) E)*sharp/2
      let T:=fun θ:ℝ=>Real.sqrt (∫ω,|Mass k θ q h ω|^2 ∂μ)
      Integrable T MeanThetaAverage.thetaMeasure→
      Integrable (fun z:ℝ×Ω=>Point k z.1 q h E z.2) (MeanThetaAverage.thetaMeasure.prod μ) ∧
      MemLp (fun ω=>∫θ,Point k θ q h E ω ∂MeanThetaAverage.thetaMeasure) 2 μ ∧
      normTwo μ (fun ω=>∫θ,Point k θ q h E ω ∂MeanThetaAverage.thetaMeasure)≤
        Real.sqrt C*K*(∫θ,T θ ∂MeanThetaAverage.thetaMeasure):=by
  filter_upwards [MixedPastNativeCovariance.actual_even_energy_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallPoint hvH hv1 Bpast hBDGpast
    hages hspan ρ k] with h hmom
  intro q hvq hqH hqt hp hs A0 ν hA0 hν hjet B0 hBDG σ target lo hi E hE oldEnvelope sharp C K T hTi
  have hOld:0≤oldEnvelope:=mul_nonneg
    (timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant n)
      (fun j=>(uniformConstant_pos n j).le) k h hp)
    (OrderedHeatForests.parentDensity_nonneg 2 (by norm_num) k _ _ _)
  have hSharp:0≤sharp:=MixedPastWordMoments.total_nonneg P lo hi _ A0 ν
  have hK:0≤K:=div_nonneg
    (mul_nonneg (mul_nonneg hOld (Real.sqrt_nonneg _)) hSharp) (by norm_num)
  have hC:0≤C:=TwoFreshCompleteWord.momentConstant_nonneg P k k 1 _
  have hTm:=MixedPastNativeThetaRMSFields.mass_rms_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint k q h
  have hpm:=MixedPastNativeMarkThetaFields.point_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint k q h E
  have hm:∀ᵐθ∂MeanThetaAverage.thetaMeasure,
      Integrable (fun ω=>|Point k θ q h E ω|^2) μ ∧
      (∫ω,|Point k θ q h E ω|^2 ∂μ)≤C*(K*T θ)^2:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have hθabs:|θ|≤1:=by rw [abs_of_nonneg hθ.1.le];exact hθ.2
    have hh:=hmom q hvq hqH hqt hp hs θ hθabs A0 ν hA0 hν hjet B0 hBDG E hE
    have hsq:(T θ)^2=∫ω,(Mass k θ q h ω)^2 ∂μ:=by
      dsimp only [T]
      rw [Real.sq_sqrt (integral_nonneg (fun _=>sq_nonneg _))]
      simp only [sq_abs]
    refine ⟨hh.1,?_⟩
    rw [mul_pow,hsq]
    convert! hh.2 using 1
    simp only [MixedPastNativeThetaRMSFields.mass,C,K,oldEnvelope,sharp,σ,target,lo,hi,mul_assoc]
  exact ScalarThetaMinkowski.scaled_moment μ MeanThetaAverage.thetaMeasure
    _ hpm T hTm hTi (fun _=>Real.sqrt_nonneg _) C K hC hK hm

end SHE.MixedPastNativeCovarianceThetaBound
