module
public import SHE.InitialOrdinaryErrorOutput
public import SHE.NewestWindowBudget
public import SHE.InitialOrdinaryNewestActual
public import SHE.MixedOrdinaryErrorRootIdentity
public import SHE.MixedOrdinaryFiniteHilbertError
public import SHE.NativeBesselReparameter
public import SHE.NativeBesselFiniteSumEnergy
public import SHE.InitialOrdinaryNewestFibre
public import SHE.InitialOrdinaryNewestIntegration
public import SHE.RootSectionAverage
public import SHE.InitialOrdinaryNewestFields
public import SHE.InitialNativeKernelFibre
public import SHE.MixedNativePairInitial
public import SHE.MixedPastNewestOriginalMass
public import SHE.PhysicalWordErrorFields
public import SHE.MixedPastNewestOrdinaryError
public import SHE.InitialNativeKernelFields
public import SHE.InitialTerminalFields
public import SHE.MovingNativeFields
public import SHE.ZeroDirectionProfile
public import SHE.MixedPastNativeTimeFields
public import SHE.NativeRowTimeShift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.InitialOrdinaryErrorEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingNativeKernelFields_realSigma : MeasurableSpace RealL2 := borel _
local instance movingNativeKernelFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingNativeKernelFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingNativeKernelFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingNativeKernelFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingNativeKernelFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
attribute [local irreducible] GaussianConvolution.gaussianAverage ActualMeanKernel.cappedAverage
  GaussianTaylor.hessian WordRecursion.hessian UncutSmoothWords.test
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
open PastItoInputs PastItoAlgebra PhysicalProfile


local instance movingNativeKernelFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingNativeKernelFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance movingNativeKernelFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingNativeKernelFields_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "R"=>InitialNativeKernelFields.referenceData Λ u₀ P haP h
local notation "L"=>InitialTerminalLevel.level R F hF hFm
local notation "Root"=>InitialTerminalLevel.Root R

local notation "Mean"=>InitialNativeKernelFields.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Error"=>MixedPastNewestOrdinaryError.errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

local notation "BT" T:max=>InitialNativeKernelFibre.terminal Λ u₀ P haP h T
local notation "NB" T:max=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "K" T:max=>(NB T) (0,(embed u₀,0))
local notation "Lift" T:max=>InitialTerminalFields.lift R T
local notation "MA"=>InitialNativeKernelFibre.actualMean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Point"=>InitialOrdinaryNewestFields.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "CA" T:max=>MixedPastNewestOriginalMass.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "PA" T:max=>MixedPastNewestOriginalMass.primitive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
  (ControlledScalarReference.observations (BT T)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm

local notation "Primitive"=>InitialOrdinaryNewestFields.primitive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

local notation "ZZ" T:max=>ControlledScalarReference.observations (BT T)
local notation "Average"=>InitialOrdinaryNewestFields.average
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
local notation "Value"=>InitialOrdinaryErrorOutput.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hL hρ
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
local notation "G" T:max=>MixedOrdinaryRootFields.error
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs 0 0 (BT T) bot_le (ZZ T) (fun _=>rfl) (fun _=>rfl) F hF hFm
local notation "Disc" T:max=>MixedOrdinaryRootHilbertExpansion.discrepancy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs 0 0 (BT T) bot_le (ZZ T) (fun _=>rfl) (fun _=>rfl) F hF hFm hL hρ
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hsmall hIJ₀ hIJ₁ hnull hJ hAs in
/-- Uniform initial finite-error energy, with the original positive
ordinary errors retained and ONE original initial event before time. -/
theorem section_energy(hA:P.coefficient=(fun z=>κ+aV z))
    (D:SmoothApproximation.ScalarData){tau:ℝ}(htau:0<tau)(htau1:tau≤1)
    (hcontract:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*tau^(D.beta/4)≤1/2)
    (j:ℕ)(hP:P=ControlledSmoothLimit.smoothTotalParameters D htau htau1 hcontract j)
    (hU:aU=D.residualCoefficient)(hV:aV=D.smoothCoefficient j)
    {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hlocal:StandardTerminalPastLocality J)(hhH:h≤H)(h1:(h:ℝ)≤1)
    (hspan:(h:ℝ)≤P.horizon)(depth:ℕ)
    (hold:∀i,i<depth→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 i)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x i,i≤depth→∀z,‖iteratedFDeriv ℝ i (F x) z‖≤A0*ν^i)
    (B0:ℕ→ℝ≥0)(hBDG:∀k,k<depth→StandardTerminalBDGPower (k+2) J (B0 k))
    (T:Icc (R).base (R).horizon)(hT:0<BT T):
    Integrable (fun ω=>‖Value depth (T,ω)‖^2) μ ∧
      (∫ω,‖Value depth (T,ω)‖^2 ∂μ)≤
        Λ^(-ρ)*(ScalarApproximationDiscrepancy.scalarError D j)^2*
          MixedPastNewestFiniteError.constant
            (ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract) κ M 0 1 B Hr depth B0 A0 ν:=by
  have he:∀ᵐω∂μ,Value depth (T,ω)=∑k∈Finset.range depth,(Disc T) k ω:=by
    filter_upwards [InitialOrdinaryErrorOutput.value_all_parameters_ae
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
      hL hρ J hIJ₀ hIJ₁ hnull hJ hAs hsmall hA] with ω hω
    exact hω T depth
  have hTh:BT T≤h:=T.2.2
  have hThR:((BT T):ℝ)≤(h:ℝ):=by exact_mod_cast hTh
  have hc:=MixedOrdinaryFiniteHilbertError.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P haP hAs 0 (BT T) bot_le (ZZ T) (fun _=>rfl) (fun _=>rfl) F hF hFm hsmall hL hρ
    hA D htau htau1 hcontract j hP hU hV hB hHr hroot hrootmod hlocal
    (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans hspan) hT (hTh.trans hhH) depth
    (fun i hi=>by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans (hold i hi))
    A0 ν hA0 hν hjet B0 hBDG
  have hm:=NewestWindowBudget.finite_constant_le_one
    (ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract) κ M 0 (BT T) bot_le
    (by simpa only [NNReal.coe_zero,sub_zero] using hThR.trans h1) hB hHr hA0 depth B0 ν
  have hs:∀ᵐω∂μ,‖Value depth (T,ω)‖^2=‖∑k∈Finset.range depth,(Disc T) k ω‖^2:=
    he.mono (fun _ hx=>by rw [hx])
  refine ⟨hc.1.congr (hs.mono (fun _ hx=>hx.symm)),?_⟩
  rw [integral_congr_ae hs]
  exact hc.2.trans (mul_le_mul_of_nonneg_left hm
    (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hL) _) (sq_nonneg _)))
end SHE.InitialOrdinaryErrorEnergy
