module
public import SHE.MovingOrdinaryErrorOutput
public import SHE.MovingOrdinaryNewestCurrent
public import SHE.MixedOrdinaryErrorRootIdentity
public import SHE.MixedOrdinaryFiniteHilbertError
public import SHE.NewestWindowBudget
public import SHE.NativeBesselReparameter
public import SHE.NativeBesselFiniteSumEnergy
public import SHE.MixedNativeHigherMovingEnergy
public import SHE.MovingOrdinaryNewestTranslation
public import SHE.MovingClockEnergy
public import SHE.NativeHessianTimeShift
public import SHE.MovingOrdinaryNewestFields
public import SHE.MovingNativePointTranslation
public import SHE.ShiftedOldTimeMeasure
public import SHE.MixedPastNewestOriginalMass
public import SHE.MixedPastNewestOrdinaryError
public import SHE.ControlledThetaBackwardFields
public import SHE.PhysicalWordErrorFields
public import SHE.MovingNativeKernelFields
public import SHE.MovingNativeFields
public import SHE.MixedPastNativeTimeFields
public import SHE.NativeRowTimeShift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MovingOrdinaryErrorEnergy
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
variable (h:ℝ≥0)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledWordTimeShift.relativeLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Past" v:max ω:max=>(embed (S.first v ω),embed (S.second v ω-S.first v ω))

local notation "Mean"=>MovingNativeKernelFields.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Error"=>MixedPastNewestOrdinaryError.errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

local notation "Abs"=>ControlledWordTimeShift.absoluteLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v:max=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v:max=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v:max=>ControlledWordTimeShift.translatedStops h Z hstop v
local notation "MA"=>MovingNativePointTranslation.absoluteMean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Point"=>MovingOrdinaryNewestFields.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Primitive"=>MovingOrdinaryNewestFields.primitive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "CA" v:max=>MixedPastNewestOriginalMass.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v (v+h) le_self_add
    (ZT v) (HT v) (HS v) F hF hFm
local notation "PA" v:max=>MixedPastNewestOriginalMass.primitive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v (v+h) le_self_add
    (ZT v) (HT v) (HS v) F hF hFm

local notation "Average"=>MovingOrdinaryNewestFields.average
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
local notation "Value"=>MovingOrdinaryErrorOutput.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hL hρ

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
variable (hrootStop:∀x,(Z.observations x 0).stop=(h:ℝ))
variable (hrootTarget:∀x,(Z.observations x 0).target=(h:ℝ))
local notation "RS" v:max=>MixedNativeHigherMovingEnergy.rootStop h Z hrootStop v
local notation "RT" v:max=>MixedNativeHigherMovingEnergy.rootTarget h Z hrootTarget v
local notation "G" v:max=>MixedOrdinaryRootFields.error
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs 0 v (v+h) le_self_add (ZT v) (RS v) (RT v) F hF hFm
local notation "Disc" v:max=>MixedOrdinaryRootHilbertExpansion.discrepancy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs 0 v (v+h) le_self_add (ZT v) (RS v) (RT v) F hF hFm hL hρ
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hsmall hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget in
/-- The genuine moving ordinary finite discrepancy field has the
canonical error cap with one constant before output time and smoothing. -/
theorem section_energy(hA:P.coefficient=(fun z=>κ+aV z))
    (D:SmoothApproximation.ScalarData){tau:ℝ}(htau:0<tau)(htau1:tau≤1)
    (hcontract:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*tau^(D.beta/4)≤1/2)
    (j:ℕ)(hP:P=ControlledSmoothLimit.smoothTotalParameters D htau htau1 hcontract j)
    (hU:aU=D.residualCoefficient)(hV:aV=D.smoothCoefficient j)
    {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hlocal:StandardTerminalPastLocality J)(hpos:0<h)(h1:(h:ℝ)≤1)
    (hcenter:∀x,(Z.observations x 0).center=x)
    (hspan:(h:ℝ)≤P.horizon)(v:ℝ≥0)(hvhH:v+h≤H)(depth:ℕ)
    (hold:∀i,i<depth→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 i)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x i,i≤depth→∀z,‖iteratedFDeriv ℝ i (F x) z‖≤A0*ν^i)
    (B0:ℕ→ℝ≥0)(hBDG:∀k,k<depth→StandardTerminalBDGPower (k+2) J (B0 k)):
    Integrable (fun ω=>‖Value depth (v,ω)‖^2) μ ∧
      (∫ω,‖Value depth (v,ω)‖^2 ∂μ)≤
        Λ^(-ρ)*(ScalarApproximationDiscrepancy.scalarError D j)^2*
          MixedPastNewestFiniteError.constant
            (ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract) κ M 0 1 B Hr depth B0 A0 ν:=by
  have he:∀ω,Value depth (v,ω)=∑k∈Finset.range depth,(Disc v) k ω:=
    MovingOrdinaryErrorOutput.value_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
      hL hρ J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hsmall hA v depth
  have hsp:((v+h:ℝ≥0):ℝ)-(v:ℝ)=(h:ℝ):=by simp only [NNReal.coe_add];ring
  have hc:=MixedOrdinaryFiniteHilbertError.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P haP hAs v (v+h) le_self_add (ZT v) (RS v) (RT v) F hF hFm hsmall hL hρ
    hA D htau htau1 hcontract j hP hU hV hB hHr hroot hrootmod hlocal
    (by simpa only [hsp] using hspan) (lt_add_of_pos_right v hpos) hvhH depth
    (fun i hi=>by simpa only [hsp] using hold i hi) A0 ν hA0 hν hjet B0 hBDG
  have hm:=NewestWindowBudget.finite_constant_le_one
    (ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract) κ M v (v+h) le_self_add
    (by simpa only [hsp] using h1) hB hHr hA0 depth B0 ν
  simp_rw [he]
  exact ⟨hc.1,hc.2.trans (mul_le_mul_of_nonneg_left hm
    (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hL) _) (sq_nonneg _)))⟩
end SHE.MovingOrdinaryErrorEnergy
