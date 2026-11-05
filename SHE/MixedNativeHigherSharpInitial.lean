module
public import SHE.MixedNativeHigherInitialOutput
public import SHE.MixedNativeInitialEnvelopeRate
public import SHE.NativeOriginalOutputParameter
public import SHE.InitialNativePredictableAverages
public import SHE.MixedNativeHigherInitialCap
public import SHE.NativeCurrentWindowMeasure
public import SHE.InitialNativeAverageActual
public import SHE.InitialNativeColumnActual
public import SHE.InitialNativeOldCube
public import SHE.InitialNativeColumnAverages
public import SHE.MixedPastNativeCompleteColumns
public import SHE.InitialNativeColumns
public import SHE.MixedPastNativeKernelSemigroup
public import SHE.MixedPastNativeOldTimeEnergy
public import SHE.MixedPastSignedEndpointFields
public import SHE.NativeKernelCongruence
public import SHE.MixedNativePairInitial
public import SHE.ControlledScalarReference
public import SHE.WordRootState
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
namespace SHE.MixedNativeHigherSharpInitial
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeHigherSharpInitial_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeHigherSharpInitial_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeHigherSharpInitial_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeHigherSharpInitial_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeHigherSharpInitial_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeHigherSharpInitial_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedNativeHigherSharpInitial_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeHigherSharpInitial_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedNativeHigherSharpInitial_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeHigherSharpInitial_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "R"=>InitialNativeKernelFields.referenceData Λ u₀ P haP h
local notation "BT" T:max=>InitialNativeKernelFibre.terminal Λ u₀ P haP h T
local notation "ZZ" T:max=>ControlledScalarReference.observations (BT T)
local notation "LeftA" T:max=>MixedPastNativeCompleteColumns.left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (BT T) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "RightA" T:max=>MixedPastNativeCompleteColumns.right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  0 (BT T) bot_le (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Left"=>InitialNativeColumnAverages.left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Right"=>InitialNativeColumnAverages.right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
local instance mixedNativeHigherSharpInitial_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance mixedNativeHigherSharpInitial_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩

local notation "TT" t:max=>(show Icc (R).base (R).horizon from InitialRetainedTriangleEnergy.clippedTime h (t:ℝ))
local notation "Output"=>MixedNativeHigherInitialEnergy.output
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
  J hIJ₀ hIJ₁ hnull hJ hAs
local notation "Row"=>InitialNativePredictableAverages.row
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Source0" T:max=>MixedNativeOriginalFourierRows.left
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
  (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Source1" T:max=>MixedNativeOriginalFourierRows.right
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 (BT T) bot_le
  (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm

variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Pzero"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall 0
local notation "scoreFloor"=>ControlledOldIntervals.fraction Pzero*(Pzero).lower
local notation "Cs"=>PhysicalScoreChain.uniformConstant 1
variable (k:ℕ)(hk:0<k)
variable (ρ χ η ε tail ζ:ℝ)(hρ:0<ρ)(hχ0:0≤χ)(hχ1:χ<1)(hm:χ<D.beta+2*ρ)
    (hα:0<ρ+η)(hαhalf:ρ+η<1/2)(hζ:0<ζ)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Cc"=>NativeCanonicalFrequency.currentCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm ζ hζ
local notation "Cp"=>NativeCanonicalFrequency.pastCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm ζ hζ
local notation "Ci"=>NativeCanonicalFrequency.initialCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm ζ hζ
local notation "Cg"=>NativeCanonicalFrequency.goodCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ η ε tail ζ hα hαhalf hζ
local notation "Cb"=>NativeCanonicalFrequency.badCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ η ε tail ζ hα hαhalf hζ
local notation "qc"=>NativeBandFrequencyRates.currentDegree D.beta ρ χ ζ
local notation "qp"=>NativeBandFrequencyRates.pastDegree D.beta ζ
local notation "qg"=>SignedNativeBandFrequency.goodDegree D.beta ε ζ
local notation "qb"=>SignedNativeBandFrequency.badDegree D.beta tail ζ

local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

include haP hIJ₀ hIJ₁ hnull hJ hρ hχ0 hχ1 hm hα hαhalf hζ in
theorem exists_initial(hA:P.coefficient=(fun z=>κ+aV z))
    (hlocal:StandardTerminalPastLocality J)(hL:1≤Λ)(hρhalf:ρ<1/2)
    (hhH:h≤H)(hH:(H:ℝ)≤1)
    (hsmallProfile:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hspan:(h:ℝ)≤P.horizon)
    (hspanF:(h:ℝ)≤NativeUniversalConstants.rowHorizon (1+k))
    (hspanC:(h:ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega))
    (hspanS:(h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hHistory:∀j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)
    (n:ℕ)(ν:ℝ)(hν:1≤ν)(hP:P=Smooth n)
    (hwindow:(h:ℝ)=NativeBandFrequencyRates.window D.beta ν)
    (A:ℝ)(hA0:0≤A)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤(A*ν^(-D.beta))*ν^j)
    (p:ℕ)(hp:0<p)(Bcur:ℝ≥0)(hBDGcur:StandardTerminalBDGPower (p*(k+2)) J Bcur)
    (Bword:ℝ≥0)(hBDGword:StandardTerminalBDGPower (k+2) J Bword)
    (horder:1≤(p:ℝ)*(1-χ))(htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)
    (hFubini:StandardItoParameterFubini J):
    let Cf:=NativeUniversalConstants.rowConstant (1+k)
    let Cdim:=NativeUniversalConstants.currentConstant.{0} (1+k) (by omega)
    let C:=MixedPastNativeQuarterRMS.coefficient κ (M:=M) Pzero k Cf ρ
    let Ccur:=Real.sqrt (8*C*MixedPastNativeEnergyNormalization.currentCoefficient κ (M:=M) Pzero k p χ Cdim Bcur)
    let Jt:=MixedPastSignedEndpointMoments.traceConstant (Ω:=Ω) (M:=M) hell ρ hρ hρhalf
    let Cmom:=MixedPastWordMoments.momentConstant Pzero k k p
      ((k:ℝ)*(NativeHybridMoments.momentConstant (p*(k+2)) Bcur κ M)^(Pzero).exponent)
    let Cgood:=PastSignedEndpointTime.goodCoefficient Pzero k Jt ρ η
    let Cbad:=PastSignedEndpointTime.badCoefficient Pzero k M Cmom
    ∃I:ℝ≥0×Ω→CircleL2,Measurable I ∧
      (∀ᵐt∂timeMeasure h,(fun ω=>I (t,ω))=ᵐ[μ]
        (fun ω=>MixedNativeHigherInitialOutput.output
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
          J hIJ₀ hIJ₁ hnull hJ hAs hL hρ.le k (t,ω))) ∧
      (∫⁻t,∫⁻ω,ENNReal.ofReal (‖I (t,ω)‖^2) ∂μ ∂timeMeasure h)≤
      ENNReal.ofReal (8*A^2*Ccur^2)*ENNReal.ofReal (Ci*ν^(-qc))*
        (ENNReal.ofReal Global^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))+
      ENNReal.ofReal (4*A^2*Cgood^2)*ENNReal.ofReal (Cg*ν^(-qg))*Neg ρ+
      ENNReal.ofReal (4*A^2*Cbad^2)*ENNReal.ofReal (Cb*ν^(-qb))*ENNReal.ofReal (H:ℝ):=by
  intro Cf Cdim C Ccur Jt Cmom Cgood Cbad
  let Cap:ℝ≥0∞:=
      ENNReal.ofReal (8*A^2*Ccur^2)*ENNReal.ofReal (Ci*ν^(-qc))*
        (ENNReal.ofReal Global^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))+
      ENNReal.ofReal (4*A^2*Cgood^2)*ENNReal.ofReal (Cg*ν^(-qg))*Neg ρ+
      ENNReal.ofReal (4*A^2*Cbad^2)*ENNReal.ofReal (Cb*ν^(-qb))*ENNReal.ofReal (H:ℝ)
  have hamp:0≤A*ν^(-D.beta):=mul_nonneg hA0 (Real.rpow_nonneg (zero_le_one.trans hν) _)
  have hmin:min (H:ℝ) (h:ℝ)=(h:ℝ):=min_eq_right (by exact_mod_cast hhH)
  have hc:=MixedNativeHigherInitialCap.iterated
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
    J hIJ₀ hIJ₁ hnull hJ hAs hA hlocal hL hρ hρhalf hhH hH k
    hsmallProfile hsmallL2 hspan hspanF hspanC hspanS hHistory B1 hBDG1
    (A*ν^(-D.beta)) ν hamp (zero_le_one.trans hν) hjet
    p hp Bcur hBDGcur Bword hBDGword χ hχ0 hχ1 horder
    ν ε tail η hν htail hη (by linarith)
  rw [hmin] at hc
  have hr:=MixedNativeInitialEnvelopeRate.initial
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    D hT hT1 hsmall k hk ρ χ η ε tail ζ hρ hχ0 hχ1 hm hα hαhalf hζ
    hL hρhalf hH B1 hBDG1 n ν hν A p Bcur Bword
  have hr':
      (∫⁻t in Ioc (0:ℝ) (h:ℝ),∫⁻q in Ioc (0:ℝ) t,ENNReal.ofReal
        (MovingNativeFourTermEnergy.envelope
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P 0 t.toNNReal q.toNNReal k
          (A*ν^(-D.beta)) ν Λ ρ χ ν ε tail η hL hρ hρhalf p Bcur Bword))≤Cap:=by
    rw [hP]
    simpa only [←hwindow,hmin] using hr
  have he:=hc.trans hr'
  have hNeg:Neg ρ≠∞:=ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (MixedActualEnergyBridge.negative_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (zero_lt_one.trans_le hL) hρ.le)
  have hpowG:ENNReal.ofReal Global^χ≠∞:=ENNReal.rpow_ne_top_of_nonneg hχ0 ENNReal.ofReal_ne_top
  have hpowH:(ENNReal.ofReal (H:ℝ))^(1-χ)≠∞:=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  have hCap:Cap<∞:=by
    apply lt_top_iff_ne_top.mpr
    dsimp only [Cap]
    finiteness
  have hfinite:
      (∫⁻t,∫⁻ω,ENNReal.ofReal (‖MixedNativeHigherInitialOutput.output
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
        J hIJ₀ hIJ₁ hnull hJ hAs hL hρ.le k (t,ω)‖^2) ∂μ ∂timeMeasure h)<∞:=by
    rw [MixedNativeHigherInitialOutput.mass_eq]
    exact he.trans_lt hCap
  obtain ⟨I,hI,hIa,hEq⟩:=MixedNativeHigherInitialOutput.exists_identified
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
    J hIJ₀ hIJ₁ hnull hJ hAs hA hlocal hL hρ hρhalf hhH hH k
    hsmallProfile hsmallL2 hspan hspanF hspanC hspanS hHistory B1 hBDG1
    (A*ν^(-D.beta)) ν hamp (zero_le_one.trans hν) hjet
    p hp Bcur hBDGcur Bword hBDGword χ hχ0 hχ1 horder
    ν ε tail η hν htail hη (by linarith) (timeMeasure h) hFubini hfinite
  refine ⟨I,hI,hIa,?_⟩
  rw [hEq,MixedNativeHigherInitialOutput.mass_eq]
  exact he

end SHE.MixedNativeHigherSharpInitial

