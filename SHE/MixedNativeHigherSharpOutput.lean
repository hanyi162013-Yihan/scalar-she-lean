module
public import SHE.MixedNativeHigherMovingRate
public import SHE.MixedNativeMovingEnvelopeRate
public import SHE.MixedNativeHigherMovingOutput
public import SHE.NativeOriginalOutputParameter
public import SHE.MovingNativePredictableAverages
public import SHE.MixedNativeHigherMovingEnergy
public import SHE.NativeCurrentWindowMeasure
public import SHE.MovingNativeAverageTranslation
public import SHE.MovingNativeColumnTranslation
public import SHE.MovingNativeColumnAverages
public import SHE.MixedPastNativeCompleteColumns
public import SHE.ShiftedOldTimeMeasure
public import SHE.MovingNativeColumns
public import SHE.MixedPastNativeOldTimeEnergy
public import SHE.MixedPastSignedEndpointFields
public import SHE.NativeKernelCongruence
public import SHE.ShiftedPhysicalArrays
public import SHE.NativeRowTimeShift
public import SHE.MovingNativeSpatialKernel
public import SHE.ControlledMeanSpatialShift
public import SHE.MixedPastNativeKernelSemigroup

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MixedNativeHigherSharpOutput
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeHigherSharpOutput_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeHigherSharpOutput_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeHigherSharpOutput_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeHigherSharpOutput_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeHigherSharpOutput_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeHigherSharpOutput_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedNativeHigherSharpOutput_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeHigherSharpOutput_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedNativeHigherSharpOutput_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeHigherSharpOutput_nativeSecond:SecondCountableTopology CircleL2:=
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

local notation "Abs"=>ControlledWordTimeShift.absoluteLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v:max=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v:max=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v:max=>ControlledWordTimeShift.translatedStops h Z hstop v
local notation "Mean"=>MovingNativeKernelFields.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

local notation "LeftA" v:max=>MixedPastNativeCompleteColumns.left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm
local notation "RightA" v:max=>MixedPastNativeCompleteColumns.right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm
local notation "Left"=>MovingNativeColumnAverages.left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Right"=>MovingNativeColumnAverages.right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
variable (hrootStop:∀x,(Z.observations x 0).stop=(h:ℝ))
variable (hrootTarget:∀x,(Z.observations x 0).target=(h:ℝ))

local instance mixedNativeHigherSharpOutput_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance mixedNativeHigherSharpOutput_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩

local notation "Output"=>MixedNativeHigherMovingEnergy.output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P h Z F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget

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

include haP htarget hstop hIJ₀ hIJ₁ hnull hJ hrootStop hrootTarget
  hρ hχ0 hχ1 hm hα hαhalf hζ in
/-- The literal higher original-J output has the four sharp frequency
rates. The coefficients are chosen from the common numerical profile
before the smooth companion index. No output-version premise occurs. -/
theorem exists_completed(hA:P.coefficient=(fun z=>κ+aV z))
    (hlocal:StandardTerminalPastLocality J)(hL:1≤Λ)(hρhalf:ρ<1/2)
    (hpos:0<h)(hH:(H:ℝ)≤1)
    (hsmallProfile:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hcenter:∀x,(Z.observations x 0).center=x)
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
    (hhH:h≤H)(hFubini:StandardItoParameterFubini J):
    let Cf:=NativeUniversalConstants.rowConstant (1+k)
    let Cdim:=NativeUniversalConstants.currentConstant.{0} (1+k) (by omega)
    let C:=MixedPastNativeQuarterRMS.coefficient κ (M:=M) Pzero k Cf ρ
    let Ccur:=Real.sqrt (8*C*MixedPastNativeEnergyNormalization.currentCoefficient κ (M:=M) Pzero k p χ Cdim Bcur)
    let Cpast:=Real.sqrt (2*C*MixedPastNativeEnergyNormalization.pastCoefficient κ (M:=M) Pzero k Bword)
    let Jt:=MixedPastSignedEndpointMoments.traceConstant (Ω:=Ω) (M:=M) hell ρ hρ hρhalf
    let Cmom:=MixedPastWordMoments.momentConstant Pzero k k p
      ((k:ℝ)*(NativeHybridMoments.momentConstant (p*(k+2)) Bcur κ M)^(Pzero).exponent)
    let Cgood:=PastSignedEndpointTime.goodCoefficient Pzero k Jt ρ η
    let Cbad:=PastSignedEndpointTime.badCoefficient Pzero k M Cmom
    ∃Y:ℝ≥0×Ω→CircleL2,Measurable Y ∧
      (∀ᵐv∂timeMeasure (H-h),(fun ω=>Y (v,ω))=ᵐ[μ]
        (fun ω=>MixedNativeHigherMovingOutput.output
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P h Z F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hL hρ.le k (v,ω))) ∧
      (∫⁻v,∫⁻ω,ENNReal.ofReal (‖Y (v,ω)‖^2) ∂μ ∂timeMeasure (H-h))≤
    ENNReal.ofReal (8*A^2*Ccur^2)*ENNReal.ofReal (Cc*ν^(-qc))*
      (ENNReal.ofReal Global^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))+
    ENNReal.ofReal (8*A^2*Cpast^2)*ENNReal.ofReal (Cp*ν^(-qp))*ENNReal.ofReal Global+
    ENNReal.ofReal (4*A^2*Cgood^2)*ENNReal.ofReal (Cg*ν^(-qg))*Neg ρ+
    ENNReal.ofReal (4*A^2*Cbad^2)*ENNReal.ofReal (Cb*ν^(-qb))*ENNReal.ofReal (H:ℝ):=by
  intro Cf Cdim C Ccur Cpast Jt Cmom Cgood Cbad
  let Cap:ℝ≥0∞:=
    ENNReal.ofReal (8*A^2*Ccur^2)*ENNReal.ofReal (Cc*ν^(-qc))*
      (ENNReal.ofReal Global^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))+
    ENNReal.ofReal (8*A^2*Cpast^2)*ENNReal.ofReal (Cp*ν^(-qp))*ENNReal.ofReal Global+
    ENNReal.ofReal (4*A^2*Cgood^2)*ENNReal.ofReal (Cg*ν^(-qg))*Neg ρ+
    ENNReal.ofReal (4*A^2*Cbad^2)*ENNReal.ofReal (Cb*ν^(-qb))*ENNReal.ofReal (H:ℝ)
  have he:(∫⁻v in Ioc (0:ℝ) ((H:ℝ)-(h:ℝ)),∫⁻ω,
      ENNReal.ofReal (‖Output hL hρ.le k v.toNNReal ω‖^2) ∂μ)≤Cap:=by
    exact MixedNativeHigherMovingRate.energy
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
      J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget
      D hT hT1 hsmall k hk ρ χ η ε tail ζ hρ hχ0 hχ1 hm hα hαhalf hζ
      hA hlocal hL hρhalf hpos hH hsmallProfile hsmallL2 hcenter
      hspan hspanF hspanC hspanS hHistory B1 hBDG1 n ν hν hP hwindow
      A hA0 hjet p hp Bcur hBDGcur Bword hBDGword horder htail hη
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
      (∫⁻v,∫⁻ω,ENNReal.ofReal (‖MixedNativeHigherMovingOutput.output
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h Z F hF hFm
        J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hL hρ.le k (v,ω)‖^2)
        ∂μ ∂timeMeasure (H-h))<∞:=by
    rw [MixedNativeHigherMovingOutput.mass_eq]
    · exact he.trans_lt hCap
    · exact hhH
  obtain ⟨Y,hY,hYa,hEq⟩:=MixedNativeHigherMovingOutput.exists_identified
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
    J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget
    hA hlocal hL hρ hρhalf hpos hH k hsmallProfile hsmallL2 hcenter
    hspan hspanF hspanC hspanS hHistory B1 hBDG1 (A*ν^(-D.beta)) ν
    (mul_nonneg hA0 (Real.rpow_nonneg (zero_le_one.trans hν) _)) (zero_le_one.trans hν) hjet
    p hp Bcur hBDGcur Bword hBDGword χ hχ0 hχ1 horder
    ν ε tail η hν htail hη (by linarith) (timeMeasure (H-h)) hFubini hfinite
  refine ⟨Y,hY,hYa,?_⟩
  rw [hEq,MixedNativeHigherMovingOutput.mass_eq]
  · exact he
  · exact hhH

end SHE.MixedNativeHigherSharpOutput
