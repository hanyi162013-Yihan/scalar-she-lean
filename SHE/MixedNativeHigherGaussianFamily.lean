module
public import SHE.MixedNativeHigherGaussianBand
public import SHE.NativeGaussianWindowCutoff
public import SHE.NativeFullRateCap
public import SHE.HilbertENNRateTails
public import SHE.MixedNativeHigherFullOutput
public import SHE.CanonicalGaussianRootBands
public import SHE.MixedNativeHigherMovingRate
public import SHE.MixedNativeMovingEnvelopeRate
public import SHE.MixedNativeHigherSharpOutput
public import SHE.MixedNativeHigherSharpInitial
public import SHE.NativeOutputTimePatch
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
namespace SHE.MixedNativeHigherGaussianFamily
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
variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
variable (n:ℕ)(ψ:HeatCircle→ℝ)(hψm:Measurable ψ)
variable {W:ℝ}(hW:0≤W)(hψ:∀x,|ψ x|≤W)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))

/-- The literal actual kth paired output for its own Gaussian band and
its own physical window, including the true initial triangle. -/
def actual{ρ:ℝ}(hL:1≤Λ)(hρ0:0≤ρ)(k band:ℕ):ℝ≥0×Ω→CircleL2:=
  let h:=RemainderBandSpans.span D.beta band
  let F:=CanonicalGaussianRootBands.test D n ψ band
  let hF:=CanonicalGaussianRootBands.uniform D n ψ hW hψ band
  let hFm:=CanonicalGaussianRootBands.measurable D n ψ hψm band
  NativeOutputTimePatch.field h
    (MixedNativeHigherInitialOutput.output
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
      J hIJ₀ hIJ₁ hnull hJ hAs hL hρ0 k)
    (MixedNativeHigherMovingOutput.output
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P h (ControlledScalarReference.observations h) F hF hFm
      J hIJ₀ hIJ₁ hnull hJ hAs (fun _=>rfl) (fun _=>rfl) hL hρ0 k)

local notation "Pzero"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall 0
local notation "scoreFloor"=>ControlledOldIntervals.fraction Pzero*(Pzero).lower
local notation "Cs"=>PhysicalScoreChain.uniformConstant 1
variable (k:ℕ)(hk:0<k)
local notation "A"=>CanonicalGaussianRootBands.amplitude D W k
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
local notation "Actual"=>actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D n ψ hψm hW hψ
  J hIJ₀ hIJ₁ hnull hJ hAs

include haP hIJ₀ hIJ₁ hnull hJ hρ hχ0 hχ1 hm hα hαhalf hζ in
/-- All actual canonical Gaussian bands are chosen simultaneously as
Borel original-time noise fields. The finite-depth cutoff is fixed
before the smoothing index, and each field retains its own window. -/
theorem exists_family(hA:P.coefficient=(fun z=>κ+aV z))
    (hlocal:StandardTerminalPastLocality J)(hL:1≤Λ)(hρhalf:ρ<1/2)
    (hHpos:0<H)(hH:(H:ℝ)≤1)
    (hsmallProfile:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)(hP:P=Smooth n)
    (p:ℕ)(hp:0<p)(Bcur:ℝ≥0)(hBDGcur:StandardTerminalBDGPower (p*(k+2)) J Bcur)
    (Bword:ℝ≥0)(hBDGword:StandardTerminalBDGPower (k+2) J Bword)
    (horder:1≤(p:ℝ)*(1-χ))(htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)
    (hFubini:StandardItoParameterFubini J):
    let J0:=NativeGaussianWindowCutoff.index D hT hT1 hsmall H hHpos k
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
    let q:=NativeFullRateCap.degree qc qp qg qb
    let K:=NativeFullRateCap.coefficient
      (ENNReal.ofReal (8*A^2*Ccur^2)) (ENNReal.ofReal (8*A^2*Cpast^2))
      (ENNReal.ofReal (4*A^2*Cgood^2)) (ENNReal.ofReal (4*A^2*Cbad^2))
      Cc Ci Cp Cg Cb Global (H:ℝ) χ (Neg ρ)
    ∃Y:ℕ→ℝ≥0×Ω→CircleL2,(∀j,Measurable (Y j)) ∧
      (∀j,∀ᵐt∂timeMeasure H,(fun ω=>Y j (t,ω))=ᵐ[μ]
        (fun ω=>Actual hL hρ.le k (j+J0) (t,ω))) ∧
      (∀j,Integrable (fun z=>‖Y j z‖^2) (energyMeasure μ H)) ∧
      (∀i:Fin 4,K i≠∞) ∧
      ∀j,(∫⁻z,ENNReal.ofReal (‖Y j z‖^2) ∂energyMeasure μ H)≤
        ∑i,K i*ENNReal.ofReal ((((2:ℝ)^(j+J0)))^(-q i)):=by
  intro J0 Cf Cdim C Ccur Cpast Jt Cmom Cgood Cbad q K
  have hband(j:ℕ):∃Y:ℝ≥0×Ω→CircleL2,Measurable Y ∧
      (∀ᵐt∂timeMeasure H,(fun ω=>Y (t,ω))=ᵐ[μ]
        (fun ω=>Actual hL hρ.le k (j+J0) (t,ω))) ∧
      Integrable (fun z=>‖Y z‖^2) (energyMeasure μ H) ∧
      (∫⁻z,ENNReal.ofReal (‖Y z‖^2) ∂energyMeasure μ H)≤
        ∑i,K i*ENNReal.ofReal ((((2:ℝ)^(j+J0)))^(-q i)):=by
    let band:=j+J0
    let h:=RemainderBandSpans.span D.beta band
    let Z:=ControlledScalarReference.observations h
    have hr:=NativeGaussianWindowCutoff.ready D hT hT1 hsmall H hHpos k band (by dsimp [band];omega)
    have hspan:(h:ℝ)≤P.horizon:=by
      rw [hP]
      exact hr.2.1
    obtain ⟨Y,hY,hYa,hi,hb⟩:=MixedNativeHigherGaussianBand.exists_band
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z
      (fun _ _=>le_rfl) (fun _ _=>le_rfl) D hT hT1 hsmall n band ψ hψm hW hψ
      J hIJ₀ hIJ₁ hnull hJ hAs (fun _=>rfl) (fun _=>rfl) k hk
      ρ χ η ε tail ζ hρ hχ0 hχ1 hm hα hαhalf hζ hA hlocal hL hρhalf
      (RemainderBandSpans.span_pos D.beta band) hH hsmallProfile hsmallL2
      (fun _=>rfl) hspan hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2
      B1 hBDG1 hP rfl p hp Bcur hBDGcur Bword hBDGword horder htail hη
      (show h≤H from hr.1) hFubini
    refine ⟨Y,hY,hYa,hi,?_⟩
    convert hb using 1
    exact (NativeFullRateCap.combine
      (ENNReal.ofReal (8*A^2*Ccur^2)) (ENNReal.ofReal (8*A^2*Cpast^2))
      (ENNReal.ofReal (4*A^2*Cgood^2)) (ENNReal.ofReal (4*A^2*Cbad^2))
      Cc Ci Cp Cg Cb Global (H:ℝ) χ ((2:ℝ)^band) qc qp qg qb (Neg ρ) (by positivity)).symm
  choose Y hY hYa hi hb using hband
  have hNeg:Neg ρ≠∞:=ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (MixedActualEnergyBridge.negative_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (zero_lt_one.trans_le hL) hρ.le)
  have hpowG:ENNReal.ofReal Global^χ≠∞:=ENNReal.rpow_ne_top_of_nonneg hχ0 ENNReal.ofReal_ne_top
  have hpowH:(ENNReal.ofReal (H:ℝ))^(1-χ)≠∞:=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  refine ⟨Y,hY,hYa,hi,?_,hb⟩
  intro i
  fin_cases i
  · change ENNReal.ofReal (8*A^2*Ccur^2)*(ENNReal.ofReal Ci+ENNReal.ofReal Cc)*
      (ENNReal.ofReal Global^χ*ENNReal.ofReal (H:ℝ)^(1-χ))≠∞
    finiteness
  · change ENNReal.ofReal (8*A^2*Cpast^2)*ENNReal.ofReal Cp*ENNReal.ofReal Global≠∞
    finiteness
  · change 2*ENNReal.ofReal (4*A^2*Cgood^2)*ENNReal.ofReal Cg*Neg ρ≠∞
    finiteness
  · change 2*ENNReal.ofReal (4*A^2*Cbad^2)*ENNReal.ofReal Cb*ENNReal.ofReal (H:ℝ)≠∞
    finiteness

end SHE.MixedNativeHigherGaussianFamily
