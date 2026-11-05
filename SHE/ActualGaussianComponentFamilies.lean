module
public import SHE.CommonHigherGaussianFamily
public import SHE.CommonReferenceGaussianFamily
public import SHE.MixedNativeHigherGaussianTailFamily
public import SHE.FiniteNativeGaussianCutoff
public import SHE.FullHigherClockIdentity
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
namespace SHE.ActualGaussianComponentFamilies
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
variable (n:ℕ)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))

local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Pzero"=>Smooth 0
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall
local notation "scoreFloor"=>ControlledOldIntervals.fraction Pzero*(Pzero).lower
local notation "Cs"=>PhysicalScoreChain.uniformConstant 1
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
variable (N Jbase:ℕ)(ρ χ χref η ε tail ζ εref ηref:ℝ)
  (hρ:0<ρ)(hχ0:0≤χ)(hχ1:χ<1)(hm:χ<D.beta+2*ρ)
  (hα:0<ρ+η)(hαhalf:ρ+η<1/2)(hζ:0<ζ)
  (hχref:0<χref)(hχref1:χref<1)(hεref:0≤εref)(hεrefhalf:εref<1/2)(hηref:0<ηref)
  (p:ℕ)(hp:0<p)(Bcur Bword Bref:ℕ→ℝ≥0)
local notation "Bare"=>CanonicalGaussianBareRoot.test D n
local notation "BU"=>CanonicalGaussianBareRoot.uniform D n
local notation "BM"=>CanonicalGaussianBareRoot.measurable D n
local notation "OriginalR"=>FullReferenceClockIdentity.original
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P J hIJ₀ hIJ₁ hnull hJ hAs
local notation "OriginalH"=>FullHigherClockIdentity.original
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P J hIJ₀ hIJ₁ hnull hJ hAs

/-- Actual reference components at a single cutoff shared by all finite depths. -/
def reference(k j:ℕ)(hL:1≤Λ):ℝ≥0×Ω→CircleL2:=
  MixedNativeReferenceGaussianFamily.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D n
    (fun _:HeatCircle=>(1:ℝ)) measurable_const (W:=1) zero_le_one (fun _=>by norm_num)
    hL hρ.le (k+1) (j+Jbase+1)
local notation "Ref"=>reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D n Jbase ρ hρ

include hχ0 hχ1 hm hα hαhalf hζ hχref hχref1 hεref hεrefhalf hηref hp in
/-- The common-cutoff finite reference and higher-noise fields are supplied by
actual same-noise constructions, rather than by an assumed comparison budget. -/
theorem exists_family(hA:P.coefficient=(fun z=>κ+aV z))
    (hlocal:StandardTerminalPastLocality J)(hL:1≤Λ)(hρhalf:ρ<1/2)
    (hHpos:0<H)(hH:(H:ℝ)≤1)
    (hsmallProfile:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)(hP:P=Smooth n)
    (hBDGcur:∀k,k<N→StandardTerminalBDGPower (p*(k+3)) J (Bcur k))
    (hBDGword:∀k,k<N→StandardTerminalBDGPower (k+3) J (Bword k))
    (hBDGref:∀k,k<N→StandardTerminalBDGPower ((2*p)*(k+3)) J (Bref k))
    (horder:1≤(p:ℝ)*(1-χ))(horderref:1≤(p:ℝ)*(1-χref))
    (htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)(hFubini:StandardItoParameterFubini J)
    (hJbase:FiniteNativeGaussianCutoff.index D hT hT1 hsmall H hHpos N≤Jbase):
    ∃Y:Fin N→ℕ→ℝ≥0×Ω→CircleL2,
      (∀(k:Fin N) j,Measurable (Ref k j hL)) ∧ (∀k j,Measurable (Y k j)) ∧
      (∀(k:Fin N) j,∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Ref k j hL (t,ω)=
        OriginalR (Bare (j+Jbase+1)) (BU (j+Jbase+1)) (BM (j+Jbase+1))
          (RemainderBandSpans.span D.beta (j+Jbase+1)) hL hρ.le (k+1) (t,ω)) ∧
      (∀k j,∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Y k j (t,ω)=
        OriginalH (Bare (j+Jbase+1)) (BU (j+Jbase+1)) (BM (j+Jbase+1))
          (RemainderBandSpans.span D.beta (j+Jbase+1)) hL hρ.le (k+1) (t,ω)) ∧
      (∀(k:Fin N) j,Integrable (fun z=>‖Ref k j hL z‖^2) (energyMeasure μ H)) ∧
      (∀k j,Integrable (fun z=>‖Y k j z‖^2) (energyMeasure μ H)):=by
  have hR(k:Fin N):=(CommonReferenceGaussianFamily.family
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D hT hT1 hsmall n
    J hIJ₀ hIJ₁ hnull hJ hAs hA hlocal hL hρ hρhalf hHpos hH hsmallProfile hsmallL2
    (k+1) hP χref hχref hχref1 p hp horderref B1 (Bword k) (Bref k) hBDG1
    (by simpa only [Nat.add_assoc] using hBDGword k k.isLt)
    (by simpa only [Nat.add_assoc] using hBDGref k k.isLt)
    εref hεref hεrefhalf ηref hηref N Jbase (by omega) (by omega) hJbase)
  have hH(k:Fin N):∃Y:ℕ→ℝ≥0×Ω→CircleL2,(∀j,Measurable (Y j)) ∧
      (∀j,∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Y j (t,ω)=
        OriginalH (Bare (j+Jbase+1)) (BU (j+Jbase+1)) (BM (j+Jbase+1))
          (RemainderBandSpans.span D.beta (j+Jbase+1)) hL hρ.le (k+1) (t,ω)) ∧
      (∀j,Integrable (fun z=>‖Y j z‖^2) (energyMeasure μ H)):=by
    obtain ⟨Y,hY,hYa,hi,_,_⟩:=CommonHigherGaussianFamily.exists_family
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D hT hT1 hsmall n
      J hIJ₀ hIJ₁ hnull hJ hAs (k+1) (by omega) ρ χ η ε tail ζ hρ hχ0 hχ1 hm hα hαhalf hζ
      hA hlocal hL hρhalf hHpos hH hsmallProfile hsmallL2 B1 hBDG1 hP
      p hp (Bcur k) (by simpa only [Nat.add_assoc] using hBDGcur k k.isLt)
      (Bword k) (by simpa only [Nat.add_assoc] using hBDGword k k.isLt)
      horder htail hη hFubini N Jbase (by omega) hJbase
    exact ⟨Y,hY,hYa,hi⟩
  choose Y hYm hYa hYi using hH
  exact ⟨Y,(fun k=> (hR k).1),hYm,(fun k=>(hR k).2.1),hYa,(fun k=>(hR k).2.2.1),hYi⟩
end SHE.ActualGaussianComponentFamilies
