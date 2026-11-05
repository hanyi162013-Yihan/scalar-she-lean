module
public import SHE.MixedNativePairedReferenceFull
public import SHE.PastReferenceConstantUniform
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
namespace SHE.MixedNativeReferenceGaussianFamily
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

/-- The actual reference on its own Gaussian band and physical window,
with the true initial reference and completed history reference. -/
def actual{ρ:ℝ}(hL:1≤Λ)(hρ:0≤ρ)(k band:ℕ):ℝ≥0×Ω→CircleL2:=
  let h:=RemainderBandSpans.span D.beta band
  let F:=CanonicalGaussianRootBands.test D n ψ band
  let hF:=CanonicalGaussianRootBands.uniform D n ψ hW hψ band
  let hFm:=CanonicalGaussianRootBands.measurable D n ψ hψm band
  MixedNativePairedReferenceFull.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h (ControlledScalarReference.observations h) (fun _ _=>le_rfl) (fun _ _=>le_rfl)
    F hF hFm hL hρ k

def literal{ρ:ℝ}(hL:1≤Λ)(hρ:0≤ρ)(k band:ℕ):ℝ≥0×Ω→CircleL2:=
  let h:=RemainderBandSpans.span D.beta band
  let F:=CanonicalGaussianRootBands.test D n ψ band
  let hF:=CanonicalGaussianRootBands.uniform D n ψ hW hψ band
  let hFm:=CanonicalGaussianRootBands.measurable D n ψ hψm band
  MixedNativePairedReferenceFull.literal 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P h (ControlledScalarReference.observations h) (fun _ _=>le_rfl) F hF hFm
    J hIJ₀ hIJ₁ hnull hJ hAs (fun _ _=>le_rfl) (fun _ _=>rfl) hL hρ k

local notation "Actual"=>actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP D n ψ hψm hW hψ
local notation "Literal"=>literal 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P D n ψ hψm hW hψ
  J hIJ₀ hIJ₁ hnull hJ hAs
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall
local notation "Amp"=>CanonicalGaussianRootBands.amplitude D W
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

def degrees(β ρ ε η:ℝ)(k:ℕ):Fin 3→ℝ:=![
  PastReferenceBandFrequency.covarianceDegree β k η,
  PastReferenceBandFrequency.baselineDegree β k η,
  PastReferenceBandFrequency.meanDegree β ρ ε k η]

def coefficients(Q:CanonicalCovariance.ProfileParameters)(κ M Λ G H A:ℝ)(k p:ℕ)
    (Babs B0:ℝ≥0)(ρ χ ε η:ℝ):Fin 3→ℝ≥0∞:=![
  ENNReal.ofReal (3*A^2*2^(2*η)*Λ^(-ρ)*PastReferenceBandConstants.covariance Q κ M k Babs η)*ENNReal.ofReal G,
  ENNReal.ofReal (3*A^2*2^(2*η)*Λ^(-ρ)*PastReferenceBandConstants.baseline Q κ M k Babs η)*ENNReal.ofReal G,
  ENNReal.ofReal (3*A^2*2^(2*η)*Λ^(-2*ε)*PastReferenceBandConstants.mean Q κ M k p B0 ρ χ ε η)*
    (ENNReal.ofReal G^χ*ENNReal.ofReal H^(1-χ))]

private theorem cap_eq(Q:CanonicalCovariance.ProfileParameters)(κ M Λ G H A ν:ℝ)(k p:ℕ)
    (Babs B0:ℝ≥0)(ρ χ ε η:ℝ)(hΛ:0≤Λ)(hν:0≤ν):
    ENNReal.ofReal (3*A^2*2^(2*η)*Λ^(-ρ)*
      (PastReferenceBandConstants.covariance Q κ M k Babs η*ν^(-PastReferenceBandFrequency.covarianceDegree Q.exponent k η)+
        PastReferenceBandConstants.baseline Q κ M k Babs η*ν^(-PastReferenceBandFrequency.baselineDegree Q.exponent k η)))*ENNReal.ofReal G+
      ENNReal.ofReal (3*A^2*2^(2*η)*Λ^(-2*ε)*PastReferenceBandConstants.mean Q κ M k p B0 ρ χ ε η*
        ν^(-PastReferenceBandFrequency.meanDegree Q.exponent ρ ε k η))*(ENNReal.ofReal G^χ*ENNReal.ofReal H^(1-χ))=
      ∑i:Fin 3,coefficients Q κ M Λ G H A k p Babs B0 ρ χ ε η i*ENNReal.ofReal (ν^(-degrees Q.exponent ρ ε η k i)):=by
  have hc:=PastReferenceBandConstants.covariance_nonneg Q κ M k Babs η
  have hb:=PastReferenceBandConstants.baseline_nonneg Q κ M k Babs η
  have hm:=PastReferenceBandConstants.mean_nonneg Q κ M k p B0 ρ χ ε η
  have hpre:0≤3*A^2*2^(2*η)*Λ^(-ρ):=by positivity
  have hpm:0≤3*A^2*2^(2*η)*Λ^(-2*ε)*PastReferenceBandConstants.mean Q κ M k p B0 ρ χ ε η:=by positivity
  rw [mul_add,ENNReal.ofReal_add (by positivity) (by positivity)]
  simp only [←mul_assoc]
  rw [ENNReal.ofReal_mul (mul_nonneg hpre hc),ENNReal.ofReal_mul (mul_nonneg hpre hb),ENNReal.ofReal_mul hpm]
  simp only [Fin.sum_univ_three,coefficients,degrees,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons]
  ring

include haP hIJ₀ hIJ₁ hnull hJ hAs in
/-- Exact canonical Gaussian reference fields on one original product
measure. The constants are fixed before every smooth index and band,
and all three decay rates retain their massive-energy factors. -/
theorem family(hA:P.coefficient=(fun z=>κ+aV z))
    (hlocal:StandardTerminalPastLocality J)(hL:1≤Λ){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hHpos:0<H)(hH:(H:ℝ)≤1)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ)(hP:P=Smooth n)(χ:ℝ)(hχ:0<χ)(hχ1:χ<1)
    (p:ℕ)(hp:0<p)(horder:1≤(p:ℝ)*(1-χ))
    (Bpast Babs B0:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs:StandardTerminalBDGPower (k+2) J Babs)
    (hBDG:StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (ε:ℝ)(hε:0≤ε)(hεhalf:ε<1/2)(η:ℝ)(hη:0<η):
    let J0:=NativeGaussianWindowCutoff.index D hT hT1 hsmall H hHpos k
    let q:=degrees D.beta ρ ε η k
    let K:=coefficients Rough κ M Λ Global (H:ℝ) (Amp k) k p Babs B0 ρ χ ε η
    let Y:=fun j=>Actual hL hρ.le k (j+J0)
    (∀j,Measurable (Y j)) ∧
    (∀j,∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Y j (t,ω)=Literal hL hρ.le k (j+J0) (t,ω)) ∧
    (∀j,Integrable (fun z=>‖Y j z‖^2) (energyMeasure μ H)) ∧
    (∀i:Fin 3,K i≠∞) ∧
    ∀j,(∫⁻z,ENNReal.ofReal (‖Y j z‖^2) ∂energyMeasure μ H)≤
      ∑i,K i*ENNReal.ofReal (((2:ℝ)^(j+J0))^(-q i)):=by
  intro J0 q K Y
  have hbet:P.exponent=D.beta:=by rw [hP];rfl
  have hc:=PastReferenceConstantUniform.canonical D hT hT1 hsmall n κ M k p Babs B0 ρ χ ε η
  have hcov:PastReferenceBandConstants.covariance P κ M k Babs η=PastReferenceBandConstants.covariance Rough κ M k Babs η:=by rw [hP];exact hc.1
  have hbase:PastReferenceBandConstants.baseline P κ M k Babs η=PastReferenceBandConstants.baseline Rough κ M k Babs η:=by rw [hP];exact hc.2.1
  have hmean:PastReferenceBandConstants.mean P κ M k p B0 ρ χ ε η=PastReferenceBandConstants.mean Rough κ M k p B0 ρ χ ε η:=by rw [hP];exact hc.2.2
  have hb(j:ℕ):Measurable (Y j) ∧
      (∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Y j (t,ω)=Literal hL hρ.le k (j+J0) (t,ω)) ∧
      Integrable (fun z=>‖Y j z‖^2) (energyMeasure μ H) ∧
      (∫⁻z,ENNReal.ofReal (‖Y j z‖^2) ∂energyMeasure μ H)≤
        ∑i,K i*ENNReal.ofReal (((2:ℝ)^(j+J0))^(-q i)):=by
    let band:=j+J0
    let h:=RemainderBandSpans.span D.beta band
    let Z:=ControlledScalarReference.observations h
    let F:=CanonicalGaussianRootBands.test D n ψ band
    let hF:=CanonicalGaussianRootBands.uniform D n ψ hW hψ band
    let hFm:=CanonicalGaussianRootBands.measurable D n ψ hψm band
    have hr:=NativeGaussianWindowCutoff.ready D hT hT1 hsmall H hHpos k band (by dsimp [band];omega)
    have hspan:(h:ℝ)≤P.horizon:=by rw [hP];exact hr.2.1
    have hj:∀x l,l≤k→∀z,‖iteratedFDeriv ℝ l (F x) z‖≤(Amp k*((2:ℝ)^band)^(-P.exponent))*((2:ℝ)^band)^l:=by
      rw [hbet]
      exact fun x l hl z=>CanonicalGaussianRootBands.jets D n ψ hW hψ k band x l hl z
    have he:=MixedNativePairedReferenceFull.actual_full
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z (fun _ _=>le_rfl) (fun _ _=>le_rfl)
      F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs (fun _ _=>le_rfl) (fun _ _=>rfl) hL hρ.le
      hA hlocal hH hsmallPoint hsmallL2 (fun _ _=>le_rfl) (fun _=>rfl) hspan k
      hr.2.2.2.2.1 hr.2.2.2.2.2 (Amp k) ((2:ℝ)^band) (CanonicalGaussianRootBands.amplitude_nonneg D hW k)
      (one_le_pow₀ (by norm_num:(1:ℝ)≤2)) hj χ hχ hχ1 p hp horder Bpast Babs B0 hBDGpast hBDGabs hBDG
      hρ hρhalf ε hε hεhalf (show h≤H from hr.1) (RemainderBandSpans.span_pos D.beta band)
      (by rw [hbet];rfl) η hη
    refine ⟨he.1,he.2.1,he.2.2.1,he.2.2.2.trans_eq ?_⟩
    dsimp only at he ⊢
    rw [hcov,hbase,hmean,hbet]
    exact cap_eq Rough κ M Λ Global (H:ℝ) (Amp k) ((2:ℝ)^band) k p Babs B0 ρ χ ε η
      (zero_le_one.trans hL) (by positivity)
  have hKG:ENNReal.ofReal Global^χ≠∞:=ENNReal.rpow_ne_top_of_nonneg hχ.le ENNReal.ofReal_ne_top
  have hKH:ENNReal.ofReal (H:ℝ)^(1-χ)≠∞:=ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  refine ⟨fun j=>(hb j).1,fun j=>(hb j).2.1,fun j=>(hb j).2.2.1,?_,fun j=>(hb j).2.2.2⟩
  intro i
  fin_cases i
  · change ENNReal.ofReal _*ENNReal.ofReal _≠∞
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · change ENNReal.ofReal _*ENNReal.ofReal _≠∞
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · change ENNReal.ofReal _*(ENNReal.ofReal Global^χ*ENNReal.ofReal (H:ℝ)^(1-χ))≠∞
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hKG hKH)

end SHE.MixedNativeReferenceGaussianFamily
