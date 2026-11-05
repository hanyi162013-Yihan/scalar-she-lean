module
public import SHE.MixedPastNativeBaselineLeaf
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

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeBaselineRow
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

local notation "Input"=>MixedPastOmittedMarkFields.leafInput
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- The actual baseline multiplier square is integrable at EVERY
original history/space point, from coarse profile regularity and the
original pair's past second energy. Quantitative estimates retain its
sharp spatial RMS rather than this coarse applicability bound. -/
theorem leaf_input_integrable (hΛ:0≤Λ)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH:v≤H) (hv1:(v:ℝ)≤1) (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (k:ℕ) (h:History X k) (q:ℝ≥0) (hvq:v≤q) (hqt:(q:ℝ)<(carrier Zero k).terminal h)
    (θ:ℝ) (j0:Fin k):Integrable (fun ω=>|Input k θ h j0 ω|^2) μ:=by
  have hDenergy:=MixedHeatedDifferenceMoments.current_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ v hvH hv1 1 (by decide) Bpast hBDGpast
  have hDi:Integrable (fun ω=>‖Dir ω‖^2) μ:=by
    simpa only [MixedPastJointData.pastD,NativeHeatObservation.embed_norm] using hDenergy.1
  let e:=Input k θ h j0
  have he:Measurable e:=(MixedPastOmittedMarkFields.leaf_input_past_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k θ h j0).mono (𝓕.le v) le_rfl
  let age:=lower Zero k h j0-(v:ℝ)
  have hage:0≤age:=by
    have hlow:=terminal_le_lower Zero k h j0
    have hvq':(v:ℝ)≤(q:ℝ):=by exact_mod_cast hvq
    dsimp only [age]
    linarith
  let K:=2*(ProfileStability.meanConstant P.lower P.holder P.exponent*
    Real.sqrt (1+StoppedFourier.heatConstant))*age^((P.exponent-2)/4)
  have hb(ω:Ω):|e ω|≤K*‖Dir ω‖:=by
    have hh:=ControlledScoreRates.derivative_coarse_power P hΛ (U ω) (Dir ω) hsmall θ
      (age,space k h j0) hage
    convert! hh using 1 <;> dsimp only [e,MixedPastOmittedMarkFields.leafInput,age,K,ControlledScoreRates.coarseConstant] <;> ring
  apply (hDi.const_mul (K^2)).mono' ((continuous_abs.measurable.comp he).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun ω=>by
    have hh:=pow_le_pow_left₀ (abs_nonneg (e ω)) (hb ω) 2
    convert! hh using 1 <;> simp only [Real.norm_eq_abs,abs_pow,abs_abs,mul_pow,Function.comp_apply])

include hIJ₀ hIJ₁ in
/-- Actual omitted-baseline input and Gaussian word may be correlated.
The true F_v derivative is used as a conditional weight BEFORE spatial
averaging. Only its genuine pointwise sample energy is required here. -/
theorem energy_ae (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH:v≤H) (hv1:(v:ℝ)≤1) (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∃ Hf Cf : ℝ,0<Hf ∧ 0<Cf ∧
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k,
      ∀ q : ℝ≥0,v≤q→q≤H→(q:ℝ)<(carrier Zero k).terminal h→
      ∀ r:ℝ,(q:ℝ)≤r → r<(carrier Zero k).terminal h →
      (∀ i,targets Zero k h i-r≤Hf) →
      ∀ hp : StrictHistory Zero k h,SmallHistory Zero (uniformHorizon n) k h→
      ∀ θ : ℝ,|θ|≤1→∀ A0 ν : ℝ,0≤A0→0≤ν→
      (∀ j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j)→
      ∀ j0 : Fin k,∀ B0 : ℝ≥0,StandardTerminalBDGPower (k+2) J B0→
      ∀ᵐ y:HeatCircle∂haarAddCircle,
      let E:=heatRow ((carrier Zero k).observations.observations h) r y
      let e:=MixedPastOmittedMarkFields.leafInput
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ h j0
      let fresh:=Real.sqrt (Cf/((P.lower/8)*((carrier Zero k).terminal h-r)))*
        ∑i,Real.sqrt ‖ProfileVariance.heatPhysical (4*(targets Zero k h i-r)) (centers Zero k h i) y‖
      let oldEnvelope:=timeWeight Zero (fraction P*P.lower) (uniformConstant n) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero hages k h hp) (centers Zero k h)
      let sharp:=NativeOmittedTimeTotal.total (d:=n) P
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ))
        (fun j=>targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ)) j0 A0 ν
      let G:=MixedPastNativeBaselineLeaf.value
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q h E j0
      Integrable (fun ω=>|G ω|^2) μ ∧
        (∫ ω,|G ω|^2 ∂μ)≤
          NativeOmittedCompleteWord.momentConstant P k k j0 1
            ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)*
              (oldEnvelope*fresh*sharp)^2*(∫ ω,|e ω|^2 ∂μ) := by
  obtain ⟨Hf,Cf,hHf,hCf,henv⟩:=NativeReserveRowEnvelope.sqrt_heat_envelope (n+k)
  refine ⟨Hf,Cf,hHf,hCf,?_⟩
  filter_upwards [MixedPastNativeBaselineLeaf.leaf_moment_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmall hages hspan ρ k] with h hleaf
  intro q hvq hqH hqt r hqr hrt hsmallAge hp hsmallOld θ hθ A0 ν hA0 hν hjet j0 B0 hBDG
  let σ:=fun i=>stops Zero k h i-(v:ℝ)
  let target:=fun i=>targets Zero k h i-(v:ℝ)
  let center:=centers Zero k h
  let Q:Fin (n+k)→Observation:=(carrier Zero k).observations.observations h
  have hQage(i:Fin (n+k)):(Q i).stop≤(Q i).target:=
    RecursiveScoreSupport.carrier_ages Zero hages k h i
  have hQstop(i:Fin (n+k)):(carrier Zero k).terminal h≤(Q i).stop:=
    (carrier Zero k).stops_after h i
  have hQsmall(i:Fin (n+k)):(Q i).target-r≤Hf:=hsmallAge i
  have hstopEq:stops Zero k h=(fun i=>(Q i).stop):=by
    funext i
    exact min_eq_left (CarrierStopBounds.stop_le_initial Zero hrootStop k h i)
  have hNative:NativeFirstScoreReserve.covariance P (stops Zero k h) (targets Zero k h) center q=
      NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ)):=
    ControlledThetaTwoFreshArrays.native_relative P (v:ℝ) q _ _ center
  filter_upwards [henv P Q hQage q.2 hqr hrt hQstop hQsmall] with y hy
  intro E e fresh oldEnvelope sharp G
  have hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ)))).range:=by
    rw [←hNative,hstopEq]
    exact hy.1
  have hscore:Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ))) E)≤fresh:=by
    rw [←hNative,hstopEq]
    exact hy.2
  have hEi:=leaf_input_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall hvH hv1 Bpast hBDGpast k h q hvq hqt θ j0
  have hmom:=hleaf q hvq hqH hqt hp hsmallOld θ hθ A0 ν hA0 hν hjet E hE j0 B0 hBDG hEi
  refine ⟨hmom.1,hmom.2.trans ?_⟩
  have hOld:0≤oldEnvelope:=mul_nonneg
    (timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant n)
      (fun j=>(uniformConstant_pos n j).le) k h hp)
    (OrderedHeatForests.parentDensity_nonneg 2 (by norm_num) k _ _ _)
  have hSharp:0≤sharp:=NativeOmittedTimeTotal.total_nonneg P _ _ _ j0 A0 ν
  have hraw:0≤oldEnvelope*Real.sqrt (scoreVariance
      (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ))) E)*sharp:=
    mul_nonneg (mul_nonneg hOld (Real.sqrt_nonneg _)) hSharp
  have hcost:oldEnvelope*Real.sqrt (scoreVariance
      (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ))) E)*sharp≤
      oldEnvelope*fresh*sharp:=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscore hOld) hSharp
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hraw hcost 2)
      (NativeOmittedCompleteWord.momentConstant_nonneg P k k j0 1 _))
    (integral_nonneg (fun _=>sq_nonneg _))

end SHE.MixedPastNativeBaselineRow
