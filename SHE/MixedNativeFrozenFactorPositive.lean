module

public import SHE.NativeFrozenFactorIdentity
public import SHE.MixedNativeFrozenFactorGammaTime
public import SHE.EllipticPositiveEnergy
public import SHE.NativeGammaAgeValue
public import SHE.MixedNativeGammaEnergy
public import SHE.MixedPastReferenceInput
public import SHE.FirstGammaCanonicalReferenceEnergy
public import SHE.ScalarHeatGradientOpenTime
public import SHE.ControlledVarianceGammaTime

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeFrozenFactorPositive
open MeasureTheory AddCircle GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaReferenceEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance firstGammaFrozenValues_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaFrozenValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaFrozenValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaFrozenValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaFrozenValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaFrozenValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance frozenFactorPositive_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance frozenFactorPositive_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance frozenFactorPositive_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance frozenFactorPositive_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
variable {Ω : Type*}
 [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P:CanonicalCovariance.ProfileParameters) (hκP:κ<P.lower)
variable (hΛ:0≤Λ) (v b:ℝ≥0) (hvb:v<b) (hbH:b≤H) (hH:(H:ℝ)≤1)
variable (hwindow:(b:ℝ)-(v:ℝ)≤P.horizon)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 2 J Bpast)
local notation "OldU"=>S.first v
local notation "OldD"=>(fun ω=>S.second v ω-S.first v ω)
local notation "OldUM"=>(((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v).measurable)
local notation "OldDM"=>((((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted v).sub
  ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v)).measurable)
local notation "hb1"=>((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH)

def frozen (θ:ℝ)(p:ℝ≥0×Ω):CircleHeat.CircleL2:=
  (NativeCanonicalGammaEnergy.frozen (v:=v) (U:=Function.uncurry S.first) (V:=Function.uncurry S.second)
    (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP)
    (m:=MixedNativeGammaEnergy.commonLower (ell:=ell) (P:=P) (κ:=κ))
    (W:=MixedNativeGammaEnergy.commonUpper (M:=M) (P:=P) (κ:=κ))
    (hmP:=min_le_right _ _) (hWP:=le_max_right _ _) θ p).val
local notation "R"=>frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v

def integrand (A ρ:ℝ)(j:ℕ)(τ:ℝ):ℝ:=
  ∫ω,(NativeCanonicalGammaSharp.sharp (v:=v) (b:=b) (P:=P) A P.exponent j (((b:ℝ)-τ).toNNReal,ω))^2*
    (NativeHeatSpan.clock (NativeGammaClock.age v b (((b:ℝ)-τ).toNNReal,ω)))^(ρ-1/2)*
      ‖R 0 (((b:ℝ)-τ).toNNReal,ω)-R 1 (((b:ℝ)-τ).toNNReal,ω)‖^2 ∂μ
local notation "G"=>integrand 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b

def constant (A ρ:ℝ):ℝ:=
  let p:=(P.exponent-1)/2
  (4*Real.pi^2)^(1/2-ρ)*(A*ScalarHeatBandEnvelope.constant P.exponent 0)^2*
    (2*ProfileStability.meanConstant P.lower P.holder P.exponent)^2*
      (((1/2:ℝ)^p)*(1/(ρ+1/2)+1/(1-P.exponent/2-ρ))+2/(p+1))*
        (ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)

def density (A ρ:ℝ)(j:ℕ)(τ:ℝ)(ω:Ω):ℝ:=
  (NativeCanonicalGammaSharp.sharp (v:=v) (b:=b) (P:=P) A P.exponent j (((b:ℝ)-τ).toNNReal,ω))^2*
    (NativeHeatSpan.clock (NativeGammaClock.age v b (((b:ℝ)-τ).toNNReal,ω)))^(ρ-1/2)*
      ‖R 0 (((b:ℝ)-τ).toNNReal,ω)-R 1 (((b:ℝ)-τ).toNNReal,ω)‖^2
local notation "Density"=>density 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b

def budget (A ρ:ℝ)(j:ℕ):ℝ≥0∞:=
  ∫⁻τ in Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (Density A ρ j τ ω) ∂μ
local notation "Budget"=>budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b

include hIJ₀ hIJ₁ hΛ hH hvb hbH hwindow hsmall hBDGpast in
/-- Exact positive time/sample version of the actual changed frozen
factor cap. True elliptic-factor sample integrability is derived. -/
theorem energy {A ρ:ℝ} (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2) (j:ℕ):
    Budget A ρ j≤ENNReal.ofReal (constant P A ρ*CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*
      ((b:ℝ)-(v:ℝ))^((P.exponent-1)/2)*(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)):=by
  let F:=fun θ=>NativeCanonicalGammaEnergy.frozen (v:=v) (U:=Function.uncurry S.first) (V:=Function.uncurry S.second)
    (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP)
    (m:=MixedNativeGammaEnergy.commonLower (ell:=ell) (P:=P) (κ:=κ))
    (W:=MixedNativeGammaEnergy.commonUpper (M:=M) (P:=P) (κ:=κ))
    (hmP:=min_le_right _ _) (hWP:=le_max_right _ _) θ
  have hF(θ:ℝ):Measurable (F θ):=
    (NativeCanonicalGammaEnergy.frozen_predictable (𝓕:=𝓕) (hU:=S.first_predictable) (hV:=S.second_predictable)
      (v:=v) (U:=Function.uncurry S.first) (V:=Function.uncurry S.second) (P:=P) (Λ:=Λ) (κ:=κ)
      (hκP:=hκP) (hmP:=min_le_right _ _) (hWP:=le_max_right _ _) θ).mono (predictable_le_product 𝓕) le_rfl
  have hn(τ:ℝ)(ω:Ω):0≤Density A ρ j τ ω:=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (NativeHeatSpan.clock_pos (NativeGammaClock.age_pos v b (((b:ℝ)-τ).toNNReal,ω))).le _)) (sq_nonneg _)
  have hcast(τ:ℝ)(ht:τ∈Set.Ioo (0:ℝ) ((b:ℝ)-(v:ℝ))):
      (∫⁻ω,ENNReal.ofReal (Density A ρ j τ ω) ∂μ)=ENNReal.ofReal (G A ρ j τ):=by
    let q:=((b:ℝ)-τ).toNNReal
    have hi:=EllipticPositiveEnergy.integrable μ (fun ω=>F 0 (q,ω)) (fun ω=>F 1 (q,ω))
      ((hF 0).comp (measurable_const.prodMk measurable_id)) ((hF 1).comp (measurable_const.prodMk measurable_id))
    let K:ℝ:=(A*ScalarHeatBandEnvelope.constant P.exponent 0*CompactMollifier.radius (j+1)^(P.exponent-1)*
      ScalarHeatBandEnvelope.decay (CompactMollifier.radius (j+1)) (ProfileVariance.lowerConstant*P.lower*Real.sqrt τ)
        ((3-P.exponent)/2))^2*(NativeHeatSpan.clock τ)^(ρ-1/2)
    have he:(fun ω=>Density A ρ j τ ω)=(fun ω=>K*‖(F 0 (q,ω)).val-(F 1 (q,ω)).val‖^2):=by
      funext ω
      dsimp only [density]
      rw [NativeGammaAgeValue.sharp P v b A P.exponent j ht ω,NativeGammaAgeValue.age v b ht ω]
      rfl
    have hiD:Integrable (Density A ρ j τ) μ:=by
      change Integrable (fun ω=>Density A ρ j τ ω) μ
      rw [he]
      exact hi.const_mul K
    exact (ofReal_integral_eq_lintegral_ofReal hiD (ae_of_all _ (hn τ))).symm
  have he:=MixedNativeFrozenFactorGammaTime.energy (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (P:=P) (hκP:=hκP) (hΛ:=hΛ) (v:=v) (b:=b)
    (hvb:=hvb) (hbH:=hbH) (hH:=hH) (hwindow:=hwindow) (hsmall:=hsmall) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    (A:=A) hρ0 hρ1 j
  have hm:∀ᵐτ∂volume.restrict (Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ))),τ∈Set.Ioo (0:ℝ) ((b:ℝ)-(v:ℝ)):=by
    rw [←restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  calc
    _=(∫⁻τ in Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),ENNReal.ofReal (G A ρ j τ)):=
      lintegral_congr_ae (hm.mono (fun τ ht=>hcast τ ht))
    _=ENNReal.ofReal (∫τ in Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),G A ρ j τ):=
      (ofReal_integral_eq_lintegral_ofReal he.1 (ae_of_all _ (fun τ=>integral_nonneg (hn τ)))).symm
    _≤_:=ENNReal.ofReal_le_ofReal he.2
end SHE.MixedNativeFrozenFactorPositive
