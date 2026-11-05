module

public import SHE.NativeFrozenFactorIdentity
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

namespace SHE.MixedNativeFrozenFactorGammaTime
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
variable {Ω : Type*} [MeasurableSpace Ω]
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

include hIJ₀ hIJ₁ hΛ hH hvb hbH hwindow hsmall hBDGpast in
/-- Literal changed frozen-factor term in the COMPLETE original-J
Gamma estimate, with exact native clock and both time-face gains.
All reference-profile and actual past-energy hypotheses are derived. -/
theorem energy {A ρ:ℝ} (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2) (j:ℕ):
    IntegrableOn (G A ρ j) (Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ))) ∧
      (∫τ in Set.Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),G A ρ j τ)≤
        constant P A ρ*(CompactMollifier.radius (j+1))^(2*P.exponent+4*ρ)*
          ((b:ℝ)-(v:ℝ))^((P.exponent-1)/2)*(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ):=by
  have hu:Measurable (fun ω=>embed (OldU ω)):=embed.continuous.measurable.comp ((OldUM).mono (𝓕.le v) le_rfl)
  have hd:Measurable (fun ω=>embed (OldD ω)):=embed.continuous.measurable.comp ((OldDM).mono (𝓕.le v) le_rfl)
  have hv1:(v:ℝ)≤1:=(show (v:ℝ)≤(H:ℝ) from by exact_mod_cast hvb.le.trans hbH).trans hH
  have hi:=MixedPastReference.data_moments 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    hΛ v (hvb.le.trans hbH) hv1 (p:=1) (by norm_num) Bpast hBDGpast
  have hi':Integrable (fun ω=>‖embed (OldD ω)‖^2) μ:=by
    simpa only [MixedPastReference.data] using hi.1
  let hh:ℝ:=(b:ℝ)-(v:ℝ)
  let Cclock:ℝ:=(4*Real.pi^2)^(1/2-ρ)
  let B:=fun τ=>τ^(ρ-1/2)*(A*ScalarHeatBandEnvelope.constant P.exponent 0*
      CompactMollifier.radius (j+1)^(P.exponent-1)*ScalarHeatBandEnvelope.decay (CompactMollifier.radius (j+1))
        (ProfileVariance.lowerConstant*P.lower*Real.sqrt τ) ((3-P.exponent)/2))^2*
    (∫ω,‖NativeFrozenFactorGammaTime.coefficient P Λ κ hκP (fun ω=>embed (OldU ω)) (fun ω=>embed (OldD ω)) 0 (hh-τ) ω-
      NativeFrozenFactorGammaTime.coefficient P Λ κ hκP (fun ω=>embed (OldU ω)) (fun ω=>embed (OldD ω)) 1 (hh-τ) ω‖^2 ∂μ)
  have hbase:=NativeFrozenFactorGammaTime.energy μ P Λ κ hκP (fun ω=>embed (OldU ω)) (fun ω=>embed (OldD ω)) hu hd
    hΛ (A:=A*ScalarHeatBandEnvelope.constant P.exponent 0) (show 0<hh by dsimp only [hh];exact sub_pos.mpr (by exact_mod_cast hvb))
    hwindow hρ0 hρ1 hsmall hi' 0 1 j
  have heq(τ:ℝ)(ht:τ∈Set.Ioo (0:ℝ) hh):G A ρ j τ=Cclock*B τ:=by
    have hq0:0≤(b:ℝ)-τ:=by linarith [ht.2,v.coe_nonneg]
    have hage(ω:Ω):NativeGammaClock.age v b (((b:ℝ)-τ).toNNReal,ω)=τ:=NativeGammaAgeValue.age v b ht ω
    have hcoef(θ:ℝ)(ω:Ω):R θ (((b:ℝ)-τ).toNNReal,ω)=
        NativeFrozenFactorGammaTime.coefficient P Λ κ hκP (fun ω=>embed (OldU ω)) (fun ω=>embed (OldD ω)) θ (hh-τ) ω:=by
      have hw:=NativeGammaAgeValue.window v b ht ω
      have h:=NativeFrozenFactorIdentity.coefficient_eq (Function.uncurry S.first) (Function.uncurry S.second) P Λ κ hκP
        (min_le_right ell (P.lower-κ)) (le_max_right M (P.upper-κ)) v ((b:ℝ)-τ).toNNReal hw.1 θ ω
      simpa only [frozen,Function.uncurry,Real.coe_toNNReal _ hq0,hh,show (b:ℝ)-τ-(v:ℝ)=((b:ℝ)-(v:ℝ))-τ by ring] using h
    unfold integrand
    simp_rw [NativeGammaAgeValue.sharp P v b A P.exponent j ht,hage,hcoef,NativeGammaAgeValue.clock_power ht.1.le,
      show -(ρ-1/2)=1/2-ρ by ring]
    rw [integral_const_mul]
    dsimp only [Cclock,B]
    ring
  have hm:∀ᵐτ∂volume.restrict (Set.Ioc (0:ℝ) hh),τ∈Set.Ioo (0:ℝ) hh:=by
    rw [←restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have he:(G A ρ j)=ᵐ[volume.restrict (Set.Ioc (0:ℝ) hh)] (fun τ=>Cclock*B τ):=by
    filter_upwards [hm] with τ ht
    exact heq τ ht
  refine ⟨(hbase.1.const_mul Cclock).congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_const_mul]
  have hClock:0≤Cclock:=by dsimp only [Cclock];positivity
  have hn:=mul_le_mul_of_nonneg_left hbase.2 hClock
  simp only [sub_zero,zero_sub,abs_neg,abs_one,one_pow,mul_one,embed_norm] at hn
  convert! hn using 1 <;> simp only [constant,Cclock,hh,B] <;> ring
end SHE.MixedNativeFrozenFactorGammaTime
