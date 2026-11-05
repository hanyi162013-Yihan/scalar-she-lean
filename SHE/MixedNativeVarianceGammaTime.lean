module

public import SHE.NativeCanonicalGammaFields
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

namespace SHE.MixedNativeVarianceGammaTime
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

def variance (ξ:ℝ):ℝ×(Ω×HeatCircle)→ℝ:=
  ControlledVarianceGammaTime.variance P Λ v b ξ (fun ω=>embed (OldU ω)) (fun ω=>embed (OldD ω))
local notation "Var"=>variance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b

def currentMean (p:ℝ×(Ω×HeatCircle)):ℝ:=
  NativeCanonicalGammaFields.current (v:=v) (b:=b) (U:=Function.uncurry S.first) (V:=Function.uncurry S.second)
    (Λ:=Λ) 1 ((((b:ℝ)-p.1).toNNReal,p.2.1),p.2.2)

def referenceMean (p:ℝ×(Ω×HeatCircle)):ℝ:=
  PredictableScalarField.nativeField
    (NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP OldU OldD OldUM OldDM hbH hb1 I₀ I₁ 1)
      ((((b:ℝ)-p.1).toNNReal,p.2.1),p.2.2)

theorem ageClock_measurable : Measurable (fun p:ℝ×(Ω×HeatCircle)=>
    ((((b:ℝ)-p.1).toNNReal,p.2.1),p.2.2)):=
  ((measurable_real_toNNReal.comp (measurable_const.sub measurable_fst)).prodMk measurable_snd.fst).prodMk measurable_snd.snd

theorem currentMean_measurable :Measurable (currentMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v b):=by
  have hs:Measurable (NativeCorrectedCurrentFields.state (Function.uncurry S.first) (Function.uncurry S.second) Λ 1 v b):=
    ((NativeCorrectedCurrentFields.state_predictable 𝓕 _ _ S.first_predictable S.second_predictable Λ 1 v b).mono
      (predictable_le_product 𝓕)).measurable
  exact (PredictableScalarField.nativeField_measurable hs).comp (ageClock_measurable (Ω:=Ω) b)

include hvb in
theorem referenceMean_measurable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1):
    Measurable (referenceMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hbH hH):=by
  have hb0:0<b:=(show (0:ℝ≥0)≤v from zero_le).trans_lt hvb
  have hs:Measurable (NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP OldU OldD OldUM OldDM hbH hb1 I₀ I₁ 1):=
    ((NativeCanonicalReferenceField.state_predictable 𝓕 μ H b v P Λ κ hκ hκP OldU OldD OldUM OldDM hbH hb1 I₀ I₁
      hb0 hnull B0 B1 hBDG0 hBDG1 1).mono (predictable_le_product 𝓕)).measurable
  exact (PredictableScalarField.nativeField_measurable hs).comp (ageClock_measurable (Ω:=Ω) b)

def constant (A ρ:ℝ):ℝ:=
  let p:=(P.exponent-1)/2
  (((1/2:ℝ)*A*ScalarHeatBandEnvelope.constant P.exponent 2)^2)*
    (((1/2:ℝ)^p)*(1/(ρ+3/2)+1/(1-P.exponent/2-ρ))+2/(p+1))*
    (ProfileVariance.lowerConstant*P.lower)^(-3-2*ρ)*(ControlledScalarCovarianceTail.constant P)^2

def gradient (a:ℝ→ℝ) (j:ℕ) (m:ℝ×(Ω×HeatCircle)→ℝ) (p:ℝ×(Ω×HeatCircle)):ℝ:=
  deriv (ScalarGaussianSemigroup.heat (Var 0 p).toNNReal (ScalarHeatBands.band a (j+1))) (m p)-
    deriv (ScalarGaussianSemigroup.heat (Var 1 p).toNNReal (ScalarHeatBands.band a (j+1))) (m p)
local notation "Grad"=>gradient 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b

include hIJ₀ hIJ₁ hΛ hH hvb hbH hwindow hsmall hBDGpast in
/-- The actual solution supplies all past moments. BOTH variance-change
slots allow the actual dependent current/reference mean. Their precise
band/time power is derived from the true own-profile covariance tails. -/
theorem scalar_energy {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ}
    (hA:0≤A) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
    (m:ℝ×(Ω×HeatCircle)→ℝ) (hm:Measurable m) (j:ℕ):
    IntegrableOn (fun t=>t^(ρ-1/2)*(∫z,|Grad a j m (t,z)|^2 ∂μ.prod haarAddCircle)) (Set.Ioc 0 ((b:ℝ)-(v:ℝ))) ∧
      (∫t in Set.Ioc 0 ((b:ℝ)-(v:ℝ)),t^(ρ-1/2)*(∫z,|Grad a j m (t,z)|^2 ∂μ.prod haarAddCircle))≤
        constant P A ρ*(CompactMollifier.radius (j+1))^(2*P.exponent+4*ρ)*
          ((b:ℝ)-(v:ℝ))^((P.exponent-1)/2)*(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ):=by
  have hu:Measurable (fun ω=>embed (OldU ω)):=embed.continuous.measurable.comp ((OldUM).mono (𝓕.le v) le_rfl)
  have hd:Measurable (fun ω=>embed (OldD ω)):=embed.continuous.measurable.comp ((OldDM).mono (𝓕.le v) le_rfl)
  have hv1:(v:ℝ)≤1:=(show (v:ℝ)≤(H:ℝ) from by exact_mod_cast hvb.le.trans hbH).trans hH
  have hi:=MixedPastReference.data_moments 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    hΛ v (hvb.le.trans hbH) hv1 (p:=1) (by norm_num) Bpast hBDGpast
  have hi':Integrable (fun ω=>‖embed (OldD ω)‖^2) μ:=by
    simpa only [MixedPastReference.data] using hi.1
  have he:=ControlledVarianceGammaTime.actual_energy P μ hΛ (show (v:ℝ)<(b:ℝ) by exact_mod_cast hvb)
    hwindow hρ0 hρ1 hsmall (fun ω=>embed (OldU ω)) (fun ω=>embed (OldD ω)) hu hd hi' 1 0 ha hA hholder m hm j
  dsimp only at he
  simp only [sub_zero,abs_one,one_pow,mul_one,embed_norm] at he
  convert! he using 1 <;> dsimp only [constant,gradient,variance] <;> ring

end SHE.MixedNativeVarianceGammaTime
