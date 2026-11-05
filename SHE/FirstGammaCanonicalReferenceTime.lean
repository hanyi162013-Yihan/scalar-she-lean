module

public import SHE.FirstGammaCanonicalReferenceEnergy
public import SHE.ScalarHeatGradientOpenTime
public import SHE.ControlledVarianceGammaTime

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.FirstGammaCanonicalReferenceTime
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
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v c : ℝ≥0) (hgap : ∀ i,(c:ℝ)<(Z i).target)


open FirstGammaConstruction
local notation "Rold" => FirstGammaRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S Z hΛ c hgap
local notation "Rnew" => FirstGammaRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S Z P hκP v c hgap
local notation "z₀" => MixedNativePairExtendedMartingale.initial u₀ u₀ (fun i=>(Z i).target) (fun i=>(Z i).center)
local notation "Y" => FirstGammaConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S Z J P hκP hΛ v c hgap
variable (hH : (H:ℝ)≤1) (hH0 : 0<H) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))



local notation "Data"=>MixedPastReference.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v
local notation "DataM"=>MixedPastReference.data_past_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (hvc:v<c) (hcH:c≤H) (hspan:(c:ℝ)-(v:ℝ)≤P.horizon)
variable (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 2 J Bpast)
local notation "hv1"=>(show (v:ℝ)≤1 from
  (show (v:ℝ)≤(H:ℝ) from by exact_mod_cast hvc.le.trans hcH).trans hH)
local notation "Inp" "[" θ "," η "]"=>MixedPastReference.input
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
  P hΛ hκP θ η hsmall v c hvc hcH hv1 hspan 1 (by norm_num) Bpast hBDGpast



local notation "OldU"=>S.first v
local notation "OldD"=>(fun ω=>S.second v ω-S.first v ω)
local notation "OldUM"=>(((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v).measurable)
local notation "OldDM"=>((((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted v).sub
  ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v)).measurable)


variable (b:ℝ≥0) (hvb:v<b) (hbH:b≤H) (hwindow:(b:ℝ)-(v:ℝ)≤P.horizon)

def reference_time (θ:ℝ) (p:ℝ×(Ω×HeatCircle)):ℝ:=
  FirstGammaCanonicalReferenceEnergy.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP
    v ((b:ℝ)-p.1).toNNReal hH b hbH θ p.2

def variance_time (ξ:ℝ):ℝ×(Ω×HeatCircle)→ℝ:=
  ControlledVarianceGammaTime.variance P Λ v b ξ (fun ω=>embed (OldU ω)) (fun ω=>embed (OldD ω))

include hH hvb in
theorem reference_time_measurable
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1) (θ:ℝ):
    Measurable (reference_time 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v hH b hbH θ):=by
  have hb0:0<b:=(show (0:ℝ≥0)≤v from by exact_mod_cast v.coe_nonneg).trans_lt hvb
  have hstate:Measurable (NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP OldU OldD OldUM OldDM
      hbH ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₀ I₁ θ):=
    ((NativeCanonicalReferenceField.state_predictable 𝓕 μ H b v P Λ κ hκ hκP OldU OldD OldUM OldDM
      hbH ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₀ I₁ hb0 hnull B0 B1 hBDG0 hBDG1 θ).mono
        (predictable_le_product 𝓕)).measurable
  have hclock:Measurable (fun p:ℝ×(Ω×HeatCircle)=>((((b:ℝ)-p.1).toNNReal,p.2.1),p.2.2)):=
    ((measurable_real_toNNReal.comp (measurable_const.sub measurable_fst)).prodMk
      measurable_snd.fst).prodMk measurable_snd.snd
  convert! (PredictableScalarField.nativeField_measurable hstate).comp hclock using 1

include hH hΛ hsmall hvb hwindow Bpast hBDGpast B hBDG hIJ₀ hIJ₁ in
/-- The ACTUAL frozen-root gradient difference has the sharp integrated
future-time/band gain and a clip of the true original past energy. Both
means use the SAME original predictable reference processes; all moment,
measurability and variance applicability is derived. -/
theorem energy {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ}
    (hA:0≤A) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (hlocal:StandardTerminalPastLocality I₁) (Bnext:ℝ≥0) (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
    (θ η ξ:ℝ) (j:ℕ):
    let x:=reference_time 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v hH b hbH θ
    let y:=reference_time 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v hH b hbH η
    let σ:=variance_time 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v b ξ
    let g:=fun p=>deriv (ScalarGaussianSemigroup.heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (y p)-
      deriv (ScalarGaussianSemigroup.heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (x p)
    let r:=CompactMollifier.radius (j+1)
    let E:=2*((θ-η)^2+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ θ η 1)*
      (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)
    IntegrableOn (fun t=>t^(ρ-1/2)*(∫z,|g (t,z)|^2 ∂μ.prod haarAddCircle)) (Set.Ioc 0 ((b:ℝ)-(v:ℝ))) ∧
      (∫t in Set.Ioc 0 ((b:ℝ)-(v:ℝ)),t^(ρ-1/2)*(∫z,|g (t,z)|^2 ∂μ.prod haarAddCircle))≤
        (2*A*ScalarHeatGradientDifference.constant P.exponent)^2*ScalarHeatBandTime.massConstant P.exponent ρ*
          (ProfileVariance.lowerConstant*P.lower)^(-1-2*ρ)*r^(2*P.exponent+4*ρ)*min 1 (E/r^2):=by
  intro x y σ g r E
  have hu:Measurable (fun ω=>embed (OldU ω)):=embed.continuous.measurable.comp ((OldUM).mono (𝓕.le v) le_rfl)
  have hd:Measurable (fun ω=>embed (OldD ω)):=embed.continuous.measurable.comp ((OldDM).mono (𝓕.le v) le_rfl)
  have hσm:Measurable σ:=ControlledVarianceGammaTime.variance_measurable P Λ v b ξ _ _ hu hd
  have hxm:=reference_time_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v hH b hvb hbH
    hnull B0 B1 hBDG0 hBDG1 θ
  have hym:=reference_time_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v hH b hvb hbH
    hnull B0 B1 hBDG0 hBDG1 η
  have hclocks(t:ℝ)(ht:t∈Set.Ioo 0 ((b:ℝ)-(v:ℝ))):
      (((b:ℝ)-t).toNNReal:ℝ)=(b:ℝ)-t ∧ v<((b:ℝ)-t).toNNReal ∧ ((b:ℝ)-t).toNNReal<b:=by
    have h0:0≤(b:ℝ)-t:=by linarith [v.coe_nonneg,ht.2]
    have he:=Real.coe_toNNReal _ h0
    refine ⟨he,?_,?_⟩
    · exact_mod_cast (show (v:ℝ)<(((b:ℝ)-t).toNNReal:ℝ) by rw [he];linarith [ht.2])
    · exact_mod_cast (show (((b:ℝ)-t).toNNReal:ℝ)<(b:ℝ) by rw [he];linarith [ht.1])
  have hdi(t:ℝ)(ht:t∈Set.Ioo 0 ((b:ℝ)-(v:ℝ))):
      Integrable (fun z=>(y (t,z)-x (t,z))^2) (μ.prod haarAddCircle) ∧
        (∫z,(y (t,z)-x (t,z))^2 ∂μ.prod haarAddCircle)≤E:=by
    rcases hclocks t ht with ⟨hq,hvq,hqb⟩
    have hqH:=hqb.le.trans hbH
    have hqspan:(((b:ℝ)-t).toNNReal:ℝ)-(v:ℝ)≤P.horizon:=by rw [hq];linarith [ht.1,hwindow]
    have he:=FirstGammaCanonicalReferenceEnergy.energy (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
      (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀)
      (S:=S) (J:=J) (P:=P) (hκP:=hκP) (hΛ:=hΛ) (v:=v) (c:=((b:ℝ)-t).toNNReal) (hH:=hH)
      (B:=B) (hBDG:=hBDG) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hsmall:=hsmall) (hvc:=hvq) (hcH:=hqH)
      (hspan:=hqspan) (Bpast:=Bpast) (hBDGpast:=hBDGpast) b hqb hbH η θ hnull B0 B1 hBDG0 hBDG1 hlocal Bnext hBDGnext
    simpa only [x,y,reference_time,E,sub_sq_comm,PastReferenceBracket.energyConstant,sub_sq_comm] using he
  have hlo(t:ℝ)(ht:t∈Set.Ioo 0 ((b:ℝ)-(v:ℝ))):
      ∀ᵐz:Ω×HeatCircle∂μ.prod haarAddCircle,ProfileVariance.lowerConstant*P.lower*Real.sqrt t≤σ (t,z):=by
    apply ae_of_all
    intro z
    have heq:σ (t,z)=ControlledScalarCovarianceTail.tail P Λ v ((b:ℝ)-t) b ξ (embed (OldU z.1)) (embed (OldD z.1)) z.2:=by
      dsimp only [σ,variance_time,ControlledVarianceGammaTime.variance,ControlledScalarCovarianceTailEnergy.field]
      rw [min_eq_left (by linarith [ht.1] : (b:ℝ)-t≤(b:ℝ))]
    rw [heq]
    have hc:Measurable (fun w:ControlledProfile.Domain=>ControlledProfile.profile P Λ
        (embed (OldU z.1)) (embed (OldD z.1)) (ξ,(w.1-(v:ℝ),w.2))):=
      (ControlledProfile.profile_measurable P Λ (embed (OldU z.1)) (embed (OldD z.1))).comp
        (measurable_const.prodMk ((measurable_fst.sub_const (v:ℝ)).prodMk measurable_snd))
    have he:=ScalarCovarianceTailScale.elliptic hc (by linarith [ht.1] : (b:ℝ)-t<(b:ℝ))
      (by linarith [ht.2,P.horizon_le_one,hwindow]) P.lower_pos.le P.upper_nonneg
      (fun w=>ControlledProfile.profile_bounds P Λ (embed (OldU z.1)) (embed (OldD z.1)) _) z.2
    simpa only [show (b:ℝ)-((b:ℝ)-t)=t by ring,Real.sqrt_eq_rpow,ControlledScalarCovarianceTail.tail] using he.1
  have hE:0≤E:=by
    have he:=PastReferenceBracket.energyConstant_nonneg P hκP (by norm_num : (0:ℝ)≤1) θ η
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (mul_nonneg Bnext.coe_nonneg he)))
      (integral_nonneg (fun _=>sq_nonneg _))
  exact ScalarHeatGradientOpenTime.energy (μ.prod haarAddCircle) ha hA P.exponent_pos.le P.exponent_le_one
    hρ0 hρ1 (mul_pos ProfileVariance.lowerConstant_pos P.lower_pos) hE hholder σ x y hσm hxm hym hlo
    (fun t ht=>(hdi t ht).1) (fun t ht=>(hdi t ht).2) j

end SHE.FirstGammaCanonicalReferenceTime
