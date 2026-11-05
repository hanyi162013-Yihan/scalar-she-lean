module

public import SHE.FirstGammaCanonicalReferenceEnergy
public import SHE.NativeRepresentativeEnergy
public import SHE.ConditionalFatouMoment
public import Mathlib.Topology.Order.IsLUB
public import SHE.FirstGammaReferenceEnergy
public import SHE.FirstGammaCanonicalReference
public import SHE.FirstGammaEndpointReferenceHilbert
public import SHE.NativeCanonicalGammaFields
public import SHE.JointInterpolationFields

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.FirstGammaTerminalReferenceEnergy
open MeasureTheory AddCircle GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal Topology
open Filter
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

def reference (b:ℝ≥0) (hbH:b≤H) (θ:ℝ) (z:Ω×HeatCircle):ℝ:=
  PredictableScalarField.nativeField
    (fun ω=>NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP OldU OldD OldUM OldDM
      hbH ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₀ I₁ θ (c,ω)) z

local notation "State" b:max hbH:max ξ:max=>NativeCanonicalReferenceField.state
  𝓕 μ H b v P Λ κ hκ hκP OldU OldD OldUM OldDM hbH
    ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₀ I₁ ξ

/-- The actual full-target reference state converges strongly at its
terminal time along every sequence staying strictly after the past. -/
theorem state_tendsto(b:ℝ≥0) (hbH:b≤H) (hvb:v<b) (ξ:ℝ) (q:ℕ→ℝ≥0)
    (hq:∀n,v<q n) (hqb:Tendsto q atTop (𝓝 b)) (ω:Ω):
    Tendsto (fun n=>(State b hbH ξ) (q n,ω)) atTop (𝓝 ((State b hbH ξ) (b,ω))):=by
  have hb0:0<b:=bot_le.trans_lt hvb
  let Rξ:=FrozenReferenceFields.field P Λ κ ξ hκP v (NativeCanonicalReferenceField.data OldU OldD)
  let hRξ:=FrozenReferenceFields.field_predictable 𝓕 P Λ κ ξ hκP v _
    (NativeCanonicalReferenceField.data_measurable 𝓕 v OldU OldD OldUM OldDM)
  let N:=NativeFrozenHilbertField.noise 𝓕 μ H b v (sub_pos.mpr hκP)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP) Rξ hRξ hbH
    ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₁
  let A:=NativeFrozenHilbertField.noise 𝓕 μ H b v hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH
    ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₀
  let Z:=NativeCanonicalReferenceField.initial (b:=b) (v:=v) (Λ:=Λ) (u:=OldU) (d:=OldD) ξ
  have he(t:ℝ≥0) (ht:v<t):(State b hbH ξ) (t,ω)=Z ω+N t ω+A t ω:=by
    unfold NativeCanonicalReferenceField.state NativeFrozenHilbertField.field
    rw [PredictablePastParameter.held_eq _ _ ht]
  have hN:Tendsto (fun n=>N (q n) ω) atTop (𝓝 (N b ω)):=
    (NativeFrozenHilbertField.noise_continuous 𝓕 μ H b v (sub_pos.mpr hκP)
      (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP) Rξ hRξ hbH _ I₁ hb0 ω).continuousAt.tendsto.comp hqb
  have hA:Tendsto (fun n=>A (q n) ω) atTop (𝓝 (A b ω)):=
    (NativeFrozenHilbertField.noise_continuous 𝓕 μ H b v hκ hκ.le
      (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH _ I₀ hb0 ω).continuousAt.tendsto.comp hqb
  rw [he b hvb]
  exact (((tendsto_const_nhds (x:=Z ω)).add hN).add hA).congr'
    (Eventually.of_forall (fun n=>(he (q n) (hq n)).symm))

include hIJ₀ hIJ₁ hΛ hH hsmall Bpast hBDGpast B hBDG in
/-- The positive-prefix displacement bound passes to the TRUE terminal
reference in the original RealL2 state, by strong continuity and Fatou. -/
theorem state_energy(b:ℝ≥0) (hvb:v<b) (hbH:b≤H)
    (hwindow:(b:ℝ)-(v:ℝ)≤P.horizon) (θ η:ℝ)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (hlocal:StandardTerminalPastLocality I₁) (Bnext:ℝ≥0)
    (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext):
    Integrable (fun ω=>‖(State b hbH θ) (b,ω)-(State b hbH η) (b,ω)‖^2) μ ∧
      (∫ω,‖(State b hbH θ) (b,ω)-(State b hbH η) (b,ω)‖^2 ∂μ)≤
        2*((θ-η)^2+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ θ η 1)*
          (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ):=by
  let C:=2*((θ-η)^2+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ θ η 1)*
    (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)
  obtain ⟨q,hmono,hq,hlim⟩:=exists_seq_strictMono_tendsto' hvb
  have hc(n:ℕ):Integrable (fun ω=>‖(State b hbH θ) (q n,ω)-(State b hbH η) (q n,ω)‖^2) μ ∧
      (∫ω,‖(State b hbH θ) (q n,ω)-(State b hbH η) (q n,ω)‖^2 ∂μ)≤C:=by
    have hqb:(q n:ℝ)≤(b:ℝ):=by exact_mod_cast (hq n).2.le
    have hvq:(v:ℝ)≤(q n:ℝ):=by exact_mod_cast (hq n).1.le
    have he:=FirstGammaCanonicalReferenceEnergy.energy
      (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV)
      (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
      (J:=J) (P:=P) (hκP:=hκP) (hΛ:=hΛ) (v:=v) (c:=q n) (hH:=hH)
      (B:=B) (hBDG:=hBDG) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hsmall:=hsmall)
      (hvc:=(hq n).1) (hcH:=(hq n).2.le.trans hbH)
      (hspan:=by linarith) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
      b (hq n).2 hbH θ η hnull B0 B1 hBDG0 hBDG1 hlocal Bnext hBDGnext
    dsimp only at he
    have heq(ω:Ω):(∫x:HeatCircle,
        (FirstGammaCanonicalReferenceEnergy.reference
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v (q n) hH b hbH θ (ω,x)-
        FirstGammaCanonicalReferenceEnergy.reference
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v (q n) hH b hbH η (ω,x))^2 ∂haarAddCircle)=
          ‖(State b hbH θ) (q n,ω)-(State b hbH η) (q n,ω)‖^2:=
      NativeRepresentativeEnergy.section_energy
        (fun ω=>(State b hbH η) (q n,ω)) (fun ω=>(State b hbH θ) (q n,ω)) ω
    have hi:Integrable (fun ω=>‖(State b hbH θ) (q n,ω)-(State b hbH η) (q n,ω)‖^2) μ:=by
      simpa only [heq] using he.1.integral_prod_left
    refine ⟨hi,?_⟩
    rw [integral_prod _ he.1] at he
    simpa only [heq,C] using he.2
  have hC:0≤C:=(integral_nonneg (fun _=>sq_nonneg _)).trans (hc 0).2
  apply ConditionalFatouMoment.nonnegative_limit μ
    (fun n ω=>‖(State b hbH θ) (q n,ω)-(State b hbH η) (q n,ω)‖^2)
    (fun ω=>‖(State b hbH θ) (b,ω)-(State b hbH η) (b,ω)‖^2)
    (ae_of_all _ (fun ω=>(((state_tendsto 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v hH b hbH hvb θ q
      (fun n=>(hq n).1) hlim ω).sub
      (state_tendsto 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v hH b hbH hvb η q
      (fun n=>(hq n).1) hlim ω)).norm.pow 2)))
    (fun _ _=>sq_nonneg _) (fun _=>sq_nonneg _) hC hc

include hIJ₀ hIJ₁ hΛ hH hsmall Bpast hBDGpast B hBDG in
/-- Actual native scalar displacement energy at q=b. This is the
terminal reference state itself, rather than a positive-age proxy. -/
theorem energy (b:ℝ≥0) (hvb:v<b) (hbH:b≤H)
    (hwindow:(b:ℝ)-(v:ℝ)≤P.horizon) (θ η:ℝ)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (hlocal:StandardTerminalPastLocality I₁) (Bnext:ℝ≥0)
    (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext):
    let f:=fun z=>reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hH b hbH θ z-
      reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hH b hbH η z
    Integrable (fun z=>f z^2) (μ.prod haarAddCircle) ∧
      (∫z,f z^2 ∂μ.prod haarAddCircle)≤
        2*((θ-η)^2+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ θ η 1)*
          (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ):=by
  intro f
  have hb0:0<b:=bot_le.trans_lt hvb
  have hRm(ξ:ℝ):Measurable (fun ω=>(State b hbH ξ) (b,ω)):=
    ((NativeCanonicalReferenceField.state_predictable 𝓕 μ H b v P Λ κ hκ hκP OldU OldD OldUM OldDM
      hbH ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₀ I₁ hb0 hnull B0 B1 hBDG0 hBDG1 ξ).mono
        (predictable_le_product 𝓕)).measurable.comp (measurable_const.prodMk measurable_id)
  have hs:=state_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J P hκP hΛ v hH B hBDG
    hIJ₀ hIJ₁ hsmall Bpast hBDGpast b hvb hbH hwindow θ η hnull B0 B1 hBDG0 hBDG1 hlocal Bnext hBDGnext
  have he:=NativeRepresentativeEnergy.product_energy μ
    (fun ω=>(State b hbH η) (b,ω)) (fun ω=>(State b hbH θ) (b,ω)) (hRm η) (hRm θ) hs.1
  exact ⟨he.1,he.2.trans_le hs.2⟩

end SHE.FirstGammaTerminalReferenceEnergy
