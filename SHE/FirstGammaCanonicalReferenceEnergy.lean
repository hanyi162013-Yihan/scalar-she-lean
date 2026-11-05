module

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

namespace SHE.FirstGammaCanonicalReferenceEnergy
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

def reference (b:ℝ≥0) (hbH:b≤H) (θ:ℝ) (z:Ω×HeatCircle):ℝ:=
  PredictableScalarField.nativeField
    (fun ω=>NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP OldU OldD OldUM OldDM
      hbH ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₀ I₁ θ (c,ω)) z

include hIJ₀ hIJ₁ hΛ hH hsmall hvc hcH hspan Bpast hBDGpast B hBDG in
/-- ACTUAL jointly predictable canonical reference roots have the uniform
original sample/native-space displacement budget. Finite-Ito endpoint,
same-driver reference input, original moments and scalar field versions
are all identified, rather than supplied as applicability hypotheses. -/
theorem energy (b:ℝ≥0) (hcb:c<b) (hbH:b≤H) (θ η:ℝ)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (hlocal:StandardTerminalPastLocality I₁) (Bnext:ℝ≥0)
    (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext):
    let f:=fun z=>reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v c hH b hbH θ z-
      reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v c hH b hbH η z
    Integrable (fun z=>f z^2) (μ.prod haarAddCircle) ∧
      (∫z,f z^2 ∂μ.prod haarAddCircle)≤
        2*((θ-η)^2+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ θ η 1)*
          (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ):=by
  intro f
  have hb0:0<b:=(show (0:ℝ≥0)≤v from by exact_mod_cast v.coe_nonneg).trans_lt (hvc.trans hcb)
  have hHpos:0<H:=hb0.trans_le hbH
  let g:=fun z:Ω×HeatCircle=>((θ-η)*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))*
    functional ((b:ℝ)-(v:ℝ)) z.2 (OldD z.1)+
    functional ((b:ℝ)-(c:ℝ)) z.2 (I₁.integral (Inp[θ,η]) z.1)
  have he:=FirstGammaReferenceEnergy.uniform_energy (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hκP:=hκP)
    (hΛ:=hΛ) (v:=v) (c:=c) (hH:=hH) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
    (hsmall:=hsmall) (hvc:=hvc) (hcH:=hcH) (hspan:=hspan)
    (Bpast:=Bpast) (hBDGpast:=hBDGpast) b hcb θ η hlocal Bnext hBDGnext Set.univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at he
  have hRm(ξ:ℝ):Measurable (reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v c hH b hbH ξ):=by
    apply PredictableScalarField.nativeField_measurable
    exact ((NativeCanonicalReferenceField.state_predictable 𝓕 μ H b v P Λ κ hκ hκP OldU OldD OldUM OldDM
      hbH ((show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH) I₀ I₁ hb0 hnull B0 B1 hBDG0 hBDG1 ξ).mono
        (predictable_le_product 𝓕)).measurable.comp (measurable_const.prodMk measurable_id)
  have hDm:Measurable OldD:=MixedHeatedDifferenceMoments.difference_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v
  have hg:Measurable g:=by
    have hm1:=functional_joint_measurable.comp
      ((hDm.comp measurable_fst).prodMk ((measurable_const (a:=(b:ℝ)-(v:ℝ))).prodMk measurable_snd))
    have hm2:=functional_joint_measurable.comp
      (((Lp.stronglyMeasurable (I₁.integral (Inp[θ,η]))).measurable.comp measurable_fst).prodMk
        ((measurable_const (a:=(b:ℝ)-(c:ℝ))).prodMk measurable_snd))
    exact (hm1.const_mul _).add hm2
  have hcan(ξ:ℝ):∀ᵐx:HeatCircle∂haarAddCircle,∀ᵐω∂μ,
      FirstGammaAffine.reference 1 Λ ξ (fun _=>(b:ℝ))
        (FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
          (ScalarCovarianceTailScale.observation b x) J P hκP hΛ v b (fun _=>le_rfl) hbH ξ (c,ω)) 0=
      reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v c hH b hbH ξ (ω,x):=by
    exact FirstGammaCanonicalReference.reference_eq_field
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J P hκP hΛ v c hH B hBDG hIJ₀ hIJ₁
      b hcb hbH hvc B0 B1 hBDG0 hBDG1 ξ
  have hx:∀ᵐx:HeatCircle∂haarAddCircle,∀ᵐω∂μ,f (ω,x)=g (ω,x):=by
    filter_upwards [hcan θ,hcan η] with x hθ hη
    let Zx:=ScalarCovarianceTailScale.observation (b:ℝ) x
    have hgapx:∀i,(c:ℝ)<(Zx i).target:=fun _=>by exact_mod_cast hcb
    have hf:=FirstGammaEndpointReferenceHilbert.reference_difference
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S Zx J P hκP hΛ v c hgapx
      hH hHpos B hBDG hIJ₀ hIJ₁ hsmall hvc hcH hspan Bpast hBDGpast b (fun _=>le_rfl) hbH hcb.le hb0 θ η
    filter_upwards [hθ,hη,hf] with ω hθ hη hf
    dsimp only [f]
    rw [←hθ,←hη]
    simpa only [Zx,ScalarCovarianceTailScale.observation] using hf 0
  have hset:MeasurableSet {z:Ω×HeatCircle|f z=g z}:=
    measurableSet_eq_fun ((hRm θ).sub (hRm η)) hg
  have hae:∀ᵐz:Ω×HeatCircle∂μ.prod haarAddCircle,f z=g z:=
    (Measure.ae_prod_iff_ae_ae hset).mpr ((Measure.ae_ae_comm hset).mpr hx)
  have hsq:∀ᵐz:Ω×HeatCircle∂μ.prod haarAddCircle,f z^2=g z^2:=hae.mono (fun _ hz=>congrArg (fun t:ℝ=>t^2) hz)
  refine ⟨he.1.congr (hsq.mono (fun _ hz=>hz.symm)),?_⟩
  rw [integral_congr_ae hsq]
  exact he.2

end SHE.FirstGammaCanonicalReferenceEnergy
