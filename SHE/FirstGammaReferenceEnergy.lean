module

public import SHE.ReferenceBracketUniform
public import SHE.NativeReferenceProductEnergy
public import SHE.FirstGammaReferenceHilbert
public import SHE.FirstGammaFrozenDifference
public import SHE.PastReferenceScalarStopped
public import SHE.MixedPastReferenceDampedMoment
public import SHE.FirstGammaFrozenValues
public import SHE.FirstGammaEndpointPhysical
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.FirstGammaRows
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaValues
public import SHE.FiniteReferenceSpliceRows
public import SHE.MixedNativeFrozenInterpolationRows
public import SHE.MixedNativeFrozenPrefixValues
public import SHE.FiniteReferenceSplicePast
public import SHE.StoppedInputAlgebra
public import SHE.PastFrozenPrefixRows
public import SHE.MixedPastJointData
public import SHE.FiniteReferenceSplice
public import SHE.MixedNativeJointPhysical
public import SHE.MixedNativePairMartingale
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.FirstGammaReferenceEnergy
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


/-- The literal compatible reference root field on original sample and
native space, for any positive future target b-c. -/
def field (b:ℝ≥0) (θ η:ℝ) (z:Ω×HeatCircle):ℝ:=
  ((θ-η)*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))*
    functional ((b:ℝ)-(v:ℝ)) z.2 (S.second v z.1-S.first v z.1)+
  functional ((b:ℝ)-(c:ℝ)) z.2 (I₁.integral (Inp[θ,η]) z.1)


include hIJ₀ hIJ₁ in
/-- The ACTUAL reference displacement has genuine original sample/space
L2 on EVERY original past event. Its random past norm stays inside the
conditional estimate. The sharp compatible frozen-noise time gain is
derived from ordinary BDG/locality, never assumed as a reference model. -/
theorem actual_energy (b:ℝ≥0) (hcb:c<b) (θ η:ℝ)
    (hlocal:StandardTerminalPastLocality I₁) (Bnext:ℝ≥0)
    (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
    (A:Set Ω) (hA:MeasurableSet[𝓕 v] A):
    let f:=fun z:Ω×HeatCircle=>((θ-η)*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))*
      functional ((b:ℝ)-(v:ℝ)) z.2 (S.second v z.1-S.first v z.1)+
      functional ((b:ℝ)-(c:ℝ)) z.2 (I₁.integral (Inp[θ,η]) z.1)
    Integrable (fun z=>f z^2) ((μ.restrict A).prod haarAddCircle) ∧
      (∫z,f z^2 ∂(μ.restrict A).prod haarAddCircle)≤
        2*(((θ-η)*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))^2+
          (Bnext:ℝ)*PastReferenceBracket.energyConstant P κ θ η ((c:ℝ)-(v:ℝ)))*
          (∫ω in A,‖S.second v ω-S.first v ω‖^2 ∂μ):=by
  intro f
  have hd:=MixedPastReference.data_moments 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ v (hvc.le.trans hcH) hv1 (p:=1) (by norm_num) Bpast hBDGpast
  have hdi:Integrable (fun ω=>‖S.second v ω-S.first v ω‖^2) μ:=by
    simpa only [MixedPastReference.data,embed_norm] using hd.1
  have hn:=MixedPastReference.actual_moment
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P hΛ hκP θ η hsmall v c hvc hcH hv1 hspan 1 (by norm_num) Bpast hBDGpast
    hlocal Bnext hBDGnext A hA
  simp only [Nat.mul_one,pow_one] at hn
  have hmD:Measurable (fun ω=>S.second v ω-S.first v ω):=
    MixedHeatedDifferenceMoments.difference_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v
  have he:=NativeReferenceProductEnergy.energy (μ.restrict A)
    (sub_nonneg.mpr (by exact_mod_cast hvc.le)) (sub_pos.mpr (by exact_mod_cast hcb))
    ((θ-η)*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))
    (fun ω=>S.second v ω-S.first v ω) (I₁.integral (Inp[θ,η])) hmD
    (Lp.stronglyMeasurable _).measurable hdi.integrableOn hn.1
  have hif:=he.1
  have hbf:=he.2
  have hage:((c:ℝ)-(v:ℝ))+((b:ℝ)-(c:ℝ))=(b:ℝ)-(v:ℝ):=by ring
  have hif':Integrable (fun z=>f z^2) ((μ.restrict A).prod haarAddCircle):=by
    convert! hif using 1
    funext z
    dsimp only [f]
    exact congrArg (fun t:ℝ=>(((θ-η)*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))*
      functional t z.2 (S.second v z.1-S.first v z.1)+
      functional ((b:ℝ)-(c:ℝ)) z.2 (I₁.integral (Inp[θ,η]) z.1))^2) hage.symm
  have hbf':(∫z,f z^2 ∂(μ.restrict A).prod haarAddCircle)≤
      2*(((θ-η)*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))^2)*
        (∫ω in A,‖S.second v ω-S.first v ω‖^2 ∂μ)+
      2*(∫ω in A,‖I₁.integral (Inp[θ,η]) ω‖^2 ∂μ):=by
    convert! hbf using 1
    congr 1
    funext z
    dsimp only [f]
    exact congrArg (fun t:ℝ=>(((θ-η)*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))*
      functional t z.2 (S.second v z.1-S.first v z.1)+
      functional ((b:ℝ)-(c:ℝ)) z.2 (I₁.integral (Inp[θ,η]) z.1))^2) hage.symm
  refine ⟨hif',hbf'.trans ?_⟩
  calc
    _≤2*(((θ-η)*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))^2)*
        (∫ω in A,‖S.second v ω-S.first v ω‖^2 ∂μ)+
        2*((Bnext:ℝ)*PastReferenceBracket.energyConstant P κ θ η ((c:ℝ)-(v:ℝ))*
          (∫ω in A,‖S.second v ω-S.first v ω‖^2 ∂μ)):=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hn.2 (by norm_num))
    _=_:=by ring

include hIJ₀ hIJ₁ in
/-- A uniform compatible-reference root budget, independent of damping
and the current/future clocks in the unit horizon. -/
theorem uniform_energy (b:ℝ≥0) (hcb:c<b) (θ η:ℝ)
    (hlocal:StandardTerminalPastLocality I₁) (Bnext:ℝ≥0)
    (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
    (A:Set Ω) (hA:MeasurableSet[𝓕 v] A):
    let f:=fun z:Ω×HeatCircle=>((θ-η)*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))*
      functional ((b:ℝ)-(v:ℝ)) z.2 (S.second v z.1-S.first v z.1)+
      functional ((b:ℝ)-(c:ℝ)) z.2 (I₁.integral (Inp[θ,η]) z.1)
    Integrable (fun z=>f z^2) ((μ.restrict A).prod haarAddCircle) ∧
      (∫z,f z^2 ∂(μ.restrict A).prod haarAddCircle)≤
        2*((θ-η)^2+(Bnext:ℝ)*PastReferenceBracket.energyConstant P κ θ η 1)*
          (∫ω in A,‖S.second v ω-S.first v ω‖^2 ∂μ):=by
  intro f
  have he:=actual_energy (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ)
    (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (P:=P) (hκP:=hκP)
    (hΛ:=hΛ) (v:=v) (c:=c) (hH:=hH) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁)
    (hsmall:=hsmall) (hvc:=hvc) (hcH:=hcH) (hspan:=hspan)
    (Bpast:=Bpast) (hBDGpast:=hBDGpast) b hcb θ η hlocal Bnext hBDGnext A hA
  have hdamp:=ReferenceBracketUniform.damped_square_le (a:=θ-η) hΛ
    (sub_nonneg.mpr (by exact_mod_cast (hvc.le.trans hcb.le)))
  have hc0:0≤(c:ℝ)-(v:ℝ):=sub_nonneg.mpr (by exact_mod_cast hvc.le)
  have hc1:(c:ℝ)-(v:ℝ)≤1:=by
    have hc:(c:ℝ)≤(H:ℝ):=by exact_mod_cast hcH
    linarith [v.coe_nonneg]
  have hbr:=ReferenceBracketUniform.energy_constant_le P hκP hc0 hc1 θ η
  have hp:0≤∫ω in A,‖S.second v ω-S.first v ω‖^2 ∂μ:=
    integral_nonneg (fun ω=>sq_nonneg _)
  refine ⟨he.1,he.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (add_le_add hdamp (mul_le_mul_of_nonneg_left hbr Bnext.coe_nonneg)) (by norm_num)) hp

end SHE.FirstGammaReferenceEnergy
