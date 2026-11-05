module

public import SHE.PhysicalMeanEnergy
public import SHE.TwoFreshThetaWordFields
public import SHE.NativeCurrentMeanAverage
public import SHE.MixedNativeDampedScoreAmplitude
public import SHE.MixedPastNativePacketBounds
public import SHE.MixedPastNativePacketUniform
public import SHE.NativeCurrentCapInterpolation
public import SHE.NativePacketEnvelope
public import SHE.MixedPastNativeFirstWholeCompleteWeights
public import SHE.MixedPastTwoFreshCompleteWeights
public import SHE.ControlledFutureFields
public import SHE.SectionEnergy
public import SHE.NativeFirstWholeComplete
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedPastJointData
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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeMeanCap
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeMeanCap_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeMeanCap_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeMeanCap_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeMeanCap_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeMeanCap_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeMeanCap_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedPastNativeMeanCap_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω]
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


local instance mixedPastNativeMeanCap_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeMeanCap_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  NativeFirstWholeMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

/-- The actual theta-averaged current-mean packet has the distinguished
Dcur amplitude, with one common consistent endpoint cap. Theta
integrability is derived; the stochastic current is never a fixed input. -/
theorem cap (P:CanonicalCovariance.ProfileParameters) (hΛ:0≤Λ) (v q:ℝ≥0) (hvq:v≤q)
    (target:Fin n→ℝ) (a:Fin n→UnitAddCircle)
    (hgap:∀i,(q:ℝ)-(v:ℝ)<target i) (ht1:∀i,target i≤1)
    (lo hi:Fin r→ℝ) (hlo:∀j,(q:ℝ)-(v:ℝ)≤lo j) (hlohi:∀j,lo j<hi j)
    (hstop:∀j i,target i≤lo j ∨ hi j≤target i)
    (hdisjoint:∀j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (leaf:Fin m→Fin n) (ht:∀j,target (leaf j)∈Set.Ioc 0 P.horizon)
    (D:Fin r→State n) (E:State n) (z:Ω×UnitAddCircle)
    (hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance target target (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2))
        (referenceProfile P Λ
          (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v z.1)
          (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v z.1)) lo hi j)).range)
    (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P target target
      (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2)) ((q:ℝ)-(v:ℝ)))).range)
    (g:Fin d→Fin n) (F:State d→ℝ) (hFm:Measurable F) {A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν)
    (hf:ContDiff ℝ r F) (hfb:∀j,j≤r→∀w,‖iteratedFDeriv ℝ j F w‖≤A0*ν^j)
    (p:ℕ) (hp:0<p) (K:ℝ) (hK:0≤K)
    (hgeom:|(∏j,scoreVariance (familyCovariance target target
      (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2))
      (referenceProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v z.1)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v z.1)) lo hi j) (D j))*
      Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P target target
        (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2)) ((q:ℝ)-(v:ℝ))) E)|≤K):
    let U:=MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v z.1
    let Dir:=MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v z.1
    let center:=StoppedGaussianScore.nativeCenter (fun i=>a i+z.2)
    let mean:=fun θ=>MixedPastNativePacketEnergy.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      v q target target a (θ,z)
    let V:=PhysicalMeanRange.dampedDirection target target (fun i=>a i+z.2) ((q:ℝ)-(v:ℝ)) Λ
      (embed (S.second q z.1-S.first q z.1))
    let MP:=fun θ=>TwoFreshCompleteWord.value P Λ U Dir θ ((q:ℝ)-(v:ℝ)) target target center lo hi
      (mean θ) false D E V g leaf F
    let T:=MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν
    let G:=MixedPastNativePacketUniform.packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      (r:=r) P v q target target a leaf p z
    let Dcur:=MixedNativeDampedScoreAmplitude.amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P v q target a lo hi z
    let WP:=fun θ=>NativeFirstWholeComplete.value P Λ U Dir θ ((q:ℝ)-(v:ℝ)) target target center lo hi
      (mean θ) D E g leaf F
    Integrable MP MixedNativeDampedScoreAmplitude.thetaMeasure ∧
      |∫θ,MP θ ∂MixedNativeDampedScoreAmplitude.thetaMeasure|≤(K*T)*Dcur*G ∧
      |WP 1-WP 0|≤2*(K*T)*G:=by
  intro U Dir center mean V MP T G Dcur WP
  let τ:=MixedNativeDampedScoreAmplitude.thetaMeasure
  let qr:ℝ:=(q:ℝ)-(v:ℝ)
  have hqr:0≤qr:=sub_nonneg.mpr (by exact_mod_cast hvq)
  have ht0(i:Fin n):0<target i:=hqr.trans_lt (hgap i)
  obtain ⟨δ,hδ,hδt⟩:=PhysicalMeanRange.exists_positive_gap (fun i=>target i-qr) (fun i=>sub_pos.mpr (hgap i))
  have hmin(i:Fin n):qr+δ≤target i:=by linarith [hδt i]
  let old:=fixedProfile P Λ U Dir lo hi
  let C:=fun θ=>ControlledFixedReserve.covariance P Λ U Dir (NativeFirstScoreReserve.oldProfile P old)
    target target center qr θ
  let c:=fun θ=>ControlledFixedReserve.coefficient P Λ U Dir (NativeFirstScoreReserve.oldProfile P old) θ
  have hold:Measurable old:=fixedProfile_measurable P Λ U Dir lo hi
  have holdb:=fixedProfile_bounds P Λ U Dir lo hi hdisjoint
  have hc(θ:ℝ):Measurable (c θ):=
    ((ControlledProfile.profile_measurable P Λ U Dir).comp (measurable_const.prodMk measurable_id)).sub
      (NativeFirstScoreReserve.oldProfile_measurable P hold)
  have hfloor:0<3*P.lower/8:=by have:=P.lower_pos;positivity
  have hcb(θ:ℝ)(x:ControlledProfile.Domain):3*P.lower/8≤c θ x ∧ c θ x≤P.upper:=
    NativeFirstScoreReserve.residual_bounds P Λ U Dir holdb θ x
  have hV(θ:ℝ):V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (C θ)).range:=
    PhysicalMeanRange.dampedDirection_mem_range target target (fun i=>a i+z.2) qr Λ hΛ
      (fun _=>le_rfl) δ hδ hmin (c θ) (hc θ) P.upper (3*P.lower/8)
      (fun x=>⟨hfloor.le.trans (hcb θ x).1,(hcb θ x).2⟩) hfloor (fun x=>(hcb θ x).1) _
  let score:=fun θ=>scoreVariance (C θ) V
  have hs0(θ:ℝ):0≤score θ:=scoreVariance_nonneg
    (NativeFirstScoreRepresentation.residual_posSemidef P Λ U Dir old hold holdb target target center
      (fun _=>le_rfl) qr θ) (hV θ)
  have hscore:Measurable score:=by
    have hC:Measurable C:=by
      convert! StoppedGaussianFields.covariance_measurable
        (VaryingControlledGaussianFields.family (Ω:=ℝ) target target center)
        ((ControlledProfile.profile_measurable P Λ U Dir).sub
          ((NativeFirstScoreReserve.oldProfile_measurable P hold).comp measurable_snd))
        (measurable_const (a:=qr)) using 1
    have hpair:Measurable (fun θ:ℝ=>(C θ,V)):=hC.prodMk measurable_const
    have hh:=scoreVariance_measurable.comp hpair
    convert! hh using 1
  have hsi:Integrable score τ:=(integrable_const (((2/δ)/(3*P.lower/8))*‖embed (S.second q z.1-S.first q z.1)‖^2)).mono'
    hscore.aestronglyMeasurable (ae_of_all _ (fun θ=>by
      rw [Real.norm_of_nonneg (hs0 θ)]
      exact PhysicalMeanEnergy.damped_score_bound target target (fun i=>a i+z.2) qr Λ hΛ
        (fun _=>le_rfl) δ hδ hmin (c θ) (hc θ) P.upper (3*P.lower/8)
        (fun x=>⟨hfloor.le.trans (hcb θ x).1,(hcb θ x).2⟩) hfloor (fun x=>(hcb θ x).1) _))
  have hm:Measurable mean:=by
    have hh:=(MixedPastNativePacketEnergy.meanField_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v q target target a hgap).comp
        (measurable_id.prodMk (measurable_const (a:=z)))
    convert! hh using 1
  have hMP:Measurable MP:=TwoFreshThetaWordFields.value_measurable P Λ U Dir qr target target center lo hi
    mean hm false D E V g leaf F hFm
  have hGn:0≤G:=Real.rpow_nonneg (MixedPastNativePacketUniform.envelope_nonneg
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P v q target target a leaf (fun j=>(ht j).1) p z) _
  have hT:0≤T:=MixedPastWordMoments.total_nonneg P lo hi _ A0 ν
  have hb(θ:ℝ)(hθ:θ∈Set.Icc (0:ℝ) 1):|WP θ|≤G*(K*T) ∧ |MP θ|≤G*(K*T*Real.sqrt (score θ)):=
    MixedPastNativePacketBounds.whole_and_mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P v q hvq θ hθ target target a ht0 ht1 (fun _=>le_rfl) lo hi hlo hlohi hstop hdisjoint
      leaf (fun _=>rfl) ht D E V z hD hE (hV θ) g F hFm hA0 hν hf hfb p hp K hK hgeom
  have hmean:=NativeCurrentMeanAverage.mean_cap τ MP score hMP hscore hsi hs0 (mul_nonneg hK hT) hGn
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
        have hh:θ∈Set.Icc (0:ℝ) 1:=⟨hθ.1.le,hθ.2⟩
        exact (hb θ hh).2.trans_eq (by ring))
  refine ⟨hmean.1,?_,?_⟩
  · convert! hmean.2 using 1
  · exact (abs_sub _ _).trans (by
      have h1:|WP 1|≤G*(K*T):=(hb 1 (by norm_num)).1
      have h0:|WP 0|≤G*(K*T):=(hb 0 (by norm_num)).1
      nlinarith)

/-- Fractional current gain for the literal consistent endpoint change.
The remaining term is exactly endpoint minus current-mean integral, ready
for the physical covariance-plus-baseline FTC identity. -/
theorem clipped (P:CanonicalCovariance.ProfileParameters) (hΛ:0≤Λ) (v q:ℝ≥0) (hvq:v≤q)
    (target:Fin n→ℝ) (a:Fin n→UnitAddCircle)
    (hgap:∀i,(q:ℝ)-(v:ℝ)<target i) (ht1:∀i,target i≤1)
    (lo hi:Fin r→ℝ) (hlo:∀j,(q:ℝ)-(v:ℝ)≤lo j) (hlohi:∀j,lo j<hi j)
    (hstop:∀j i,target i≤lo j ∨ hi j≤target i)
    (hdisjoint:∀j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (leaf:Fin m→Fin n) (ht:∀j,target (leaf j)∈Set.Ioc 0 P.horizon)
    (D:Fin r→State n) (E:State n) (z:Ω×UnitAddCircle)
    (hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance target target (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2))
        (referenceProfile P Λ
          (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v z.1)
          (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v z.1)) lo hi j)).range)
    (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P target target
      (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2)) ((q:ℝ)-(v:ℝ)))).range)
    (g:Fin d→Fin n) (F:State d→ℝ) (hFm:Measurable F) {A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν)
    (hf:ContDiff ℝ r F) (hfb:∀j,j≤r→∀w,‖iteratedFDeriv ℝ j F w‖≤A0*ν^j)
    (p:ℕ) (hp:0<p) (K:ℝ) (hK:0≤K)
    (hgeom:|(∏j,scoreVariance (familyCovariance target target
      (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2))
      (referenceProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v z.1)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v z.1)) lo hi j) (D j))*
      Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P target target
        (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2)) ((q:ℝ)-(v:ℝ))) E)|≤K) (χ:ℝ) (hχ:0≤χ) (hχ1:χ≤1):
    let U:=MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v z.1
    let Dir:=MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v z.1
    let center:=StoppedGaussianScore.nativeCenter (fun i=>a i+z.2)
    let mean:=fun θ=>MixedPastNativePacketEnergy.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      v q target target a (θ,z)
    let V:=PhysicalMeanRange.dampedDirection target target (fun i=>a i+z.2) ((q:ℝ)-(v:ℝ)) Λ
      (embed (S.second q z.1-S.first q z.1))
    let MP:=fun θ=>TwoFreshCompleteWord.value P Λ U Dir θ ((q:ℝ)-(v:ℝ)) target target center lo hi
      (mean θ) false D E V g leaf F
    let T:=MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν
    let G:=MixedPastNativePacketUniform.packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      (r:=r) P v q target target a leaf p z
    let Dcur:=MixedNativeDampedScoreAmplitude.amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P v q target a lo hi z
    let WP:=fun θ=>NativeFirstWholeComplete.value P Λ U Dir θ ((q:ℝ)-(v:ℝ)) target target center lo hi
      (mean θ) D E g leaf F
    Integrable MP MixedNativeDampedScoreAmplitude.thetaMeasure ∧
      |WP 1-WP 0|≤2*(K*T)*(Dcur^χ*G)+
        |WP 1-WP 0-(∫θ,MP θ ∂MixedNativeDampedScoreAmplitude.thetaMeasure)| :=by
  intro U Dir center mean V MP T G Dcur WP
  have hh:=cap 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P hΛ v q hvq target a hgap ht1 lo hi hlo hlohi hstop hdisjoint leaf ht
    D E z hD hE g F hFm hA0 hν hf hfb p hp K hK hgeom
  change Integrable MP MixedNativeDampedScoreAmplitude.thetaMeasure ∧
    |∫θ,MP θ ∂MixedNativeDampedScoreAmplitude.thetaMeasure|≤(K*T)*Dcur*G ∧
    |WP 1-WP 0|≤2*(K*T)*G at hh
  have hGn:0≤G:=Real.rpow_nonneg (MixedPastNativePacketUniform.envelope_nonneg
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P v q target target a leaf (fun j=>(ht j).1) p z) _
  have hT:0≤T:=MixedPastWordMoments.total_nonneg P lo hi _ A0 ν
  have hDcur:0≤Dcur:=Real.sqrt_nonneg _
  have hlinear:|WP 1-WP 0|≤(K*T)*Dcur*G+
      |WP 1-WP 0-(∫θ,MP θ ∂MixedNativeDampedScoreAmplitude.thetaMeasure)|:=by
    calc
      _=|(∫θ,MP θ ∂MixedNativeDampedScoreAmplitude.thetaMeasure)+
          (WP 1-WP 0-(∫θ,MP θ ∂MixedNativeDampedScoreAmplitude.thetaMeasure))|:=by congr 1;ring
      _≤_:=abs_add_le _ _
      _≤_:=add_le_add hh.2.1 le_rfl
  exact ⟨hh.1,NativeCurrentCapInterpolation.packet_clip (mul_nonneg hK hT) hDcur hGn
    (abs_nonneg _) hχ hχ1 hlinear hh.2.2⟩

end SHE.MixedPastNativeMeanCap
