module

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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativePacketBounds
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativePacketBounds_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativePacketBounds_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativePacketBounds_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativePacketBounds_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativePacketBounds_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativePacketBounds_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedPastNativePacketBounds_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastNativePacketBounds_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativePacketBounds_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  NativeFirstWholeMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

/-- The consistent endpoint and the COMPLETE mean-score leg share the
same actual packet. All current/reference dependence is retained before
the outer native average. -/
theorem whole_and_mean (P:CanonicalCovariance.ProfileParameters) (v q:ℝ≥0) (hvq:v≤q)
    (θ:ℝ) (hθ:θ∈Set.Icc (0:ℝ) 1) (σ target:Fin n→ℝ) (a:Fin n→UnitAddCircle)
    (hσ:∀i,0<σ i) (hσ1:∀i,σ i≤1) (hages:∀i,σ i≤target i)
    (lo hi:Fin r→ℝ) (hlo:∀j,(q:ℝ)-(v:ℝ)≤lo j) (hlohi:∀j,lo j<hi j)
    (hstop:∀j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint:∀j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (leaf:Fin m→Fin n) (hnative:∀j,σ (leaf j)=target (leaf j))
    (ht:∀j,target (leaf j)∈Set.Ioc 0 P.horizon)
    (D:Fin r→State n) (E V:State n) (z:Ω×UnitAddCircle)
    (hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2))
        (referenceProfile P Λ
          (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1)
          (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1)) lo hi j)).range)
    (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P σ target
      (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2)) ((q:ℝ)-(v:ℝ)))).range)
    (hV:V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (ControlledFixedReserve.covariance P Λ
      (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1)
      (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1)
      (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1) lo hi))
      σ target (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2)) ((q:ℝ)-(v:ℝ)) θ)).range)
    (g:Fin d→Fin n) (F:State d→ℝ) (hFm:Measurable F) {A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν)
    (hf:ContDiff ℝ r F) (hfb:∀j,j≤r→∀w,‖iteratedFDeriv ℝ j F w‖≤A0*ν^j)
    (p:ℕ) (hp:0<p) (K:ℝ) (hK:0≤K)
    (hgeom:|(∏j,scoreVariance (familyCovariance σ target
      (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2))
      (referenceProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1)) lo hi j) (D j))*
      Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target
        (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2)) ((q:ℝ)-(v:ℝ))) E)|≤K):
    let U:=MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1
    let Dir:=MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1
    let center:=StoppedGaussianScore.nativeCenter (fun i=>a i+z.2)
    let mean:=MixedPastNativePacketEnergy.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      v q σ target a (θ,z)
    let C:=ControlledFixedReserve.covariance P Λ U Dir
      (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ U Dir lo hi)) σ target center ((q:ℝ)-(v:ℝ)) θ
    let T:=MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν
    let G:=MixedPastNativePacketUniform.packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (r:=r) P v q σ target a leaf p z
    |NativeFirstWholeComplete.value P Λ U Dir θ ((q:ℝ)-(v:ℝ)) σ target center lo hi mean D E g leaf F|≤G*(K*T) ∧
      |TwoFreshCompleteWord.value P Λ U Dir θ ((q:ℝ)-(v:ℝ)) σ target center lo hi mean false D E V g leaf F|≤
        G*(K*T*Real.sqrt (scoreVariance C V)) := by
  intro U Dir center mean C T G
  have hq:0≤(q:ℝ)-(v:ℝ):=sub_nonneg.mpr (by exact_mod_cast hvq)
  let B:=MixedPastNativePacketUniform.envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (r:=r) P v q σ target a leaf p z
  have hB:0≤B:=MixedPastNativePacketUniform.envelope_nonneg
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v q σ target a leaf (fun j=>(ht j).1) p z
  have hb:=MixedPastNativePacketUniform.constants_le_envelope
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (r:=r) P v q σ target a leaf
    (fun j=>(ht j).1) p θ hθ z
  have hT:0≤T:=MixedPastWordMoments.total_nonneg P lo hi _ A0 ν
  have hKT:0≤K*T:=mul_nonneg hK hT
  have hw:=NativeFirstWholeComplete.bound P Λ U Dir θ ((q:ℝ)-(v:ℝ)) hq σ target center hσ hσ1 hages
    lo hi hlo hlohi hstop hdisjoint mean D hD E hE g leaf hnative ht F hFm hA0 hν hf hfb p hp K hK hgeom
  have hw':|NativeFirstWholeComplete.value P Λ U Dir θ ((q:ℝ)-(v:ℝ)) σ target center lo hi mean D E g leaf F|^(2*p)≤
      B*(K*T)^(2*p):=hw.trans (mul_le_mul_of_nonneg_right hb.1 (pow_nonneg hKT _))
  have hgeomV:|(∏j,scoreVariance (familyCovariance σ target center (referenceProfile P Λ U Dir) lo hi j) (D j))*
      Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ))) E)*
      GaussianDependentScores.scale false C V|≤K*Real.sqrt (scoreVariance C V):=by
    change |_*Real.sqrt (scoreVariance C V)|≤_
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right hgeom (Real.sqrt_nonneg _)
  have hm:=TwoFreshCompleteWord.bound P Λ U Dir θ ((q:ℝ)-(v:ℝ)) hq σ target center hσ hσ1 hages
    lo hi hlo hlohi hstop hdisjoint mean false D hD E V hE hV g leaf hnative ht
    F hFm hA0 hν hf hfb p hp (K*Real.sqrt (scoreVariance C V)) (by positivity) hgeomV
  have hm':|TwoFreshCompleteWord.value P Λ U Dir θ ((q:ℝ)-(v:ℝ)) σ target center lo hi mean false D E V g leaf F|^(2*p)≤
      B*(K*T*Real.sqrt (scoreVariance C V))^(2*p):=by
    have hh:=hm.trans (mul_le_mul_of_nonneg_right hb.2
      (pow_nonneg (mul_nonneg (mul_nonneg hK (Real.sqrt_nonneg _)) hT) _))
    convert! hh using 1 <;> ring
  exact ⟨NativeCurrentCapInterpolation.root_cap hB hKT p hp hw',
    NativeCurrentCapInterpolation.root_cap hB (by positivity) p hp hm'⟩

end SHE.MixedPastNativePacketBounds

