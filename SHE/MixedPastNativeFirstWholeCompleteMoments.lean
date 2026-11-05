module

public import SHE.MixedPastNativeFirstWholeCompleteWeights
public import SHE.NativeFirstWholeComplete
public import SHE.NativeFirstWholeFields
public import SHE.NativeFirstWholePointwise
public import SHE.NativeFirstWholeFibre
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

namespace SHE.MixedPastNativeFirstWholeCompleteMoments
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeFirstWholeCompleteMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeFirstWholeCompleteMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeFirstWholeCompleteMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeFirstWholeCompleteMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeFirstWholeCompleteMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeFirstWholeCompleteMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

variable (θ : ℝ)

local instance mixedPastNativeFirstWholeCompleteMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeFirstWholeCompleteMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  TwoFreshFullResidualMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

include hIJ₀ hIJ₁ in
/-- Actual conditional consistent native-first complete-word moments. The Gaussian
laws depend on the genuine random past states; pointwise Gaussian
estimation precedes conditional BDG and arbitrary past-weight averaging. -/
theorem weighted_even_moment (P:CanonicalCovariance.ProfileParameters)
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ) (hθ:|θ|≤1)
    (v q:ℝ≥0) (hvq:v≤q) (hqH:q≤H) (hspan:(q:ℝ)-(v:ℝ)≤1)
    (σ target:Fin n→ℝ) (center:Fin n→HeatCircle)
    (hσ:∀i,0<σ i) (hσ1:∀i,σ i≤1) (hages:∀i,σ i≤target i)
    (lo hi:Fin r→ℝ) (hlo:∀j,(q:ℝ)-(v:ℝ)≤lo j) (hlohi:∀j,lo j<hi j)
    (hstop:∀j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint:∀j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (D:Fin r→State n) (E:State n)
    (g:Fin d→Fin n) (leaf:Fin m→Fin n)
    (hnative:∀j,σ (leaf j)=target (leaf j)) (ht:∀j,target (leaf j)∈Set.Ioc 0 P.horizon)
    (hgap:∀j,(q:ℝ)-(v:ℝ)<target (leaf j))
    (F:State d→ℝ) (hFm:Measurable F) {A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν)
    (hf:ContDiff ℝ r F)
    (hfb:∀j,j≤r→∀z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b:ℕ) (hb:0<b) (B0:ℝ≥0) (hBDG:StandardTerminalBDGPower (b*(m+2)) J B0)
    (weight:Ω→ℝ) (hw:Measurable[𝓕 v] weight) (hw0:∀ω,0≤weight ω) (hwi:Integrable weight μ)
    (K:ℝ) (hK:0≤K)
    (hD:∀ω j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)) lo hi j)).range)
    (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ)))).range)
    (hgeom:∀ᵐω∂μ,
      let U:=MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω
      let dir:=MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω
      let A:=familyCovariance σ target center (referenceProfile P Λ U dir) lo hi
      let R:=NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ))
      |(∏j,scoreVariance (A j) (D j))*Real.sqrt (scoreVariance R E)|≤K):
    let U:=MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let dir:=MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let mean:=MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
    let G:=fun ω=>NativeFirstWholeComplete.value P Λ (U ω) (dir ω) θ ((q:ℝ)-(v:ℝ))
      σ target center lo hi (mean ω) D E g leaf F
    Integrable (fun ω=>weight ω*|G ω|^(2*b)) μ ∧
      (∫ω,weight ω*|G ω|^(2*b) ∂μ)≤NativeFirstWholeComplete.momentConstant P r m b
        ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*(K*MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν)^(2*b)*
          (∫ω,weight ω ∂μ):=by
  intro U dir mean G
  let T:=MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν
  have hKT:0≤K*T:=mul_nonneg hK (MixedPastWordMoments.total_nonneg P lo hi _ A0 ν)
  let budget:=fun ω=>NativeFirstWholeMoments.currentBudget P Λ (U ω) (dir ω) θ target center leaf (mean ω) b
  have hbudget0(ω):0≤budget ω:=NormalizedLeafOffsets.budget_nonneg _ _ _ _ (fun j=>(ht j).1)
  have hconst:=MixedPastNativeFirstWholeCompleteWeights.constant_with_past_weight (r:=r)
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ P hlocal hΛ hθ
    v q hvq hqH hspan σ target center leaf hnative (fun j=>(ht j).1) hgap b hb B0 hBDG weight hw hw0 hwi
  have hU:Measurable U:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hdir:Measurable dir:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hm:=MixedPastJointData.mean_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
  have hG:Measurable G:=by
    let cs:=assignments (m:=m+1) (List.finRange r)
    have heq:G=(fun ω=>(1/2:ℝ)^r*∑ i:Fin cs.length,
        NativeFirstWholeMoments.fibreAverage P Λ (U ω) (dir ω)
          θ ((q:ℝ)-(v:ℝ)) σ target center lo hi (mean ω) D E g leaf (cs.get i) F):=
      funext (fun _=>congrArg (fun a:ℝ=>(1/2:ℝ)^r*a) (FiniteAssignmentMoments.map_sum_eq_fin cs _))
    rw [heq]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    exact NativeFirstWholeFields.fibreAverage_measurable P Λ θ ((q:ℝ)-(v:ℝ))
      U dir hU hdir σ target center lo hi mean hm (fun _=>D) (fun _=>measurable_const)
      (fun _=>E) measurable_const g leaf (cs.get i) F hFm
  have hbound:∀ᵐω∂μ,weight ω*|G ω|^(2*b)≤
      (weight ω*NativeFirstWholeComplete.momentConstant P r m b (budget ω))*(K*T)^(2*b):=by
    filter_upwards [hgeom] with ω hω
    have hbnd:=NativeFirstWholeComplete.bound P Λ (U ω) (dir ω) θ ((q:ℝ)-(v:ℝ))
      (sub_nonneg.mpr (by exact_mod_cast hvq)) σ target center hσ hσ1 hages lo hi hlo hlohi hstop hdisjoint
      (mean ω) D (hD ω) E hE g leaf hnative ht
      F hFm hA0 hν hf hfb b hb K hK hω
    calc
      _≤weight ω*(NativeFirstWholeComplete.momentConstant P r m b (budget ω)*(K*T)^(2*b)):=
        mul_le_mul_of_nonneg_left hbnd (hw0 ω)
      _=_:=by ring
  have hgi:Integrable (fun ω=>weight ω*|G ω|^(2*b)) μ:=
    (hconst.1.mul_const ((K*T)^(2*b))).mono'
      (((hw.mono (𝓕.le v) le_rfl).mul ((continuous_abs.measurable.comp hG).pow_const _)).aestronglyMeasurable)
      (by filter_upwards [hbound] with ω hω
          rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hw0 ω) (pow_nonneg (abs_nonneg _) _))]
          exact hω)
  refine ⟨hgi,?_⟩
  have hfinal:(∫ω,weight ω*|G ω|^(2*b) ∂μ)≤
      (NativeFirstWholeComplete.momentConstant P r m b
        ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*
          (∫ω,weight ω ∂μ))*(K*T)^(2*b):=by
    apply (integral_mono_ae hgi (hconst.1.mul_const ((K*T)^(2*b))) hbound).trans
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right hconst.2 (pow_nonneg hKT _)
  convert! hfinal using 1 <;> ring

end SHE.MixedPastNativeFirstWholeCompleteMoments

