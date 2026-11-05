module

public import SHE.FullHorizonEndpointVersion
public import SHE.SingularInputBounds
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
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

namespace SHE.FirstGammaEndpointRows
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaEndpointRows_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaEndpointRows_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaEndpointRows_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaEndpointRows_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaEndpointRows_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaEndpointRows_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaEndpointRows_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaEndpointRows_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v b : ℝ≥0) (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hbH : b≤H)


open SingularInputBounds
variable (θ : ℝ)
local notation "m0" => hell.le.trans ((hbU 0).1.trans (hbU 0).2)
local notation "Past" => MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "hPast" => MixedNativeFrozenPrefixIto.data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "C" => (1+StoppedFourier.heatConstant)

def additive (i : Fin n) : Process (E:=RealHaarInput) 𝓕 μ H:=
  FullHorizonEndpoint.process 𝓕 μ H b hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const (htarget i) (Z i).center hbH
def first (i : Fin n) : Process (E:=RealHaarInput) 𝓕 μ H:=
  FullHorizonEndpoint.process 𝓕 μ H b hell m0
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient (htarget i) (Z i).center hbH
def second (i : Fin n) : Process (E:=RealHaarInput) 𝓕 μ H:=
  FullHorizonEndpoint.process 𝓕 μ H b hell m0
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient (htarget i) (Z i).center hbH
def frozen (i : Fin n) : Process (E:=RealHaarInput) 𝓕 μ H:=
  FullHorizonEndpoint.process 𝓕 μ H b (sub_pos.mpr hκP) (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP)
    (FrozenReferenceFields.field P Λ κ θ hκP v Past)
    (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v Past hPast) (htarget i) (Z i).center hbH

local notation "r0" => additive 𝓕 μ H κ hκ Z b htarget hbH
local notation "rU" => first 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b htarget hbH
local notation "rV" => second 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b htarget hbH
local notation "rF" => frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ

def actual : Fin (n+n)→Process (E:=Both RealHaarInput) 𝓕 μ H:=
  Fin.append (fun i=>TwoChannelItoRows.block 𝓕 μ H (r0 i) (rU i))
    (fun i=>InterpolatedPredictableRows.rescaledDifference 𝓕 μ H hΛ b (rU i) (rV i))
def replacement : Fin (n+n)→Process (E:=Both RealHaarInput) 𝓕 μ H:=
  Fin.append (fun i=>TwoChannelItoRows.block 𝓕 μ H (r0 i) (rF i)) (fun _=>0)

def cap : Fin (n+n)→ℝ:=Fin.append (fun _=>(κ+M)*C) (fun _=>Real.exp (Λ*(b:ℝ))^2*(4*(M*C)))
def replacementCap : Fin (n+n)→ℝ:=Fin.append (fun _=>P.upper*C) (fun _=>0)

include hκ hell hbU in
theorem cap_nonneg (i : Fin (n+n)) : 0≤cap (M:=M) Λ κ b i:=by
  have hM:=m0
  have hC : 0≤C:=add_nonneg zero_le_one StoppedFourier.heatConstant_pos.le
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [cap,Fin.append_left]
    exact mul_nonneg (add_nonneg hκ.le hM) hC
  · simp only [cap,Fin.append_right]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (mul_nonneg hM hC))
theorem replacementCap_nonneg (i : Fin (n+n)) : 0≤replacementCap P i:=by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [replacementCap,Fin.append_left]
    exact mul_nonneg P.upper_nonneg (add_nonneg zero_le_one StoppedFourier.heatConstant_pos.le)
  · simp only [replacementCap,Fin.append_right,le_refl]

theorem actual_bound (hb1 : (b:ℝ)≤1) (i : Fin (n+n)) :
    Bound 𝓕 μ H b (cap (M:=M) Λ κ b i)
      (actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b htarget hbH i) := by
  have h0 (j:Fin n) : Bound 𝓕 μ H b (κ*C) (r0 j):=FullHorizonEndpointVersion.singular_bound 𝓕 μ H b hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const (htarget j) (Z j).center hbH hb1
  have hU (j:Fin n) : Bound 𝓕 μ H b (M*C) (rU j):=FullHorizonEndpointVersion.singular_bound 𝓕 μ H b hell m0
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient (htarget j) (Z j).center hbH hb1
  have hV (j:Fin n) : Bound 𝓕 μ H b (M*C) (rV j):=FullHorizonEndpointVersion.singular_bound 𝓕 μ H b hell m0
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient (htarget j) (Z j).center hbH hb1
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · have hh:=block_bound 𝓕 μ H b (h0 j) (hU j)
    have he : κ*C+M*C=(κ+M)*C:=by ring
    rw [he] at hh
    simpa only [actual,cap,Fin.append_left] using hh
  · have hd:=sub_bound 𝓕 μ H b (hV j) (hU j)
    have he : 2*(M*C+M*C)=4*(M*C):=by ring
    rw [he] at hd
    have hw:=weighted_bound 𝓕 μ H b (K:=4*(M*C)) (u:=rV j-rU j) hd (PredictableDamping.weight Λ b)
      (PredictableDamping.weight_predictable 𝓕 Λ b) (PredictableDamping.weight_bound hΛ b)
    have hs:=smul_bound 𝓕 μ H b hw (Real.exp (Λ*(b:ℝ)))
    have hr:=right_bound 𝓕 μ H b hs
    simpa only [actual,cap,Fin.append_right,InterpolatedPredictableRows.rescaledDifference] using hr

theorem replacement_bound (hb1 : (b:ℝ)≤1) (i : Fin (n+n)) :
    Bound 𝓕 μ H b (replacementCap P i)
      (replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ i) := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · have h0:=FullHorizonEndpointVersion.singular_bound 𝓕 μ H b hκ hκ.le
      (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const (htarget j) (Z j).center hbH hb1
    have hf:=FullHorizonEndpointVersion.singular_bound 𝓕 μ H b (sub_pos.mpr hκP)
      (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP)
      (FrozenReferenceFields.field P Λ κ θ hκP v Past)
      (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v Past hPast) (htarget j) (Z j).center hbH hb1
    have hh:=block_bound 𝓕 μ H b h0 hf
    have he : κ*C+(P.upper-κ)*C=P.upper*C:=by ring
    rw [he] at hh
    simpa only [replacement,replacementCap,Fin.append_left,additive,frozen] using hh
  · filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_zero (Both RealHaarInput) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)))] with p hp hb
    simp only [replacement,Fin.append_right,hp,Pi.zero_apply,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),
      replacementCap,Fin.append_right,zero_mul,le_refl]

end SHE.FirstGammaEndpointRows
